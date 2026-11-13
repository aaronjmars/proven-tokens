import UsdtVerify.Evm.Storage
import UsdtVerify.Evm.Write
import UsdtVerify.Evm.Calldata

/-!
# The sum of the balances of a token against its total supply

For a token that keeps `balances[a]` in slot `mapSlot a b` and its total supply in slot `t`:

- `sumBal b C S`: the sum, as an integer, of the balance words of the 2^160 addresses in the
  state `S` of the contract `C`.
- `D b t C S`: that sum minus the word of slot `t`; `Inv b t C S`: `D = 0`.
- `NotBal b n`: the slot `n` is the balance slot of no address word. `UniqBal b x`: no other
  address word has the balance slot of `x`. Both are facts about keccak, used as hypotheses.
- `D_read`, `D_write_bal`, `D_write_tot`, `D_write_other`: how one SLOAD or SSTORE changes `D`.
- `sub_fact`, `add_fact`: the checks of SafeMath, as compiled (three ISZERO over GT or LT),
  give the subtraction and the addition as integers.

The base slot `b` and the slot `t` are parameters: nothing here is about one token. The sums
(`sumTo` and its lemmas) follow UsdtVerify/Usdt/Invariant/Supply.lean, where the slots are fixed.
-/

namespace TokenKit.Supply

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The sum of `f 0 .. f (n - 1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_congr {f g : Nat → Int} : ∀ n, (∀ i, i < n → f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [sumTo, sumTo, sumTo_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_update {f g : Nat → Int} {a : Nat} :
    ∀ n, a < n → (∀ i, i < n → i ≠ a → g i = f i) → sumTo g n = sumTo f n - f a + g a
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, hfg => by
    rw [sumTo, sumTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
    · rw [sumTo_update n h' (fun i hi hia => hfg i (by omega) hia), hfg n (by omega) (by omega)]
      omega
    · subst h'
      rw [sumTo_congr a (fun i hi => hfg i (by omega) (by omega))]; omega

/-- The slot `n` is the balance slot of no address word. -/
def NotBal (b n : U256) : Prop := ∀ x : U256, x.toNat < 2 ^ 160 → n ≠ mapSlot x b

/-- No address word other than `x` has the balance slot of `x`. -/
def UniqBal (b x : U256) : Prop :=
  ∀ y : U256, y.toNat < 2 ^ 160 → mapSlot y b = mapSlot x b → y = x

/-- `balances[i]` (as an integer) for the address number `i`. -/
abbrev bal (b : U256) (C : Address) (S : State.TransactionState) (i : Nat) : Int :=
  ((storageAt S C (mapSlot (BitVec.ofNat 256 i) b)).toNat : Int)

/-- The sum of the balances of the 2^160 addresses. -/
def sumBal (b : U256) (C : Address) (S : State.TransactionState) : Int :=
  sumTo (bal b C S) (2 ^ 160)

/-- The sum of the balances minus the total supply. -/
def D (b t : U256) (C : Address) (S : State.TransactionState) : Int :=
  sumBal b C S - ((storageAt S C t).toNat : Int)

/-- The invariant: the sum of all balances is the total supply. -/
def Inv (b t : U256) (C : Address) (S : State.TransactionState) : Prop := D b t C S = 0

theorem ofNat_toNat (x : U256) : BitVec.ofNat 256 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

variable {b t : U256} {C : Address} {S : State.TransactionState}

theorem sumBal_read (c : Address) (n : U256) : sumBal b C (readSlot S c n) = sumBal b C S := by
  unfold sumBal
  exact sumTo_congr _ (fun i _ => by simp only [bal, storageAt_readSlot])

theorem sumBal_write_nb (hacc : hasAccount S C) {n : U256} (hn : NotBal b n) (v : U256) :
    sumBal b C (writeSlot S C n v) = sumBal b C S := by
  unfold sumBal
  refine sumTo_congr _ (fun i hi => ?_)
  have hi' : (BitVec.ofNat 256 i : U256).toNat < 2 ^ 160 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  simp only [bal, storageAt_writeSlot_of_ne hacc (fun e => hn _ hi' e.symm)]

theorem sumBal_write_bal (hacc : hasAccount S C) {x : U256} (hu : UniqBal b x)
    (hx : x.toNat < 2 ^ 160) (v : U256) :
    sumBal b C (writeSlot S C (mapSlot x b) v) =
      sumBal b C S - (storageAt S C (mapSlot x b)).toNat + v.toNat := by
  unfold sumBal
  have h := sumTo_update (f := bal b C S) (g := bal b C (writeSlot S C (mapSlot x b) v))
    (a := x.toNat) (2 ^ 160) hx (fun i hi2 hi => ?_)
  · rw [h]
    simp only [bal, ofNat_toNat, storageAt_writeSlot_self hacc]
  · have hne : mapSlot (BitVec.ofNat 256 i) b ≠ mapSlot x b := by
      intro e
      apply hi
      have := hu _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi2) e
      rw [← this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [bal, storageAt_writeSlot_of_ne hacc hne]

/-- An SLOAD changes neither the balances nor the total supply. -/
theorem D_read (c : Address) (n : U256) : D b t C (readSlot S c n) = D b t C S := by
  unfold D
  rw [sumBal_read, storageAt_readSlot]

/-- A write of the balance of `x`: the sum moves by the new word minus the old one. -/
theorem D_write_bal (hacc : hasAccount S C) {x : U256} (hu : UniqBal b x)
    (hx : x.toNat < 2 ^ 160) (ht : NotBal b t) (v : U256) :
    D b t C (writeSlot S C (mapSlot x b) v) =
      D b t C S - (storageAt S C (mapSlot x b)).toNat + v.toNat := by
  unfold D
  rw [sumBal_write_bal hacc hu hx, storageAt_writeSlot_of_ne hacc (ht x hx)]
  omega

/-- A write of the total supply. -/
theorem D_write_tot (hacc : hasAccount S C) (ht : NotBal b t) (v : U256) :
    D b t C (writeSlot S C t v) = D b t C S + (storageAt S C t).toNat - v.toNat := by
  unfold D
  rw [sumBal_write_nb hacc ht, storageAt_writeSlot_self hacc]
  omega

/-- A write of a slot that is no balance slot and not the total supply. -/
theorem D_write_other (hacc : hasAccount S C) {n : U256} (hn : NotBal b n) (hne : n ≠ t)
    (v : U256) : D b t C (writeSlot S C n v) = D b t C S := by
  unfold D
  rw [sumBal_write_nb hacc hn, storageAt_writeSlot_of_ne hacc (Ne.symm hne)]

/-! ## The checks of SafeMath -/

/-- `require(v <= a)` as compiled: `ISZERO ISZERO ISZERO (GT v a)` is not 0. -/
theorem le_of_cond_gt {v a : U256} (h : isZero (isZero (isZero (greaterThan v a))) ≠ 0) :
    v.toNat ≤ a.toNat := by
  by_cases hgt : v.toNat > a.toNat
  · exfalso
    apply h
    have e : greaterThan v a = 1 := if_pos hgt
    rw [e]
    decide
  · omega

/-- `require(c >= a)` as compiled: `ISZERO ISZERO ISZERO (LT c a)` is not 0. -/
theorem le_of_cond_lt {c a : U256} (h : isZero (isZero (isZero (lessThan c a))) ≠ 0) :
    a.toNat ≤ c.toNat := by
  by_cases hlt : c.toNat < a.toNat
  · exfalso
    apply h
    have e : lessThan c a = 1 := if_pos hlt
    rw [e]
    decide
  · omega

/-- After the check of `sub`, the difference does not wrap. -/
theorem sub_fact {v a : U256} (h : isZero (isZero (isZero (greaterThan v a))) ≠ 0) :
    ((sub a v).toNat : Int) = a.toNat - v.toNat := by
  have hle := le_of_cond_gt h
  have ha := a.isLt
  have hv := v.isLt
  have e : (sub a v).toNat = a.toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  omega

/-- After the check of `add`, the sum does not wrap. -/
theorem add_fact {a v : U256} (h : isZero (isZero (isZero (lessThan (add a v) a))) ≠ 0) :
    ((add a v).toNat : Int) = a.toNat + v.toNat := by
  have hle := le_of_cond_lt h
  have ha := a.isLt
  have hv := v.isLt
  have e : (add a v).toNat = a.toNat + v.toNat := by
    simp only [add, BitVec.toNat_add] at hle ⊢
    omega
  omega

end TokenKit.Supply

/-- Closes the side goals of the `D_write_*` rewrites: a hypothesis of the context, or that the
contract still has its account after some reads and writes of slots. -/
macro "supply_side" : tactic =>
  `(tactic| first
    | assumption
    | (repeat' (first
        | assumption
        | apply UsdtVerify.hasAccount_writeSlot
        | apply UsdtVerify.hasAccount_readSlot)))

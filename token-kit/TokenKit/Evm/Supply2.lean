import TokenKit.Evm.Supply
import TokenKit.Evm.Safe

/-!
# The supply invariant over two mappings

A token that locks balances keeps two mappings of amounts, say `balanceOf` and `freezeOf`, and
moves an amount from one to the other without changing the total supply. Its invariant is: the
sum of the words of the first mapping plus the sum of the words of the second equals the total
supply.

- `D2 b1 b2 t C S`: the sum over the 2^160 addresses of the mapping at base `b1`, plus the same
  sum at base `b2`, minus the word of slot `t`, as an integer.
- `Inv2`: `D2 = 0`.
- `D2_read`, `D2_write_bal1`, `D2_write_bal2`, `D2_write_tot`, `D2_write_other`: how one SLOAD
  or SSTORE changes `D2`, with the facts about slots as hypotheses (`NotBal`, `UniqBal` of
  Evm/Supply.lean).
- `inv2_of_ro`: a run that only reads (`Ro` of Evm/Safe.lean) keeps `Inv2`.
- `sub_fact_lt1`, `add_fact_lt`, `add_fact2`: the checked subtraction and addition of old
  Solidity code (`require(a >= v)`, `require(b + v >= b)`, and the first check of SafeMath add
  before its ISZERO), as facts about natural numbers.

Nothing here is about one token.
-/

namespace TokenKit.Supply

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The two sums minus the total supply. -/
def D2 (b1 b2 t : U256) (C : Address) (S : State.TransactionState) : Int :=
  sumBal b1 C S + sumBal b2 C S - ((storageAt S C t).toNat : Int)

/-- The invariant: the two sums add up to the total supply. -/
def Inv2 (b1 b2 t : U256) (C : Address) (S : State.TransactionState) : Prop :=
  D2 b1 b2 t C S = 0

variable {b1 b2 t : U256} {C : Address} {S : State.TransactionState}

theorem D2_read (c : Address) (n : U256) : D2 b1 b2 t C (readSlot S c n) = D2 b1 b2 t C S := by
  unfold D2
  rw [sumBal_read, sumBal_read, storageAt_readSlot]

theorem D2_write_bal1 (hacc : hasAccount S C) {x : U256} (hu : UniqBal b1 x)
    (hx : x.toNat < 2 ^ 160) (h2 : NotBal b2 (mapSlot x b1)) (ht : NotBal b1 t) (v : U256) :
    D2 b1 b2 t C (writeSlot S C (mapSlot x b1) v) =
      D2 b1 b2 t C S - (storageAt S C (mapSlot x b1)).toNat + v.toNat := by
  unfold D2
  rw [sumBal_write_bal hacc hu hx, sumBal_write_nb hacc h2,
    storageAt_writeSlot_of_ne hacc (ht x hx)]
  omega

theorem D2_write_bal2 (hacc : hasAccount S C) {x : U256} (hu : UniqBal b2 x)
    (hx : x.toNat < 2 ^ 160) (h1 : NotBal b1 (mapSlot x b2)) (ht : NotBal b2 t) (v : U256) :
    D2 b1 b2 t C (writeSlot S C (mapSlot x b2) v) =
      D2 b1 b2 t C S - (storageAt S C (mapSlot x b2)).toNat + v.toNat := by
  unfold D2
  rw [sumBal_write_bal hacc hu hx, sumBal_write_nb hacc h1,
    storageAt_writeSlot_of_ne hacc (ht x hx)]
  omega

theorem D2_write_tot (hacc : hasAccount S C) (ht1 : NotBal b1 t) (ht2 : NotBal b2 t) (v : U256) :
    D2 b1 b2 t C (writeSlot S C t v) = D2 b1 b2 t C S + (storageAt S C t).toNat - v.toNat := by
  unfold D2
  rw [sumBal_write_nb hacc ht1, sumBal_write_nb hacc ht2, storageAt_writeSlot_self hacc]
  omega

theorem D2_write_other (hacc : hasAccount S C) {n : U256} (hn1 : NotBal b1 n)
    (hn2 : NotBal b2 n) (hne : n ≠ t) (v : U256) :
    D2 b1 b2 t C (writeSlot S C n v) = D2 b1 b2 t C S := by
  unfold D2
  rw [sumBal_write_nb hacc hn1, sumBal_write_nb hacc hn2,
    storageAt_writeSlot_of_ne hacc (Ne.symm hne)]

/-- `require(a >= v)` as compiled: `ISZERO (LT a v)` is not 0. -/
theorem le_of_cond_lt1 {a v : U256} (h : isZero (lessThan a v) ≠ 0) : v.toNat ≤ a.toNat := by
  by_cases hlt : a.toNat < v.toNat
  · exfalso
    apply h
    have e : lessThan a v = 1 := if_pos hlt
    rw [e]
    decide
  · omega

/-- After `require(a >= v)`, the difference does not wrap. -/
theorem sub_fact_lt1 {a v : U256} (h : isZero (lessThan a v) ≠ 0) :
    ((sub a v).toNat : Int) = a.toNat - v.toNat := by
  have hle := le_of_cond_lt1 h
  have ha := a.isLt
  have hv := v.isLt
  have e : (sub a v).toNat = a.toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  rw [e]
  omega

/-- After `require(b + v >= b)`, the sum does not wrap. -/
theorem add_fact_lt {b v : U256} (h : isZero (lessThan (add b v) b) ≠ 0) :
    ((add b v).toNat : Int) = b.toNat + v.toNat := by
  have hle := le_of_cond_lt1 h
  have hb := b.isLt
  have hv := v.isLt
  simp only [add, BitVec.toNat_add] at hle ⊢
  omega

/-- The first check of SafeMath add, before its ISZERO: `ISZERO (ISZERO (LT (a + v) a))` is 0. -/
theorem add_fact2 {a v : U256} (h : isZero (isZero (lessThan (add a v) a)) = 0) :
    ((add a v).toNat : Int) = a.toNat + v.toNat := by
  refine add_fact_lt ?_
  intro h0
  rw [h0] at h
  exact absurd h (by decide)

/-- The no overflow of the first check of SafeMath add, as a bound. -/
theorem add_bound2 {a v : U256} (h : isZero (isZero (lessThan (add a v) a)) = 0) :
    a.toNat + v.toNat < 2 ^ 256 := by
  have f := add_fact2 h
  have := (add a v).isLt
  omega

/-- `Ro` keeps the invariant over two mappings. -/
theorem inv2_of_ro {b1 b2 t : U256} {C : Address} {S S' : State.TransactionState}
    {ss ss' : Substate} (h : Ro C S ss S' ss') (hinv : Inv2 b1 b2 t C S) :
    Inv2 b1 b2 t C S' := by
  have e (b : U256) : sumBal b C S' = sumBal b C S :=
    sumTo_congr (f := bal b C S') (g := bal b C S) _ (fun i _ => by
      show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
      rw [h.storage])
  unfold Inv2 D2 at hinv ⊢
  rw [e b1, e b2, h.storage C t]
  exact hinv

end TokenKit.Supply

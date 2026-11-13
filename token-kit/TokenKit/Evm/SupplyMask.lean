import TokenKit.Evm.Supply
import TokenKit.Evm.Safe

/-!
# The sum of the masked balances of a token against its total supply

For a token that keeps `balances[a]` in the bits of the mask `m` of slot `mapSlot a b` (a
Compound-style token: `uint96` balances, mask `2^96 - 1`) and its total supply in slot `t`:

- `sumBal m b C S`: the sum, as an integer, of the masked balance words (`m AND word`) of the
  2^160 addresses in the state `S` of the contract `C`. This is the sum of what `balanceOf`
  returns, whatever the bits outside of the mask are.
- `D m b t C S`: that sum minus the word of slot `t`; `Inv m b t C S`: `D = 0`.
- `D_read`, `D_write_bal`, `D_write_tot`, `D_write_other`: how one SLOAD or SSTORE changes `D`.
- `D_of_ro`: a run that only reads keeps `D`.

The mask, the base slot and the slot of the total supply are parameters: nothing here is about
one token. The sums are those of TokenKit/Evm/Supply.lean (`sumTo`), and so are the two facts
about keccak used as hypotheses (`Supply.NotBal`, `Supply.UniqBal`).
-/

namespace TokenKit.SupplyMask

open UsdtVerify
open TokenKit.Supply (sumTo sumTo_congr sumTo_update NotBal UniqBal ofNat_toNat)

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- `balances[i]` under the mask `m` (as an integer) for the address number `i`. -/
abbrev bal (m b : U256) (C : Address) (S : State.TransactionState) (i : Nat) : Int :=
  ((bitwiseAnd m (storageAt S C (mapSlot (BitVec.ofNat 256 i) b))).toNat : Int)

/-- The sum of the masked balances of the 2^160 addresses. -/
def sumBal (m b : U256) (C : Address) (S : State.TransactionState) : Int :=
  sumTo (bal m b C S) (2 ^ 160)

/-- The sum of the masked balances minus the total supply. -/
def D (m b t : U256) (C : Address) (S : State.TransactionState) : Int :=
  sumBal m b C S - ((storageAt S C t).toNat : Int)

/-- The invariant: the sum of all masked balances is the total supply. -/
def Inv (m b t : U256) (C : Address) (S : State.TransactionState) : Prop := D m b t C S = 0

variable {m b t : U256} {C : Address} {S : State.TransactionState}

theorem sumBal_read (c : Address) (n : U256) :
    sumBal m b C (readSlot S c n) = sumBal m b C S := by
  unfold sumBal
  exact sumTo_congr _ (fun i _ => by simp only [bal, storageAt_readSlot])

theorem sumBal_write_nb (hacc : hasAccount S C) {n : U256} (hn : NotBal b n) (v : U256) :
    sumBal m b C (writeSlot S C n v) = sumBal m b C S := by
  unfold sumBal
  refine sumTo_congr _ (fun i hi => ?_)
  have hi' : (BitVec.ofNat 256 i : U256).toNat < 2 ^ 160 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  simp only [bal, storageAt_writeSlot_of_ne hacc (fun e => hn _ hi' e.symm)]

theorem sumBal_write_bal (hacc : hasAccount S C) {x : U256} (hu : UniqBal b x)
    (hx : x.toNat < 2 ^ 160) (v : U256) :
    sumBal m b C (writeSlot S C (mapSlot x b) v) =
      sumBal m b C S - (bitwiseAnd m (storageAt S C (mapSlot x b))).toNat +
        (bitwiseAnd m v).toNat := by
  unfold sumBal
  have h := sumTo_update (f := bal m b C S) (g := bal m b C (writeSlot S C (mapSlot x b) v))
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
theorem D_read (c : Address) (n : U256) : D m b t C (readSlot S c n) = D m b t C S := by
  unfold D
  rw [sumBal_read, storageAt_readSlot]

/-- A write of the balance word of `x`: the sum moves by the new masked word minus the old
one. -/
theorem D_write_bal (hacc : hasAccount S C) {x : U256} (hu : UniqBal b x)
    (hx : x.toNat < 2 ^ 160) (ht : NotBal b t) (v : U256) :
    D m b t C (writeSlot S C (mapSlot x b) v) =
      D m b t C S - (bitwiseAnd m (storageAt S C (mapSlot x b))).toNat +
        (bitwiseAnd m v).toNat := by
  unfold D
  rw [sumBal_write_bal hacc hu hx, storageAt_writeSlot_of_ne hacc (ht x hx)]
  omega

/-- A write of the total supply. -/
theorem D_write_tot (hacc : hasAccount S C) (ht : NotBal b t) (v : U256) :
    D m b t C (writeSlot S C t v) = D m b t C S + (storageAt S C t).toNat - v.toNat := by
  unfold D
  rw [sumBal_write_nb hacc ht, storageAt_writeSlot_self hacc]
  omega

/-- A write of a slot that is no balance slot and not the total supply. -/
theorem D_write_other (hacc : hasAccount S C) {n : U256} (hn : NotBal b n) (hne : n ≠ t)
    (v : U256) : D m b t C (writeSlot S C n v) = D m b t C S := by
  unfold D
  rw [sumBal_write_nb hacc hn, storageAt_writeSlot_of_ne hacc (Ne.symm hne)]

/-- A run that only reads keeps `D`. -/
theorem D_of_ro {S' : State.TransactionState} {ss ss' : Substate} (h : Ro C S ss S' ss') :
    D m b t C S' = D m b t C S := by
  unfold D sumBal
  rw [h.storage C t, sumTo_congr (g := bal m b C S) _ (fun i _ => by
    show ((bitwiseAnd m (storageAt S' C _)).toNat : Int) = ((bitwiseAnd m (storageAt S C _)).toNat : Int)
    rw [h.storage])]

end TokenKit.SupplyMask

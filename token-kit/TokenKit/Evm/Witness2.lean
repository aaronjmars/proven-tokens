import TokenKit.Evm.Witness

/-!
# Witness lemmas for calls that move the amount 1

A witness state gives the word 5 to a few slots and 0 to the others, and the witness call moves
the amount 1. The slots are terms (`mapSlot ...`): no fact about keccak is used, so a slot read
after a write may or may not be the slot written. The lemmas here follow a bound through such
writes instead:

- `bd_read`, `bd_write`: every word of the contract is at most 5, after a read or a write of a
  word at most 5.
- `pos_read`, `pos_write`, `pos_of_eq5`: the word of one slot is at least 1, after a read or a
  write of a word at least 1.
- `sub_le5`, `sub_pos`, `add_pos`: the words written (`5 - 1`, and `x + 1` for `x` at most 5).
- `ge_ok`, `gt_ok`, `gt3_ok`, `noov1`, `noov2`, `eq_ok`: the checks of old Solidity code
  (`require(a >= 1)`, `require(!(1 > a))`, SafeMath sub, `require(b + 1 >= b)`, the first check
  of SafeMath add, an address check) hold for such words.

Nothing here is about one token.
-/

namespace TokenKit.Witness

open UsdtVerify

open EthLib.Base (U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

variable {S : State.TransactionState} {C : Address}

theorem bd_read (h : ∀ n, (storageAt S C n).toNat ≤ 5) (c : Address) (k : U256) :
    ∀ n, (storageAt (readSlot S c k) C n).toNat ≤ 5 := by
  intro n
  rw [storageAt_readSlot]
  exact h n

theorem bd_write {m v : U256} (hacc : hasAccount S C) (h : ∀ n, (storageAt S C n).toNat ≤ 5)
    (hv : v.toNat ≤ 5) : ∀ n, (storageAt (writeSlot S C m v) C n).toNat ≤ 5 :=
  fun n => le_writeSlot hacc h hv n

theorem pos_of_eq5 {x : U256} (h : x = 5) : 1 ≤ x.toNat := by
  subst h
  decide

theorem pos_read {n : U256} (h : 1 ≤ (storageAt S C n).toNat) (c : Address) (k : U256) :
    1 ≤ (storageAt (readSlot S c k) C n).toNat := by
  rw [storageAt_readSlot]
  exact h

theorem pos_write {n m v : U256} (hacc : hasAccount S C) (h : 1 ≤ (storageAt S C n).toNat)
    (hv : 1 ≤ v.toNat) : 1 ≤ (storageAt (writeSlot S C m v) C n).toNat := by
  by_cases e : n = m
  · subst e
    rw [storageAt_writeSlot_self hacc]
    exact hv
  · rw [storageAt_writeSlot_of_ne hacc e]
    exact h

theorem sub_le5 {x : U256} (h : x = 5) : (sub x 1).toNat ≤ 5 := by
  subst h
  decide

theorem sub_pos {x : U256} (h : x = 5) : 1 ≤ (sub x 1).toNat := by
  subst h
  decide

theorem add_pos {x : U256} (h : x.toNat ≤ 5) : 1 ≤ (add x 1).toNat := by
  have h1 : (1 : U256).toNat = 1 := rfl
  simp only [add, BitVec.toNat_add, h1]
  omega

theorem ge_ok {x : U256} (h : x = 5) : isZero (lessThan x 1) ≠ 0 := by
  subst h
  decide

theorem gt_ok {x : U256} (h : x = 5) : isZero (greaterThan 1 x) ≠ 0 := by
  subst h
  decide

theorem gt3_ok {x : U256} (h : 1 ≤ x.toNat) :
    isZero (isZero (isZero (greaterThan 1 x))) ≠ 0 := by
  have e : greaterThan 1 x = 0 := by
    refine if_neg ?_
    have h1 : (1 : U256).toNat = 1 := rfl
    omega
  rw [e]
  decide

theorem noov1 (x : U256) (h : x.toNat ≤ 5) : isZero (lessThan (add x 1) x) ≠ 0 := by
  have e : lessThan (add x 1) x = 0 := by
    refine if_neg ?_
    have h1 : (1 : U256).toNat = 1 := rfl
    simp only [add, BitVec.toNat_add, h1]
    omega
  rw [e]
  decide

theorem noov2 (x : U256) (h : x.toNat ≤ 5) : isZero (isZero (lessThan (add x 1) x)) = 0 := by
  have e : lessThan (add x 1) x = 0 := by
    refine if_neg ?_
    have h1 : (1 : U256).toNat = 1 := rfl
    simp only [add, BitVec.toNat_add, h1]
    omega
  rw [e]
  decide

end TokenKit.Witness

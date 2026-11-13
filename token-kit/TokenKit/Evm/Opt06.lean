import TokenKit.Evm.Prune
import TokenKit.Evm.Opt
import TokenKit.Evm.SupplyOpt

/-!
# Shapes of old Solidity (0.5, 0.6) compiled with the optimizer

Solidity before 0.8 has no built-in overflow check: a contract in the style of DAI checks with a
`require` and then calls a SafeMath `sub` or `add`, which the optimizer compiles as
`ISZERO (GT (SUB x a) x)` and `ISZERO (LT (ADD x a) x)`. The ABI decoder masks an address
argument with AND (it does not revert on dirty bits) and tests the size of the call data with
`CALLDATASIZE - 4 < n`.

- `toNat_toU256_lt`, `mask_toU256`, `mask_toU256'`: the word of an address is below `2^160`, so
  its mask is the word itself.
- `equal_caller_mask`, `caller_masked`: `msg.sender == address(msg.sender)` is never 0 (the rule
  `caller_mask` of `paths.dead_rules`, scripts/gen_paths.py).
- `sub_check_of_ge`, `sub_checked h`: after `require(a <= x)`, the check `x - a <= x` of the
  SafeMath sub cannot fail (the rule `sub_after_ge`).
- `le_of_sub_check`, `sub_nat_check`, `add_bound_check`, `add_nat_check`: the two SafeMath checks
  as facts about natural numbers.
- `size_check_iff`: the test `CALLDATASIZE - 4 < n` of the ABI decoder.
- `and_mask_mask`: a word masked twice is the word masked once.
- `Supply.sub_fact_gt1`, `Supply.sub_fact_chk`: the same two facts about a difference, over the
  integers, for the supply proofs (`supply.checked06`, scripts/gen_supply.py).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The word of an address is below `2^160`. -/
theorem toNat_toU256_lt (a : Address) : a.toU256.toNat < 2 ^ 160 := by
  have h := EthLib.Base.toNat_toU256_toAddressMasked a.toU256
  rw [EthLib.Base.toAddressMasked_toU256] at h
  rw [h]
  exact Nat.mod_lt _ (by decide)

/-- The mask of 160 bits, as a natural number. -/
theorem toNat_and_mask (w : U256) :
    (bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256)).toNat =
      w.toNat % 2 ^ 160 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 160

/-- The masked word of an address is the word. -/
theorem mask_toU256 (a : Address) :
    bitwiseAnd a.toU256 (1461501637330902918203684832716283019655932542975 : U256) = a.toU256 := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_mask]
  exact Nat.mod_eq_of_lt (toNat_toU256_lt a)

/-- The same with the mask on the left. -/
theorem mask_toU256' (a : Address) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) a.toU256 = a.toU256 := by
  rw [← and_mask_comm]
  exact mask_toU256 a

/-- A word masked twice is the word masked once. -/
theorem and_mask_mask (w : U256) :
    bitwiseAnd (bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256))
      (1461501637330902918203684832716283019655932542975 : U256) =
      bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_mask, toNat_and_mask, Nat.mod_mod]

/-- `msg.sender == address(msg.sender)` is never 0. -/
theorem equal_caller_mask (a : Address) :
    equal a.toU256
      (bitwiseAnd a.toU256 (1461501637330902918203684832716283019655932542975 : U256)) ≠ 0 := by
  rw [mask_toU256, equal_self]
  decide

/-- The same with the mask on the left. -/
theorem equal_caller_mask' (a : Address) :
    equal a.toU256
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) a.toU256) ≠ 0 := by
  rw [mask_toU256', equal_self]
  decide

/-- Close the test of the caller against its own masked word. -/
macro "caller_masked" : tactic =>
  `(tactic| first | exact equal_caller_mask _ | exact equal_caller_mask' _)

/-- `ISZERO (GT (SUB x a) x)` is not 0 exactly when the difference did not wrap: `a ≤ x`. -/
theorem le_of_sub_check {a x : U256} (h : isZero (greaterThan (sub x a) x) ≠ 0) :
    a.toNat ≤ x.toNat := by
  have hle := Supply.le_of_cond_gt1 h
  have ha := a.isLt
  have hx := x.isLt
  simp only [sub, BitVec.toNat_sub] at hle
  omega

/-- After the check of the SafeMath sub, the difference as a natural number. -/
theorem sub_nat_check {a x : U256} (h : isZero (greaterThan (sub x a) x) ≠ 0) :
    (sub x a).toNat = x.toNat - a.toNat := by
  have hle := le_of_sub_check h
  have ha := a.isLt
  have hx := x.isLt
  simp only [sub, BitVec.toNat_sub]
  omega

/-- After `require(a <= x)`, the check `x - a <= x` of the SafeMath sub cannot fail. -/
theorem sub_check_of_ge {a x : U256} (h : isZero (greaterThan a x) ≠ 0) :
    isZero (greaterThan (sub x a) x) ≠ 0 := by
  have hle := Supply.le_of_cond_gt1 h
  have ha := a.isLt
  have hx := x.isLt
  have hs : (sub x a).toNat = x.toNat - a.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  have hn : ¬(sub x a).toNat > x.toNat := by
    rw [hs]
    omega
  have e : greaterThan (sub x a) x = 0 := if_neg hn
  rw [e]
  decide

/-- Close the check of a SafeMath sub from the earlier `require` on the same word, `h`. -/
macro "sub_checked " h:ident : tactic => `(tactic| (
  have hsc := $h
  try simp only [storageAt_readSlot] at hsc
  try simp only [storageAt_readSlot]
  exact sub_check_of_ge hsc))

/-- `ISZERO (LT (ADD x a) x)` is not 0 exactly when the sum did not wrap. -/
theorem add_bound_check {a x : U256} (h : isZero (lessThan (add x a) x) ≠ 0) :
    x.toNat + a.toNat < 2 ^ 256 := by
  have hle := Supply.le_of_cond_lt1 h
  have ha := a.isLt
  have hx := x.isLt
  simp only [add, BitVec.toNat_add] at hle
  omega

/-- After the check of the SafeMath add, the sum as a natural number. -/
theorem add_nat_check {a x : U256} (h : isZero (lessThan (add x a) x) ≠ 0) :
    (add x a).toNat = x.toNat + a.toNat := by
  have hb := add_bound_check h
  simp only [add, BitVec.toNat_add]
  omega

/-- The test of the ABI decoder of old Solidity: `CALLDATASIZE - 4 < n` is 0 exactly when the
call data holds the selector and `n` bytes of arguments. -/
theorem size_check_iff {size n : Nat} (h4 : 4 ≤ size) (hs : size < 2 ^ 256) (hn : n < 2 ^ 256) :
    isZero (lessThan (sub (BitVec.ofNat 256 size) (4 : U256)) (BitVec.ofNat 256 n)) ≠ 0 ↔
      4 + n ≤ size := by
  have h4' : (4 : U256).toNat = 4 := by decide
  have hsub : (sub (BitVec.ofNat 256 size) (4 : U256)).toNat = size - 4 := by
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, h4', Nat.mod_eq_of_lt hs]
    omega
  constructor
  · intro h
    have hle := Supply.le_of_cond_lt1 h
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hle
    omega
  · intro h
    have hnl : ¬(sub (BitVec.ofNat 256 size) (4 : U256)).toNat < (BitVec.ofNat 256 n : U256).toNat := by
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
      omega
    have e : lessThan (sub (BitVec.ofNat 256 size) (4 : U256)) (BitVec.ofNat 256 n) = 0 :=
      if_neg hnl
    rw [e]
    decide

namespace Supply

/-- After `require(a <= x)` compiled as `ISZERO (GT a x)`, the difference `x - a` does not wrap. -/
theorem sub_fact_gt1 {a x : U256} (h : isZero (greaterThan a x) ≠ 0) :
    ((sub x a).toNat : Int) = x.toNat - a.toNat ∧ a.toNat ≤ x.toNat := by
  have hle := le_of_cond_gt1 h
  have ha := a.isLt
  have hx := x.isLt
  have e : (sub x a).toNat = x.toNat - a.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  omega

/-- After the check `ISZERO (GT (SUB x a) x)` of the SafeMath sub, the difference does not
wrap. -/
theorem sub_fact_chk {a x : U256} (h : isZero (greaterThan (sub x a) x) ≠ 0) :
    ((sub x a).toNat : Int) = x.toNat - a.toNat ∧ a.toNat ≤ x.toNat := by
  have hle := le_of_sub_check h
  have e := sub_nat_check h
  omega

end Supply

end TokenKit

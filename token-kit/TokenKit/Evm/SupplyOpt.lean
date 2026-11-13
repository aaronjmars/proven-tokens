import TokenKit.Evm.Supply2
import TokenKit.Evm.Opt

/-!
# Checked arithmetic of Solidity 0.8, as facts about natural numbers

Solidity 0.8 checks every addition and subtraction. With the optimizer on, the check of
`a + v` is compiled as `GT a (NOT v)` (the sum wraps exactly when `a > 2^256 - 1 - v`), and the
check of `a - v` as `LT a v`.

- `add_bound_not`, `add_fact_not`: after `ISZERO (GT a (NOT v))` is not 0, the sum does not wrap.
- `le_of_cond_gt1`: `ISZERO (GT a b)` not 0 means `a ≤ b`.
- `gt_of_cond`, `lt_of_cond`: a comparison that is not 0, as an order on natural numbers.

Nothing here is about one token.
-/

namespace TokenKit.Supply

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- `ISZERO (GT a b)` is not 0: `a ≤ b`. -/
theorem le_of_cond_gt1 {a b : U256} (h : isZero (greaterThan a b) ≠ 0) : a.toNat ≤ b.toNat := by
  by_cases hgt : a.toNat > b.toNat
  · exfalso
    apply h
    have e : greaterThan a b = 1 := if_pos hgt
    rw [e]
    decide
  · omega

theorem toNat_bitwiseNot (v : U256) : (bitwiseNot v).toNat = 2 ^ 256 - 1 - v.toNat := by
  have hv := v.isLt
  simp only [bitwiseNot, BitVec.toNat_not]

/-- The check of a Solidity 0.8 addition with the optimizer on: the sum is below `2^256`. -/
theorem add_bound_not {a v : U256} (h : isZero (greaterThan a (bitwiseNot v)) ≠ 0) :
    a.toNat + v.toNat < 2 ^ 256 := by
  have hle := le_of_cond_gt1 h
  rw [toNat_bitwiseNot] at hle
  have hv := v.isLt
  omega

/-- After the check of a Solidity 0.8 addition with the optimizer on, the sum does not wrap. -/
theorem add_fact_not {a v : U256} (h : isZero (greaterThan a (bitwiseNot v)) ≠ 0) :
    ((add a v).toNat : Int) = a.toNat + v.toNat := by
  have hb := add_bound_not h
  have e : (add a v).toNat = a.toNat + v.toNat := by
    simp only [add, BitVec.toNat_add]
    omega
  rw [e]
  omega

/-- The same as a fact about natural numbers. -/
theorem add_nat_not {a v : U256} (h : isZero (greaterThan a (bitwiseNot v)) ≠ 0) :
    (add a v).toNat = a.toNat + v.toNat := by
  have hb := add_bound_not h
  simp only [add, BitVec.toNat_add]
  omega

/-- After `require(a >= v)`, the difference as a natural number. -/
theorem sub_nat_lt1 {a v : U256} (h : isZero (lessThan a v) ≠ 0) :
    (sub a v).toNat = a.toNat - v.toNat := by
  have hle := le_of_cond_lt1 h
  have ha := a.isLt
  have hv := v.isLt
  simp only [sub, BitVec.toNat_sub]
  omega

end TokenKit.Supply

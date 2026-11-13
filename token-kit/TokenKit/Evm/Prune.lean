import UsdtVerify.Evm.Storage
import TokenKit.Evm.Rules
import EthLib.Execution.Evm.Instructions.Comparison

/-!
# A branch that an earlier branch decides

Compiled code often tests the same fact twice in two shapes: `a < b` then `b > a`, or a word
then its double ISZERO, or the same slot read again. A path that takes the two tests in opposite
ways has no run. The generator (`scripts/gen_paths.py`, option `prune: "normalized"`) follows
only the side that the earlier condition allows, and proves the later condition from the earlier
one with the tactic `decided`.

- `isZero_eq_zero_iff` (in Rules.lean): `isZero x = 0` exactly when `x` is not 0.
- `gt_swap`: `greaterThan a b = lessThan b a`.
- `add_second`, `dead_add2`: the second check of a SafeMath add (`c >= b` after `c >= a`, with
  `c = a + b`) cannot fail: a sum that did not wrap is above both terms.
- `decided h`: closes a goal `c ≠ 0` or `c = 0` from the hypothesis `h` when the two are the same
  after ISZERO chains are removed, GT is written as LT, and reads of the state are dropped.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (U256)
open EthLib.Execution.Evm

theorem gt_swap (a b : U256) : greaterThan a b = lessThan b a := rfl

/-- Close `c ≠ 0` or `c = 0` from an earlier condition on the same fact in another shape. -/
macro "decided " h:ident : tactic => `(tactic| (
  have hdec := $h
  simp only [storageAt_readSlot, isZero_eq_zero_iff, gt_swap, ne_eq, Classical.not_not]
    at hdec ⊢
  exact hdec))

/-- The second check of a SafeMath add: `c = a + v` with `c >= a` has `c >= v`. -/
theorem add_second {a v : U256} (h : isZero (isZero (lessThan (add a v) a)) = 0) :
    isZero (isZero (isZero (lessThan (add a v) v))) ≠ 0 := by
  simp only [isZero_eq_zero_iff, Classical.not_not, ne_eq] at h ⊢
  have hn : ¬(add a v).toNat < a.toNat := by
    intro hlt
    have e : lessThan (add a v) a = 1 := if_pos hlt
    rw [e] at h
    exact absurd h (by decide)
  have hm : ¬(add a v).toNat < v.toNat := by
    have ha := a.isLt
    have hv := v.isLt
    simp only [add, BitVec.toNat_add] at hn ⊢
    omega
  exact if_neg hm

/-- Close the second check of a SafeMath add from the first one, a hypothesis of the context. -/
macro "dead_add2" : tactic => `(tactic| exact add_second (by assumption))

end TokenKit

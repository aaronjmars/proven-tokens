import TokenKit.Evm.Prune
import TokenKit.Evm.Readable

/-!
# A credit after a debit cannot overflow

A transfer as compiled by old Solidity checks `balance[from] >= v` and
`balance[to] + v >= balance[to]` on the start state, writes `balance[from] - v`, and then adds
`v` to `balance[to]` with SafeMath, which checks the overflow again on the state after the first
write. That second check cannot fail: if the two slots are the same slot the word is now
`balance[from] - v`, and adding `v` back does not wrap; if not, it is the word of the first
check. No fact about keccak is used: the proof splits on the equality of the two slot keys.

- `credit_fits`: the two cases, on words.
- `dead_credit h1 h2`: closes the first check of the SafeMath add after the debit, from the two
  earlier conditions `h1` (enough balance) and `h2` (no overflow on the start state).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (U256)
open EthLib.Execution.Evm

theorem credit_fits {a b v : U256} (h1 : isZero (lessThan a v) ≠ 0)
    (h2 : isZero (lessThan (add b v) b) ≠ 0) :
    isZero (isZero (lessThan (add b v) b)) = 0 ∧
      isZero (isZero (lessThan (add (sub a v) v) (sub a v))) = 0 := by
  simp only [isZero_eq_zero_iff, Classical.not_not, ne_eq] at h1 h2 ⊢
  refine ⟨h2, ?_⟩
  have hle : v.toNat ≤ a.toNat := by
    by_cases hlt : a.toNat < v.toNat
    · exfalso
      have e : lessThan a v = 1 := if_pos hlt
      rw [e] at h1
      exact absurd h1 (by decide)
    · omega
  have ha := a.isLt
  have hv := v.isLt
  have hs : (sub a v).toNat = a.toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  have hadd : (add (sub a v) v).toNat = a.toNat := by
    simp only [add, BitVec.toNat_add, hs]
    omega
  exact if_neg (by rw [hadd, hs]; omega)

/-- Close the first check of the SafeMath add of a credit that follows the debit. -/
macro "dead_credit " h1:ident h2:ident : tactic => `(tactic| (
  have e1 := $h1
  have e2 := $h2
  simp (disch := supply_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot]
    at e1 e2 ⊢
  split
  · exact (credit_fits e1 e2).2
  · exact (credit_fits e1 e2).1))

end TokenKit

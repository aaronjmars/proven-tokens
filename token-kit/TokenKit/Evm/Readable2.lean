import TokenKit.Evm.Readable
import TokenKit.Evm.Supply2

/-!
# More helpers for the readable corollaries (old Solidity shapes)

- `pos_of_cond`: `require(v > 0)` as compiled (`ISZERO ISZERO (GT v 0)` is not 0).
- `ne_of_cond1`: `require(w != 0)` as compiled by solc 0.4 (`ISZERO (EQ w 0)` is not 0).
- `add_bound_lt`: after `require(b + v >= b)`, the sum is below `2^256`.
- `low_byte3`: the low byte of a word under three masks.

`le_of_cond_gt1`, `div_one`, `log2` and `logs_logSub2` were here too; they are in Readable.lean,
which the other tokens share.

Nothing here is about one token.
-/

namespace TokenKit.Readable

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

theorem pos_of_cond {v : U256} (h : isZero (isZero (greaterThan v 0)) ≠ 0) : 0 < v.toNat := by
  by_cases hp : (0 : U256).toNat < v.toNat
  · simpa using hp
  · exfalso
    apply h
    have e : greaterThan v 0 = 0 := if_neg hp
    rw [e]
    decide

theorem ne_of_cond1 {w : U256} (h : isZero (equal w 0) ≠ 0) : w ≠ 0 := by
  intro e
  apply h
  subst e
  decide

theorem add_bound_lt {b v : U256} (h : isZero (lessThan (add b v) b) ≠ 0) :
    b.toNat + v.toNat < 2 ^ 256 := by
  have f := Supply.add_fact_lt h
  have := (add b v).isLt
  omega

/-- The low byte of a word, after the DIV by 1 is removed. -/
theorem low_byte3 (w : U256) :
    bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) w)) =
      BitVec.ofNat 256 (w.toNat % 256) := by
  have h := low_byte w
  rw [div_one] at h
  exact h

end TokenKit.Readable

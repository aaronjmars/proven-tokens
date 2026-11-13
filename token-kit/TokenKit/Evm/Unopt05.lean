import TokenKit.Evm.Opt06
import TokenKit.Evm.Supply2

/-!
# Shapes of old Solidity (0.5) compiled with the optimizer off

A contract in the style of DAI compiled with no optimizer: `require(x >= a)` is
`ISZERO (LT x a)`, the checked `sub` is `ISZERO (GT (SUB x a) x)` and the checked `add` is
`ISZERO (LT (ADD x a) x)` (the last two as with the optimizer, TokenKit/Evm/Opt06.lean). A mask
of an address is applied two or three times, and a boolean is normalised with a double ISZERO
more than once.

- `sub_check_of_ge_lt`, `sub_checked_lt`: after `require(x >= a)`, the check of the SafeMath sub
  cannot fail (the rule `sub_after_ge_lt` of `paths.dead_rules`, scripts/gen_paths.py).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm

/-- After `require(x >= a)` compiled as `ISZERO (LT x a)`, the check `x - a <= x` of the
SafeMath sub cannot fail. -/
theorem sub_check_of_ge_lt {a x : U256} (h : isZero (lessThan x a) ≠ 0) :
    isZero (greaterThan (sub x a) x) ≠ 0 := by
  have hs := Supply.sub_fact_lt1 h
  have hn : ¬(sub x a).toNat > x.toNat := by omega
  have e : greaterThan (sub x a) x = 0 := if_neg hn
  rw [e]
  decide

/-- Close the check of a SafeMath sub from the earlier `require` on the same word, `h`. -/
macro "sub_checked_lt " h:ident : tactic => `(tactic| (
  have hsc := $h
  try simp only [storageAt_readSlot] at hsc
  try simp only [storageAt_readSlot]
  exact sub_check_of_ge_lt hsc))

end TokenKit

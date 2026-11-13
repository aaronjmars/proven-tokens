#!/usr/bin/env python3
"""Write WbtcVerify/Wbtc/Lib.lean once, from the local lemma files of tokens/link (Lib.lean) and
tokens/wbt (Lib.lean): the rules that the generated block files of WBTC use and that the shared
library does not have. Run once; the result is kept in the project (the two source files may
move)."""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
TOK = os.path.dirname(os.path.dirname(HERE))
wbt = open(os.path.join(TOK, 'wbt/WbtVerify/Wbt/Lib.lean')).read()


def cut(a, b):
    i = wbt.index(a)
    j = wbt.index(b, i)
    return wbt[i:j]


logs = cut('/-- The substate after a LOG1', '/-! ## The shapes of Solidity 0.8')
tail = cut('/-- A log of the contract `C` with one topic. -/',
           '/-- The mask of a byte on the right')
link = open(os.path.join(TOK, 'link/LinkVerify/Link/Lib.lean')).read()
i = link.index('/-- The selector word of Solidity 0.4: the mask on the left. -/')
j = link.index('end TokenKit')
l04 = link[i:j]
out = '''import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Opt
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Supply2
import EthLib.Execution.Proofs.Evm.Logic.Copy
import WbtcVerify.Wbtc.Code

/-!
# Rules that WBTC needs and the shared library does not have yet

Nothing here is about WBTC alone, but for `codeWord_4507`: every other lemma is a candidate for
the kit (see `status.json`, `to_merge_into_kit`). They live here because the shared library is
owned by another line of work while this token is built. The lemmas are copies of the ones of
tokens/link (Lib.lean, Sep.lean) and tokens/wbt (Lib.lean), in the namespace of this token.

Solidity 0.4 with the optimizer (the dispatcher):

- `and_div_selector`, `div_and_selector`: the selector word, `(calldata[0] / 2^224) & 0xffffffff`
  in either order of AND, is the number `selector`.
- `size_isZero_zero`, `size_isZero_ne`: the test `CALLDATASIZE == 0` (not used by WBTC).
- `equal_key_zero_r`: EQ of a word that is no key with a key, the word first.
- `Supply.add_fact_ltc`: the SafeMath addition `c = a + b; assert(c >= a)`.

Logs:

- `logSub1`, `log1ZK`: the substate after a LOG1 and the rule of a LOG1 of no bytes (the events
  `Pause()` and `Unpause()`).
- `logStuckW`: a LOG in a static frame is stuck (it fails with any gas). The path generator
  uses it for a LOG that comes before the first SSTORE of a path (`claimOwnership`).
- `log1`, `logs_logSub1`: a log with one topic, for the readable corollaries.
- `D_congr`: the sum of the balances minus the total supply reads the storage of the contract
  only.

The code:

- `codeWord_4507`: the 32 bytes of the code from 4507 (0x119b) are the topic of the event
  `Transfer(address,address,uint256)`. The code reads it with CODECOPY (it is no PUSH32).
-/

namespace WbtcVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## Solidity 0.4 with the optimizer -/

''' + l04 + '''/-- The SafeMath addition of Solidity 0.4 with the optimizer on: `c = v + b; assert(c >= b)`. -/
theorem Supply.add_fact_ltc {v b : U256} (h : isZero (lessThan (add v b) b) ≠ 0) :
    ((add v b).toNat : Int) = v.toNat + b.toNat := by
  have e : add v b = add b v := by
    unfold add
    exact BitVec.add_comm _ _
  rw [e] at h ⊢
  have := TokenKit.Supply.add_fact_lt h
  omega

/-! ## Logs -/

''' + logs + tail + '''/-! ## The code -/

theorem codeWord_4507 : (⟨(bufferRead CODE 4507 32).toArray⟩ : ByteArray) =
    wordBytes (0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef : U256) := by
  simp only [bufferRead, byteAt_CODE]
  decide +kernel

end WbtcVerify
'''
open(os.path.join(TOK, 'wbtc/WbtcVerify/Wbtc/Lib.lean'), 'w').write(out)
print('Lib.lean written')

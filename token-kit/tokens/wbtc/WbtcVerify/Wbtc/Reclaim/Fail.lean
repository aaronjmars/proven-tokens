import WbtcVerify.Wbtc.Reclaim.Readable

/-!
# `reclaimToken(address token)`: the runs that fail

The failing branches of `reclaimToken`, from the bytes:

| branch | where | what happens | proved as |
|---|---|---|---|
| value not 0 | 537..548 | revert, no output | `reclaimToken_p0` (exact, generated), `reclaim_fails_value` |
| caller not the owner | 1405..1435 | revert, no output | `reclaimToken_p1` (exact), `reclaim_fails_not_owner` |
| token has no code, first test | 1521..1534 | revert, no output | `reclaimCodeA_p0` (exact, from 1522), `reclaim_fails_no_code` |
| first call fails | 1537..1552 | revert with the return data of the callee | `rc_bubble1` (exact), `ok_reclaim` |
| first call returns fewer than 32 bytes | 1562..1576 | revert, no output | `reclaimMid_p0` (exact, from 1562), `ok_reclaim` |
| token has no code, second test | 3196..3209 | revert, no output | `reclaimCodeB_p0` (exact, from 3197), `ok_reclaim` |
| second call fails | 3212..3227 | revert with the return data of the callee | `rc_bubble2` (exact), `ok_reclaim` |
| second call returns fewer than 32 bytes | 3237..3251 | revert, no output | `reclaimEnd_p0` (exact, from 3237), `ok_reclaim` |
| second call returns the word 0 | 3252..3259 | revert, no output | `reclaimEnd_p1` (exact, from 3237), `ok_reclaim` |

"exact" is a `Logic.SpecG` to `Halted true output gas state substate` from the frame named, with
the exact gas, state and substate. `ok_reclaim` is the other direction, for the whole function
and every runner: a run that ends with NO error took none of these branches (both children
ended with no error, returned at least 32 bytes, the token had code at both tests, the second
word is not 0).

What is proved here:

- `rc_bubble1`, `rc_bubble2`: the code after each CALL, from the flag 0: the frame reverts and
  its output is EXACTLY the return data of the failed call.
- `reclaim_fails_value`, `reclaim_fails_not_owner`, `reclaim_fails_no_code`: whole function,
  every runner: with a value, a caller that is not the owner, or a token with no code in the
  state before, every run ends with an error.

Assumed: Berlin ≤ fork < Glamsterdam (Byzantium for the bubbles), one counter of gas, call data
below 2^256 bytes; for the bubbles, enough gas, a memory whose size is a multiple of 32 and
return data below 2^256 bytes.

Not covered: the branches after the first EXTCODESIZE are not joined into ONE exact statement
from the start of the function (frame at the start to the reverted frame, with gas): the kit
has EXTCODESIZE and CALL in outcome form only (what a finished run did), and the exact
segments above start at the frame after each of them. The bubbles with too little gas (the
kit's `bubble_no_ok`: no run ends with no error).
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## A failed call: the revert carries the return data of the callee -/

/-- The FIRST call failed (flag 0 after the CALL at 1536): with enough gas the frame REVERTS
and its output is exactly the return data `rd` of the failed call (the output of the child). The
gas is exact. -/
theorem rc_bubble1 (hfork : .byzantium ≤ fork) {a b c : U256} {rest : List U256}
    {rd mem : ByteArray} {gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hmod : mem.size % 32 = 0) (hsize : rd.size < 2 ^ 256)
    (hrest : rest.length + 7 < STACK_LIMIT)
    (hgas : 38 + 3 * wordCount rd.size +
      (extendMemory mem.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost ≤ gas) :
    Logic.SpecG fork
      (Logic.At CODE message 1537 ((0 : U256) :: a :: b :: c :: rest) mem gas st ss rd)
      (Halted true rd
        (gas - (38 + 3 * wordCount rd.size +
          (extendMemory mem.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost)) st ss) :=
  bubble_spec (pc := 1537) hfork hsize (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by simp only [List.length_cons]; omega) hmod hgas

/-- The SECOND call failed (flag 0 after the CALL at 3211): with enough gas the frame REVERTS
and its output is exactly the return data `rd` of the failed call (the output of the child). The
gas is exact. -/
theorem rc_bubble2 (hfork : .byzantium ≤ fork) {a b c : U256} {rest : List U256}
    {rd mem : ByteArray} {gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hmod : mem.size % 32 = 0) (hsize : rd.size < 2 ^ 256)
    (hrest : rest.length + 7 < STACK_LIMIT)
    (hgas : 38 + 3 * wordCount rd.size +
      (extendMemory mem.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost ≤ gas) :
    Logic.SpecG fork
      (Logic.At CODE message 3212 ((0 : U256) :: a :: b :: c :: rest) mem gas st ss rd)
      (Halted true rd
        (gas - (38 + 3 * wordCount rd.size +
          (extendMemory mem.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost)) st ss) :=
  bubble_spec (pc := 3212) hfork hsize (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by simp only [List.length_cons]; omega) hmod hgas

/-! ## Whole function: no run with no error -/

/-- With a value, every run of `reclaimToken` ends with an error. -/
theorem reclaim_fails_value (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hv : message.value ≠ 0) : s.error ≠ none := fun hok =>
  hv (isZero_ne_zero_iff.mp (ok_reclaim hfork hglam hsize' hsel start hrun hok).1)

/-- From a caller that is not the owner in slot 5, every run of `reclaimToken` ends with an
error. -/
theorem reclaim_fails_not_owner (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s)
    (hno : message.caller ≠
      toAddressMasked (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) :
    s.error ≠ none := fun hok =>
  hno (rc_caller_owner (ok_reclaim hfork hglam hsize' hsel start hrun hok).2.1)

/-- For a token with no code in the state before (an account with no code, or no account),
every run of `reclaimToken` ends with an error: the EXTCODESIZE test at 1521 stops it before
any message is sent. -/
theorem reclaim_fails_no_code (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) {c : ByteArray}
    (hc : state.getCode (state.getAccount (rcToken message)).codeHash = .ok c)
    (h0 : c.size = 0) : s.error ≠ none := by
  intro hok
  obtain ⟨-, -, c1, _, _, _, _, _, _, _, _, _, hc1, hcs1, -⟩ :=
    ok_reclaim hfork hglam hsize' hsel start hrun hok
  have e : c1 = c := Except.ok.inj (hc1.symm.trans hc)
  subst e
  apply hcs1
  rw [h0]
  rfl

end WbtcVerify

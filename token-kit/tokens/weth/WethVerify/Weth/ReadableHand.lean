import WethVerify.Weth.Readable
import WethVerify.Weth.TotalSupply
import WethVerify.Weth.Withdraw

/-!
# Readable corollaries of totalSupply and withdraw

The two functions that the generator does not follow to the end (they use ADDRESS, BALANCE and
CALL), so their readable corollaries are written by hand, from `ok_totalSupply_exact` and
`ok_withdraw_exact`. Same words as Weth/Readable.lean.

- `totalSupply_readable`: no value; returns the ether balance of the contract; no storage word
  changes; no log.
- `withdraw_readable`: no value; `wad` (arg1) at most `balanceOf[sender]` and at most the ether of
  the contract; exactly one message, to the sender, with `wad` wei and empty data, sent from a
  state where `balanceOf[sender]` is already lowered by `wad` and no other storage word of the
  contract has changed; that message ended with no error; the END state is the state its frame
  ended in; the logs are the logs after that frame and then `Withdrawal(sender, wad)`.

`withdraw_readable` says nothing about what the callee did between the send and the end: the END
storage is the one of the frame of the callee. What the callee can do to the contract is the
subject of `CalleeQuiet` (Weth/Invariant.lean), proved for the runner of the interpreter and
every callee in Weth/Reenter.lean. Its hypotheses `hglam`, `hcode`, `hdel`, `hdepth`, `hcall` are
those of `ok_withdraw_exact`; the runs where `hcode`, `hdepth` or `hcall` fail end with an error
(Weth/WithdrawAll.lean).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace WethVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Readable
open WethVerify WethVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-- totalSupply(): no value; returns the ether balance of the contract; changes no storage word
and logs nothing. -/
theorem totalSupply_readable (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.value = 0 ∧
      s.output = wordBytes (etherOf state message.currentTarget) ∧
      (∀ a n, storageAt s.state a n = storageAt state a n) ∧
      s.substate.logs = substate.logs := by
  obtain ⟨hc1, -, ho, -, hst, hss⟩ :=
    ok_totalSupply_exact hfork hsize hsize' hsel start within hrun hok
  refine ⟨value_of_cond hc1, ho, fun a n => ?_, ?_⟩
  · rw [hst]
    rfl
  · rw [hss]

/-- withdraw(wad): see the head of this file. -/
theorem withdraw_readable (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d) {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (hcall : wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message) ≤ gas)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.value = 0 ∧
      (arg1 message).toNat ≤ (balance message state (sender message)).toNat ∧
      (arg1 message).toNat ≤ (etherOf state message.currentTarget).toNat ∧
      ∃ caller msg child, Ran runChild caller msg child ∧ child.error = none ∧
        msg.caller = message.currentTarget ∧ msg.currentTarget = message.caller ∧
        msg.value = arg1 message ∧ msg.data = ByteArray.empty ∧
        (balance message caller.state (sender message)).toNat =
          (balance message state (sender message)).toNat - (arg1 message).toNat ∧
        (∀ n, n ≠ mapSlot (sender message) 3 →
          storageAt caller.state message.currentTarget n =
            storageAt state message.currentTarget n) ∧
        s.state = child.state ∧
        s.output = ByteArray.empty ∧
        s.substate.logs = (incorporateChild fork caller child).substate.logs.push
          (log2 message.currentTarget WITHDRAWAL (sender message) (wordBytes (arg1 message))) := by
  obtain ⟨hc1, hc2, -, hacc, hbal, caller, msg, child, hran, hce, -, hsend, -, ho, -, hst, hss⟩ :=
    ok_withdraw_exact hfork hglam hsize hsize' hsel hcode hdel hdepth hcall start within hrun hok
  obtain ⟨hcs, -, -, hmc, hmt, -, -, -, hmd, hmv, -⟩ := hsend
  have hkey : wKey message = mapSlot (sender message) 3 := by
    show mapSlot _ _ = mapSlot _ _
    rw [mask_idem]
  have hacc' : hasAccount (readSlot (readSlot state message.currentTarget (wKey message))
      message.currentTarget (wKey message)) message.currentTarget :=
    hasAccount_readSlot (hasAccount_readSlot hacc)
  have hstor : ∀ n, storageAt caller.state message.currentTarget n =
      if n = wKey message then sub (storageAt state message.currentTarget (wKey message))
        (wAmt message) else storageAt state message.currentTarget n := by
    intro n
    rw [hcs]
    show storageAt (wState message state) message.currentTarget n = _
    rw [storageAt_writeSlot_ite hacc']
    simp only [storageAt_readSlot]
  have hle := Supply.le_of_cond_lt hc2
  have hsub := Supply.sub_fact_lt hc2
  rw [hkey] at hstor hle hsub
  refine ⟨value_of_cond hc1, hle, hbal, caller, msg, child, hran, hce, hmc, ?_, hmv, hmd, ?_, ?_,
    ?_, ho, ?_⟩
  · rw [hmt]
    exact toAddressMasked_wSrc message
  · show (storageAt caller.state message.currentTarget (mapSlot (sender message) 3)).toNat =
      (storageAt state message.currentTarget (mapSlot (sender message) 3)).toNat -
        (wAmt message).toNat
    rw [hstor, if_pos rfl]
    omega
  · intro n hn
    rw [hstor]
    simp only [hn, ↓reduceIte]
  · rw [hst]
    exact incorporateChild_state caller child
  · rw [hss]

end WethVerify.Readable

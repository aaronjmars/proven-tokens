import WethVerify.Weth.Invariant
import TokenKit.Evm.Ether
import TokenKit.Evm.Stipend

/-!
# Reentrancy: the callee of `withdraw` cannot break the invariant, whatever its code

`withdraw(wad)` lowers `balanceOf[msg.sender]`, then sends `wad` wei to `msg.sender` with
Solidity's `transfer`: a CALL that asks for 0 gas when `wad` is not 0 (the message then gets the
stipend of 2300 gas) and for 2300 gas when `wad` is 0. So the message that the callee runs has at
most 2300 gas (`wSubCall_le`, from the bytes of the CALL and EthLib's `messageCallGas`).

`TokenKit/Evm/Stipend.lean` proves, by induction over EthLib's interpreter, that a message with
at most 2300 gas changes no account and no storage word, apart from the move of its own value:
SSTORE fails at 2300 gas or less, a CALL with value costs 9000, CREATE costs 32000, SELFDESTRUCT
costs 5000. The callee may call back into the contract (it can afford a warm CALL of 100 gas):
that inner run of the code of the contract is one of the messages of the induction, with less
than 2300 gas, so it cannot write a balance either.

- `calleeQuiet_process`: `CalleeQuiet` (Weth/Invariant.lean) holds for the runner of the
  interpreter (`processRunner`, EthLib's `processMessage`) and EVERY code of the callee, from
  Berlin. One hypothesis: the account of the contract has code in the state at the start
  (`hcodeC`; it is the contract whose code runs, so on a chain it holds).
- `calleeQuiet_noCode`, `calleeQuiet_stop`, `calleeQuiet_accept`: the same for three named
  callees: an address with no code, the one-byte contract STOP, and a contract that only accepts
  ether (PUSH1 0x80 PUSH1 0x40 MSTORE STOP). They are instances of `calleeQuiet_process`; they
  are here so that the assumption `CalleeQuiet` is shown to hold for real callees by name.
- `solvent_preserved_process`: `solvent_preserved` for the runner of the interpreter, with no
  assumption on the callee. This is the reentrancy theorem.

## What is covered

Forks: `calleeQuiet_process` needs Berlin or later (EthLib's SSTORE sentry is from Istanbul; the
rest of this project is from Berlin). `WithdrawReady` still asks for a fork before Glamsterdam,
because the rules of the CALL of `withdraw` itself (Evm/Call.lean) are proved for the gas rules
before Glamsterdam. So the reentrancy theorem covers Berlin, London, Paris, Shanghai, Cancun,
Prague and Osaka (and the BPO forks), with the one-counter gas meter, and not Glamsterdam.

The callee is ANY code, with or without an EIP-7702 delegation of an account that it calls.
`WithdrawReady` still asks that the caller of `withdraw` itself is not an EIP-7702 delegated
account from Prague (`del`): EthLib's rule for the CALL step does not cover a delegated target.
That limit is on the CALL step of the contract, not on what the callee does. Before Prague
`WithdrawReady` is only `fork < .glamsterdam` (`withdrawReady_prePrague`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace WethVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify.Paths WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-- The message of the CALL of `withdraw` gets at most 2300 gas: asked 0 plus the stipend when
`wad` is not 0, and at most the 2300 asked when `wad` is 0. -/
theorem wSubCall_le (message : Message fork) (S : State.TransactionState) (ss : Substate)
    (g : Nat) :
    (callGas fork S ss (wAsk message) (wSrc message) (wAmt message) g).subCall ≤ 2300 := by
  have hask := wAsk_le message
  have hz : wAmt message ≠ 0 → (wAsk message).toNat = 0 := by
    intro hv
    unfold wAsk isZero
    rw [if_neg hv]
    decide
  simp only [callGas, messageCallGas]
  by_cases hv : wAmt message = 0
  · rw [if_pos hv]
    split <;> omega
  · rw [if_neg hv]
    have := hz hv
    have hst : CALL_STIPEND = 2300 := rfl
    split <;> omega

/-- For the runner of the interpreter and every code of the callee, from Berlin: the message
that the CALL of `withdraw` sends, when it ends with no error, leaves every storage word of the
contract as it was and takes at most `wad` of its ether. The callee may call the contract
again. -/
theorem calleeQuiet_process (hberlin : .berlin ≤ fork) {bound gas : Nat}
    (calleeCode : ByteArray)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    CalleeQuiet (processRunner (Meter := Nat) fork bound) message state substate gas
      calleeCode := by
  intro caller msg child hran herr hsend
  obtain ⟨hcs, -, hgas, hcaller, hto, htarget, -, -, -, hval, hstv, -, -⟩ := hsend
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  have hist : Fork.istanbul ≤ fork := Nat.le_trans (by decide) hberlin
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  rw [hp] at hrun
  have hlow : msg.gas ≤ 2300 := by
    rw [hgas]
    exact wSubCall_le message _ _ _
  obtain ⟨h1, h2⟩ := Stipend.processMessage_quiet (Meter := Nat) hist msg.gas msg caller.state
    caller.substate.child _ _ rfl hlow (by rw [htarget]; rfl) child' hrun herr
  have hq0 := Stipend.quiet_startState msg caller.state
  have hcodeS : ((startState fork msg caller.state).getAccount message.currentTarget).codeHash ≠
      EMPTY_CODE_HASH := by
    rw [hq0.1, hcs]
    simp only [wState, State.TransactionState.getAccount_recordAccountRead, getAccount_writeSlot,
      getAccount_readSlot]
    exact hcodeC
  by_cases ht : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · obtain ⟨moved, hm, hq⟩ := h1 ht
    rw [hcaller, hto, hval, toAddressMasked_wSrc] at hm
    by_cases hself : message.currentTarget = message.caller
    · rw [← hself] at hm
      have hqm := Stipend.Quiet.of_sameOutside
        (State.TransactionState.sameOutside_moveEther_self hcodeS hm)
      have hall := (hq0.trans hqm).trans hq
      refine ⟨fun n => hall.2 _ _, ?_⟩
      unfold etherOf
      rw [hall.1]
      omega
    · obtain ⟨hs, hle, he⟩ := moveEther_outOf hself hcodeS hm
      refine ⟨fun n => ((hq.2 _ _).trans (hs n)).trans (hq0.2 _ _), ?_⟩
      have e1 : etherOf child'.val.state message.currentTarget =
          etherOf moved message.currentTarget := by
        unfold etherOf
        rw [hq.1]
      have e0 : etherOf (startState fork msg caller.state) message.currentTarget =
          etherOf caller.state message.currentTarget := by
        unfold etherOf
        rw [hq0.1]
      rw [e1, he, e0]
      omega
  · have hall := h2 ht
    refine ⟨fun n => hall.2 _ _, ?_⟩
    unfold etherOf
    rw [hall.1]
    omega

/-- `CalleeQuiet` holds when the caller of `withdraw` has no code. -/
theorem calleeQuiet_noCode (hberlin : .berlin ≤ fork) {bound gas : Nat}
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    CalleeQuiet (processRunner (Meter := Nat) fork bound) message state substate gas
      ByteArray.empty :=
  calleeQuiet_process hberlin _ hcodeC

/-- The one-byte contract STOP. -/
def STOP_CODE : ByteArray := ⟨#[0x00]⟩

/-- A contract that only accepts ether: PUSH1 0x80 PUSH1 0x40 MSTORE STOP. -/
def ACCEPT_CODE : ByteArray := ⟨#[0x60, 0x80, 0x60, 0x40, 0x52, 0x00]⟩

/-- `CalleeQuiet` holds when the caller of `withdraw` is the contract STOP. -/
theorem calleeQuiet_stop (hberlin : .berlin ≤ fork) {bound gas : Nat}
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    CalleeQuiet (processRunner (Meter := Nat) fork bound) message state substate gas STOP_CODE :=
  calleeQuiet_process hberlin _ hcodeC

/-- `CalleeQuiet` holds when the caller of `withdraw` is a contract that only accepts ether. -/
theorem calleeQuiet_accept (hberlin : .berlin ≤ fork) {bound gas : Nat}
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    CalleeQuiet (processRunner (Meter := Nat) fork bound) message state substate gas
      ACCEPT_CODE :=
  calleeQuiet_process hberlin _ hcodeC

/-- The reentrancy theorem. From Berlin, every run of the interpreter loop over `CODE` from pc 0,
with the runner of the interpreter for the messages that the code sends, that ends with no error
keeps the contract solvent. There is NO assumption on the callee of `withdraw`: its code is any
code, and it may call the contract again. `hw` asks only for `WithdrawReady` (the facts about
the CALL step of `withdraw` itself), and `hcodeC` that the account of the contract has code. -/
theorem solvent_preserved_process (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hinv : Backed message.value message.currentTarget state)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (processRunner (Meter := Nat) fork bound) evm within = .ok s)
    (hok : s.error = none) :
    Solvent message.currentTarget s.state :=
  solvent_preserved hfork hsize' hsep hinv
    (fun h hv => ⟨hw h hv, fun c _ => calleeQuiet_process hfork c hcodeC⟩)
    start within hrun hok

end WethVerify

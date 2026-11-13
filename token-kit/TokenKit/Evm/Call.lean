import TokenKit.Evm.Logic
import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.FailsOn
import EthLib.Execution.Proofs.State.Tracker
import UsdtVerify.Evm.Write

/-!
# CALL with empty ranges of input and output, for the `At` of usdt-verify

EthLib proves CALL in two rules: `call` (no value) and `callValue` (a value that is not 0). A
contract that sends `v` wei with `msg.sender.call.value(v)()` runs the same CALL in both cases.
This file joins the two rules in one statement, for every `v` that the current account holds.

- `callExtra`, `callGas`: the price of the call before the gas that it passes on, and the gas of
  the call (EthLib's `messageCallGas`).
- `CallSend`: the frame that the step hands to the runner and the message that it sends.
- `callL`: the rule, under any assumption on the frames that end messages (EthLib's
  `HoareUnder`).
- `callLowL`: a value above the balance of the current account sends no message and pushes 0.
- `Ran`: the frames that a runner gives. `call_ok`, `callLow_ok`: a run of the interpreter loop
  from the frame at the CALL that returns a frame goes on from the frame after the CALL.
- `callGas_cost_le`: the gas of the call is at most the gas asked for plus the price.
- account and code facts of `readSlot` and `writeSlot`.

The hypotheses of `callL` that EthLib's rules need and that this file does not remove:
`hglam` (before Glamsterdam), `hcode` (the state holds the code of the callee), `hdel` (from
Pectra, that code is no delegation), `hdepth` (the call depth is below the limit), `hgas` (the
gas covers the price of the call).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## Accounts and code under storage reads and writes -/

/-- A recorded storage read changes no account. -/
theorem getAccount_readSlot (S : State.TransactionState) (t : Address) (n : U256) (a : Address) :
    (readSlot S t n).getAccount a = S.getAccount a := rfl

/-- A storage write changes no account (its balance, nonce and code hash). -/
theorem getAccountOptional_writeSlot (S : State.TransactionState) (t : Address) (n v : U256)
    (a : Address) : (writeSlot S t n v).getAccountOptional a = S.getAccountOptional a := by
  unfold writeSlot
  split
  · rename_i s h
    rw [State.TransactionState.getAccountOptional_setStorage h]
    rfl
  · rfl

/-- A storage write changes no account (its balance, nonce and code hash). -/
theorem getAccount_writeSlot (S : State.TransactionState) (t : Address) (n v : U256)
    (a : Address) : (writeSlot S t n v).getAccount a = S.getAccount a := by
  unfold State.TransactionState.getAccount
  rw [getAccountOptional_writeSlot]

/-- A storage write keeps the code of every code hash. -/
theorem getCode_writeSlot (S : State.TransactionState) (t : Address) (n v : U256)
    (h : EthLib.Base.Hash32) : (writeSlot S t n v).getCode h = S.getCode h := by
  unfold writeSlot
  split
  · rename_i s hs
    rw [State.TransactionState.getCode_setStorage hs]
    rfl
  · rfl

/-! ## The gas of the call -/

/-- The price of a CALL of `v` wei to `to`, before the gas that it passes on: the access to the
account, 25000 when it sends value to a dead account, and 9000 when it sends value. -/
abbrev callExtra (fork : Fork) (state : State.TransactionState) (substate : Substate)
    (to v : U256) : Nat :=
  callBaseCost fork (coldAccount substate (toAddressMasked to)) +
    callNewAccountCost fork state (toAddressMasked to) v + callValueCost fork v

/-- The gas of a CALL of `v` wei to `to` that asks for `asked` gas with `gas` left and no growth
of memory: what the frame pays (`cost`) and what the message gets (`subCall`). -/
abbrev callGas (fork : Fork) (state : State.TransactionState) (substate : Substate)
    (asked to v : U256) (gas : Nat) : MessageCallGas :=
  messageCallGas fork v asked.toNat gas 0 (callExtra fork state substate to v)

/-- The frame pays at most the gas asked for plus the price. -/
theorem callGas_cost_le (fork : Fork) (state : State.TransactionState) (substate : Substate)
    (asked to v : U256) (gas : Nat) :
    (callGas fork state substate asked to v gas).cost ≤
      asked.toNat + callExtra fork state substate to v := by
  simp only [callGas, messageCallGas]
  split
  · exact Nat.add_le_add_right (Nat.min_le_left _ _) _
  · exact Nat.le_refl _

/-- The price of a call with no value, from Berlin and before Glamsterdam. -/
theorem callExtra_zero (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (state : State.TransactionState) (substate : Substate) (to : U256) :
    callExtra fork state substate to 0 =
      if coldAccount substate (toAddressMasked to) then 2600 else 100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  have hsd : fork ≥ .spuriousDragon := Nat.le_trans (by decide) hfork
  simp [callExtra, callBaseCost_of_berlin hfork hglam, callNewAccountCost, callValueCost, hng, hsd]

/-! ## The message of the call -/

/-- The frame `caller` that the step of a CALL hands to the runner and the message `msg` that it
sends: a call of `v` wei from the current account to the address of `to`, with no data, at one
more depth, not static, with the code `calleeCode`. The frame has the state before the call with
the two accounts recorded as read: the value has not moved yet, the runner moves it. -/
def CallSend (message : Message fork) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (asked to v : U256) (calleeCode : ByteArray) (caller : Evm fork Nat)
    (msg : Message fork) : Prop :=
  caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
      message.currentTarget ∧
    caller.substate = accessAccount substate (toAddressMasked to) ∧
    msg.gas = (callGas fork state substate asked to v gas).subCall ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
    msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
    msg.code = calleeCode ∧ msg.data = .empty ∧ msg.value = v ∧
    (v ≠ 0 → msg.shouldTransferValue = true) ∧ msg.depth = message.depth + 1 ∧
    msg.isStatic = false

/-- CALL of `v` wei, at most the balance of the current account, with empty ranges, from a frame
that is not static. The rule holds for every frame `child` that ends the message and meets the
assumption `callee`. The caller pushes 1 when `child` ends with no error and 0 otherwise, gets
back the gas that `child` leaves, and takes its state and its substate from `child`. -/
theorem callL (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callExtra fork state substate to v ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧ child.gas ≤ msg.gas ∧
        CallSend message gas state substate asked to v calleeCode caller msg ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (callGas fork state substate asked to v gas).cost + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  refine HoareUnder.of_exists (R := fun rd => Logic.At code message pc
    (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest) memory gas state substate rd)
    (fun evm h => ⟨evm.returnData, h.toLogic⟩) fun rd => ?_
  by_cases hv : v = 0
  · subst hv
    have hx := callExtra_zero hfork hglam state substate to
    refine (call (callee := callee) (asked := asked) (inputStart := inputStart)
      (outputStart := outputStart) (rest := rest) (returnData := rd) hfork hglam hlt hbyte hcode
      hdel hdepth rfl (by rw [← hx]; exact hgas)).consequence (fun _ h => h) ?_
    rintro after ⟨caller, msg, child, hc, hle, hs, hss, hmg, m1, m2, m3, m4, m5, m6, m7, m8, m9,
      hat⟩
    refine ⟨caller, msg, child, hc, hle,
      ⟨hs, hss, ?_, m1, m2, m3, m4, m5, m6, m7, fun h => (h rfl).elim, m8, by rw [m9, hstatic]⟩,
      ?_⟩
    · rw [hmg, callGas, hx]
    · rw [callGas, hx]
      exact At.ofLogic hat
  · have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
      simp [extendMemory]
    have h := callValue (callee := callee) (asked := asked) (inputStart := inputStart)
      (inputSize := 0) (outputStart := outputStart) (outputSize := 0) (rest := rest)
      (returnData := rd) hfork hglam hlt hbyte hv hstatic hbal hcode hdel hdepth rfl
      (by rw [hext]; exact hgas)
    rw [hext] at h
    refine h.consequence (fun _ hp => hp) ?_
    rintro after ⟨caller, msg, child, hc, hle, hs, hss, hmg, m1, m2, m3, m4, m5, md, m6, m7, m8,
      m9, hat⟩
    refine ⟨caller, msg, child, hc, hle,
      ⟨hs, hss, hmg, m1, m2, m3, m4, m5, ?_, m6, fun _ => m7, m8, m9⟩, ?_⟩
    · simpa [memoryExtend_zero, memoryReadBytes] using md
    · have hat' := At.ofLogic hat
      simpa [memoryExtend_zero, memoryWrite, callGas, callExtra, coldAccount, accessAccount] using hat'

/-- CALL of more wei than the current account holds, with empty ranges: no message is sent and
the frame pushes 0. It gets back the gas that it would pass on. -/
theorem callLowL (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : message.isStatic = false)
    (hbal : (state.getAccount message.currentTarget).balance < v)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : callExtra fork state substate to v ≤ gas) :
    Hoare fork
      (At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      (At code message (pc + 1) (0 :: rest) memory
        (gas - (callGas fork state substate asked to v gas).cost +
          (callGas fork state substate asked to v gas).subCall)
        ((state.recordAccountRead (toAddressMasked to)).recordAccountRead message.currentTarget)
        (accessAccount substate (toAddressMasked to))) := by
  have hv : v ≠ 0 := by
    rintro rfl
    exact absurd hbal (by simp)
  have hext : extendMemory memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  intro evm hp
  have h := callValueLow (asked := asked) (inputStart := inputStart) (inputSize := 0)
    (outputStart := outputStart) (outputSize := 0) (rest := rest) (returnData := evm.returnData)
    hfork hglam hlt hbyte hv hstatic hbal hcode hdel rfl (by rw [hext]; exact hgas)
  rw [hext] at h
  obtain ⟨after, hr, hat⟩ := h evm hp.toLogic
  refine ⟨after, hr, ?_⟩
  have hat' := At.ofLogic hat
  simpa [memoryExtend_zero, callGas, callExtra, coldAccount, accessAccount] using hat'

/-! ## Runs that return a frame -/

/-- The frames that the runner gives: `child` ends the message `msg` sent from `caller`. -/
def Ran {bound : Nat} (runChild : MessageRunner fork Nat bound) (caller : Evm fork Nat)
    (msg : Message fork) (child : Evm fork Nat) : Prop :=
  ∃ lt child', runChild caller msg lt = .ok child' ∧ child'.1 = child

/-- Each frame that a runner gives is one that it gives. -/
theorem meetsOk_ran {bound : Nat} (runChild : MessageRunner fork Nat bound) :
    MeetsOk (Ran runChild) runChild :=
  fun _ _ lt child ran => ⟨lt, child, ran, rfl⟩

/-- A run of the interpreter loop from the frame at a CALL that returns a frame `s`: the runner
gave a frame `child` for the message of the call, and the loop runs the frame after the call
to `s`. For every runner and every bound. -/
theorem call_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callExtra fork state substate to v ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    ∃ caller msg child after, Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
      CallSend message gas state substate asked to v calleeCode caller msg ∧
      At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
        (gas - (callGas fork state substate asked to v gas).cost + child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  obtain ⟨after, ⟨caller, msg, child, hc, hle, hsend, hat⟩, w, h⟩ :=
    HoareOn.runFrame_of_ok
      (HoareUnder.toOn (callL (callee := Ran runChild) (asked := asked)
        (inputStart := inputStart) (outputStart := outputStart) (rest := rest) hfork hglam hlt
        hbyte hstatic hbal hcode hdel hdepth hgas))
      (meetsOk_ran runChild) start within hrun
  exact ⟨caller, msg, child, after, hc, hle, hsend, hat, w, h⟩

/-- A run of the interpreter loop from the frame at a CALL of more wei than the account holds
that returns a frame `s`: the loop runs the frame after the call, with 0 pushed, to `s`. -/
theorem callLow_ok (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : message.isStatic = false)
    (hbal : (state.getAccount message.currentTarget).balance < v)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : callExtra fork state substate to v ≤ gas)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    ∃ after, At code message (pc + 1) (0 :: rest) memory
        (gas - (callGas fork state substate asked to v gas).cost +
          (callGas fork state substate asked to v gas).subCall)
        ((state.recordAccountRead (toAddressMasked to)).recordAccountRead message.currentTarget)
        (accessAccount substate (toAddressMasked to)) after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s :=
  Hoare.runFrame_of_ok (callLowL (asked := asked) (inputStart := inputStart)
    (outputStart := outputStart) (rest := rest) hfork hglam hlt hbyte hstatic hbal hcode hdel
    hgas) start within hrun

end TokenKit

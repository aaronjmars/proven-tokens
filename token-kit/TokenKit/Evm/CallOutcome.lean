import TokenKit.Evm.Call
import EthLib.Execution.Proofs.Evm.Logic.CallSteps
import EthLib.Execution.Proofs.Evm.Logic.LessGas
import UsdtVerify.Evm.Call

/-!
# Every outcome of a CALL with empty ranges, before Glamsterdam

`Call.lean` has the rule of a CALL that sends its message (`callL`) and of a CALL of more wei
than the account holds (`callLowL`), each under side conditions (frame not static, gas for the
price, depth below the limit, code found). This file removes the side conditions: it says what a
run of the interpreter loop does from a frame at a CALL in EVERY case.

- Steps of a CALL that sends value, in the cases EthLib has no lemma for:
  `callStep_missing` (the state fails to give the code of the callee: the step fails),
  `callStep_value_poor` (the gas does not cover the price: the frame halts with an error),
  `callStep_value_static` (static frame: the frame halts with an error),
  `callStep_value_deep` (depth limit: no message, the frame pushes 0).
- `Sent`: the frame handed to the runner and the message sent. It is `CallSend` for a frame that
  may be static (a CALL with no value is allowed in a static frame; the message is then static).
- `callS`: the rule of a CALL that sends its message, for any value and a static frame when the
  value is 0.
- `callGas_subCall_le`: the message gets at most the gas asked for, plus the stipend of 2300
  when it carries value.
- `call_outcome`: a run of the loop from the frame at the CALL that returns a frame `s` is one of
  three: (1) `s` has an error (missing code, gas below the price, value in a static frame);
  (2) no message was sent and the loop went on from the next opcode with 0 pushed (value above
  the balance, depth limit); (3) the runner ran the message of `Sent` and the loop went on from
  the next opcode with the flag of the child pushed.

Scope: from Berlin and before Glamsterdam (EthLib's rules of CALL), and a callee whose code is
no EIP-7702 delegation (`hdel`). Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

/-! ## Steps of a CALL with value that send no message -/

section Steps

variable {fork : Fork} {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256}

/-- Before Glamsterdam, a CALL to an address whose code the state fails to give: the step
fails. -/
theorem callStep_missing (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {e : State.StateError}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest)
    (hmissing : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .error e) :
    StepFails (callStep .call evm) := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  simp only at hmissing ⊢
  have hab : (EvmError.state e).aborts = true := rfl
  refine .inl ⟨.state e, ?_⟩
  simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
    bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hmissing, Except.mapError, keepReads]

/-- Before Glamsterdam, a CALL with value whose frame holds less gas than the price of the call
(access, new account, value, memory): the frame halts with an error. -/
theorem callStep_value_poor (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : evm.gas <
      (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost) :
    StepFails (callStep .call evm) := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : gas < E + (extendMemory memory.size [(i, isz), (o, osz)]).cost := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have h1 : ¬(E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas) := by omega
  have h2 : gas < g.toNat + E + (extendMemory memory.size [(i, isz), (o, osz)]).cost := by omega
  have hab : EvmError.outOfGas.aborts = false := rfl
  refine .inr ?_
  simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
    bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, keepReads, GasMeter.gasLeft, hE, h1, h2,
    exceptionalHalt]

/-- Before Glamsterdam, a CALL with value in a static frame that holds the gas of the price:
the frame halts with an error (it must not change the state). -/
theorem callStep_value_static (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = true)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    StepFails (callStep .call evm) := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hstatic ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
    omega
  have hab : EvmError.writeInStaticContext.aborts = false := rfl
  refine .inr ?_
  simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
    bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hstatic, hE,
    hgas', Nat.not_lt.mpr hmin, exceptionalHalt]

/-- Before Glamsterdam, a CALL with value at the depth limit, from a frame that is not static
and holds the value and the gas of the price: no message is sent and the frame pushes 0. -/
theorem callStep_value_deep (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = false)
    (hbal : v ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdeep : STACK_DEPTH_LIMIT < evm.message.depth + 1)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdeep hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
    omega
  have hbal' : ¬(state.getAccount message.currentTarget).balance < v := by
    simpa [BitVec.lt_def, BitVec.le_def] using hbal
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hdeep, hstatic, hE,
    hgas', Nat.not_lt.mpr hmin, hbal', skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
    pushWord, Stack.push, hlen, advance, Functor.map, Except.map]

end Steps

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## The message of a CALL from a frame that may be static -/

/-- The frame `caller` that the step of a CALL hands to the runner and the message `msg` that it
sends. It is `CallSend` with the static flag of the calling frame: a CALL with no value is
allowed in a static frame, and its message is then static too. -/
def Sent (message : Message fork) (gas : Nat) (state : State.TransactionState)
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
    msg.isStatic = message.isStatic

/-- The message gets at most the gas asked for, plus the stipend when it carries value. -/
theorem callGas_subCall_le (fork : Fork) (state : State.TransactionState) (substate : Substate)
    (asked to v : U256) (gas : Nat) :
    (callGas fork state substate asked to v gas).subCall ≤
      asked.toNat + (if v = 0 then 0 else CALL_STIPEND) := by
  simp only [callGas, messageCallGas]
  split
  · exact Nat.add_le_add_right (Nat.min_le_left _ _) _
  · exact Nat.le_refl _

/-- CALL of `v` wei, at most the balance of the current account, with empty ranges. The frame
may be static when `v` is 0. The rule holds for every frame `child` that ends the message and
meets the assumption `callee`. -/
theorem callS (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hstatic : v ≠ 0 → message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callExtra fork state substate to v ≤ gas) :
    HoareUnder fork callee
      (At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧ child.gas ≤ msg.gas ∧
        Sent message gas state substate asked to v calleeCode caller msg ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (callGas fork state substate asked to v gas).cost + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  by_cases hv : v = 0
  · subst hv
    refine HoareUnder.of_exists (R := fun rd => Logic.At code message pc
      (asked :: to :: 0 :: inputStart :: 0 :: outputStart :: 0 :: rest) memory gas state substate
      rd) (fun evm h => ⟨evm.returnData, h.toLogic⟩) fun rd => ?_
    have hx := callExtra_zero hfork hglam state substate to
    refine (call (callee := callee) (asked := asked) (inputStart := inputStart)
      (outputStart := outputStart) (rest := rest) (returnData := rd) hfork hglam hlt hbyte hcode
      hdel hdepth rfl (by rw [← hx]; exact hgas)).consequence (fun _ h => h) ?_
    rintro after ⟨caller, msg, child, hc, hle, hs, hss, hmg, m1, m2, m3, m4, m5, m6, m7, m8, m9,
      hat⟩
    refine ⟨caller, msg, child, hc, hle,
      ⟨hs, hss, ?_, m1, m2, m3, m4, m5, m6, m7, fun h => (h rfl).elim, m8, m9⟩, ?_⟩
    · rw [hmg, callGas, hx]
    · rw [callGas, hx]
      exact At.ofLogic hat
  · refine (callL (callee := callee) (asked := asked) (inputStart := inputStart)
      (outputStart := outputStart) (rest := rest) hfork hglam hlt hbyte (hstatic hv) hbal hcode
      hdel hdepth hgas).consequence (fun _ h => h) ?_
    rintro after ⟨caller, msg, child, hc, hle,
      ⟨hs, hss, hmg, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩, hat⟩
    exact ⟨caller, msg, child, hc, hle,
      ⟨hs, hss, hmg, m1, m2, m3, m4, m5, m6, m7, m8, m9, by rw [m10, hstatic hv]⟩, hat⟩

/-! ## Every outcome of a run from the frame at a CALL -/

/-- The step of a frame at a CALL is the step of the call. -/
theorem step_at_call {stack : List U256} {evm : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) : step fork evm = callStep .call evm := by
  obtain ⟨hc, -, -, hp, -⟩ := start
  subst hc hp
  exact UsdtVerify.Complete.step_call hlt hbyte

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a CALL with empty ranges, of any value `v`, that returns a
frame `s`. One of three holds.

1. `s` has an error. This is the case when the state fails to give the code of the callee, when
   the gas is below the price of the call, and when the call carries value in a static frame.
2. No message was sent: the loop went on from the next opcode with 0 pushed. This is the case
   when the value is above the balance of the account, and at the depth limit.
3. The runner ran the message of `Sent` to a frame `child`, and the loop went on from the next
   opcode with the flag of `child` pushed, its gas given back, and its state taken in.

`hdel`: the code of the callee is no EIP-7702 delegation (from Pectra). -/
theorem call_outcome (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to v inputStart outputStart : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ mem g st ss after, At code message (pc + 1) (0 :: rest) mem g st ss after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s) ∨
    ∃ calleeCode caller msg child after,
      state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode ∧
      Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
      Sent message gas state substate asked to v calleeCode caller msg ∧
      At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
        (gas - (callGas fork state substate asked to v gas).cost + child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .call evm := step_at_call start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss⟩ := id start
  have hext : extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  -- a step that fails gives an error
  have fails : StepFails (callStep .call evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  -- a step to the next opcode with 0 pushed
  have next : (∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output) →
      ∃ mem g st ss after, At code message (pc + 1) (0 :: rest) mem g st ss after ∧
        ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
          Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
    rintro ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8⟩
    rw [← hstep] at hn
    rw [runFrame_of_step_eq_next hrunning hn] at hrun
    exact ⟨after.memory, after.gas, after.state, after.substate, after,
      ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, rfl, rfl, a6.trans hrunning,
        a7.trans herr, a8.trans hout, rfl, rfl⟩, _, hrun⟩
  have hcases : (∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash =
        .error e) ∨
      ∃ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c := by
    cases state.getCode (state.getAccount (toAddressMasked to)).codeHash with
    | error e => exact .inl ⟨e, rfl⟩
    | ok c => exact .inr ⟨c, rfl⟩
  rcases hcases with ⟨e, hcode⟩ | ⟨calleeCode, hcode⟩
  · exact .inl (fails (callStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  ·
    have hd := hdel calleeCode hcode
    have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
        .ok calleeCode := by rw [hs]; exact hcode
    -- the message is sent
    have sent : (v ≠ 0 → message.isStatic = false) →
        v ≤ (state.getAccount message.currentTarget).balance →
        message.depth + 1 ≤ STACK_DEPTH_LIMIT → callExtra fork state substate to v ≤ gas →
        ∃ calleeCode caller msg child after,
          state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode ∧
          Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
          Sent message gas state substate asked to v calleeCode caller msg ∧
          At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
            (gas - (callGas fork state substate asked to v gas).cost + child.gas)
            (incorporateChild fork caller child).state
            (incorporateChild fork caller child).substate after ∧
          ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
            Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' =
              .ok s := by
      intro hstatic hbal hdepth hgas
      obtain ⟨after, ⟨caller, msg, child, hch, hle, hsend, hat⟩, w, h⟩ :=
        HoareOn.runFrame_of_ok
          (HoareUnder.toOn (callS (callee := Ran runChild) (asked := asked)
            (inputStart := inputStart) (outputStart := outputStart) (rest := rest) hfork hglam
            hlt hbyte hstatic hbal hcode hd hdepth hgas))
          (meetsOk_ran runChild) start within hrun
      exact ⟨calleeCode, caller, msg, child, after, hcode, hch, hle, hsend, hat, w, h⟩
    by_cases hv : v = 0
    · subst hv
      have hx := callExtra_zero hfork hglam state substate to
      have hcb : callBaseCost fork
          (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) =
          callExtra fork state substate to 0 := by
        rw [hx, callBaseCost_of_berlin hfork hglam, hss]
      have hst0 : evm.stack.val = asked :: to ::
          ((if CallKind.call.sendsValue then [0] else []) ++
            inputStart :: 0 :: outputStart :: 0 :: rest) := hst
      by_cases hgas : callExtra fork state substate to 0 ≤ gas
      · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
        · exact .inr (.inr (sent (fun h => (h rfl).elim)
            (BitVec.le_def.mpr (Nat.zero_le _)) hdepth hgas))
        · obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
            callStep_deep_of_routes (kind := .call) (route := none) hfork hst0 hcode' hd
              (by rw [hm]; omega)
              (by
                rw [hext, hcb, hg]
                show callExtra fork state substate to 0 + 0 + 0 ≤ gas
                omega)
          exact .inr (.inl (next ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8⟩))
      · refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := none) hfork hst0
          hcode' hd ?_))
        rw [hext, hcb, hg]
        show gas < callExtra fork state substate to 0 + 0 + 0
        omega
    · have hprice : (callBaseCost fork
            (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked to) v + callValueCost fork v) +
          (extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)]).cost =
          callExtra fork state substate to v := by
        rw [hext, hs, hss]
        rfl
      by_cases hgas : callExtra fork state substate to v ≤ gas
      · by_cases hstatic : message.isStatic = false
        · by_cases hbal : v ≤ (state.getAccount message.currentTarget).balance
          · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
            · exact .inr (.inr (sent (fun _ => hstatic) hbal hdepth hgas))
            · exact .inr (.inl (next (callStep_value_deep hfork hglam hst hv
                (by rw [hm]; exact hstatic) (by rw [hs, hm]; exact hbal) hcode' hd
                (by rw [hm]; omega) (by rw [hprice, hg]; exact hgas))))
          · obtain ⟨after, hat, w, h⟩ := callLow_ok (asked := asked) (inputStart := inputStart)
              (outputStart := outputStart) (rest := rest) hfork hglam hlt hbyte hstatic
              (BitVec.not_le.mp hbal) hcode hd hgas start within hrun
            exact .inr (.inl ⟨_, _, _, _, after, hat, w, h⟩)
        · refine .inl (fails (callStep_value_static hfork hglam hst hv
            (by rw [hm]; simpa using hstatic) hcode' hd (by rw [hprice, hg]; exact hgas)))
      · refine .inl (fails (callStep_value_poor hfork hglam hst hv hcode' hd
          (by rw [hprice, hg]; omega)))

end TokenKit

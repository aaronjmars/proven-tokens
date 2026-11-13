import TokenKit.Evm.CallOutcome
import EthLib.Execution.Proofs.Evm.Logic.Route
import EthLib.Execution.Proofs.Evm.Logic.Keeps

/-!
# Every outcome of a CALL with no value and an input range inside memory, before Glamsterdam

`CallOutcome.lean` says what a run of the interpreter loop does from a frame at a CALL in every
case, for EMPTY ranges of input and output (the message has no data). This file gives the same
statements for the CALL of `transferAndCall`:
`CALL(asked, to, 0, inputStart, inputSize, outputStart, 0)`, with value 0, an input range that
lies inside the memory of the frame, and an output range of size 0.

- `extendMemory_in`: these two ranges grow memory by nothing and cost nothing.
- `SentIn`: the frame handed to the runner and the message sent. It is `Sent` with value 0 and
  with the data `data` in place of no data. It also names the fields that EthLib's rule of a
  call along a route fixes and that `Sent` leaves out: `shouldTransferValue` (true, for every
  CALL), `reservoir` (0), `disablePrecompiles` (false), and the block and the transaction of the
  message (those of the calling frame).
- `callInS`: the rule of a CALL that sends its message. The data of the message are the bytes of
  the input range, `memoryReadBytes memory inputStart.toNat inputSize.toNat`. The memory after
  the call is the memory before it.
- `callIn_outcome`: a run of the loop from the frame at the CALL that returns a frame `s` is one
  of three: (1) `s` has an error (missing code, gas below the price); (2) no message was sent
  and the loop went on from the next opcode with 0 pushed (depth limit); (3) the runner ran the
  message of `SentIn` and the loop went on from the next opcode with the flag of the child
  pushed.
- `callIn_outcome_any`: the same three cases with no assumption on the code of the callee, which
  may be an EIP-7702 delegation. It says less of the third case: the state of the frame handed
  to the runner reads as the state before the call, the message goes to the address of `to` with
  the bytes of the input range as its data, and the gas after the call is some number.

Covered: value 0; every `asked`, `to`, `inputStart`, `inputSize` (0 included) with
`inputStart + inputSize ≤ memory.size` (`hin`); every `outputStart` with output size 0; a
static frame and a frame that is not static (the message is static when the frame is); every
runner and every bound in `callIn_outcome`; every fork from Berlin and before Glamsterdam; one
counter of gas.

Not covered: a value that is not 0; an input range that ends past the memory (memory would grow
and the price would have a memory part); an output size that is not 0 (the caller would write
the output of the child to memory); a callee whose code is an EIP-7702 delegation (`hdel`),
except in `callIn_outcome_any`; Glamsterdam and later; what the child does (the rule holds for every frame that the runner
gives).

Gas: the kit's `callGas` and `callExtra` fit this call as they are (value 0, no growth of
memory), so this file defines no new gas terms. The price is `callExtra fork state substate to
0` (2600 for a cold account and 100 for a warm one, `callExtra_zero`), the frame pays
`(callGas fork state substate asked to 0 gas).cost` and the message gets `.subCall` of it.

`callInS` is derived from EthLib's `callRoute` with the route `none` (the rule that EthLib's
`callWith` is derived from: `callWith` drops the five extra fields of the message, which
`SentIn` keeps). The steps that send no message are EthLib's `callStep_fails_of_routes` and
`callStep_deep_of_routes` and the kit's `callStep_missing`; all three hold for every range, so
this file proves no new step lemma. Nothing here is about one token.
-/

namespace TokenKit


open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## The growth of memory -/

/-- An input range inside a memory of `size` bytes and an output range of size 0 grow nothing
and cost nothing. The input range may have size 0. The start of the output range is any. -/
theorem extendMemory_in {size : Nat} {inputStart inputSize outputStart : U256}
    (hin : inputStart.toNat + inputSize.toNat ≤ size) :
    extendMemory size [(inputStart, inputSize), (outputStart, 0)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero size _ fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans hin (le_ceil32 size)))
    · rw [List.mem_singleton.mp hp]
      exact .inl rfl

/-! ## The message of a CALL with no value and some data -/

/-- The frame `caller` that the step of a CALL with no value hands to the runner and the message
`msg` that it sends: a call of 0 wei from the current account to the address of `to`, with the
data `data`, at one more depth, with the code `calleeCode`, static when the calling frame is.
The frame has the state before the call with the two accounts recorded as read. The message has
no reservoir of gas, runs precompiles as usual, and keeps the block and the transaction of the
calling frame. -/
def SentIn (message : Message fork) (gas : Nat) (state : State.TransactionState)
    (substate : Substate) (asked to : U256) (data : ByteArray) (calleeCode : ByteArray)
    (caller : Evm fork Nat) (msg : Message fork) : Prop :=
  caller.state = (state.recordAccountRead (toAddressMasked to)).recordAccountRead
      message.currentTarget ∧
    caller.substate = accessAccount substate (toAddressMasked to) ∧
    msg.gas = (callGas fork state substate asked to 0 gas).subCall ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked to ∧
    msg.target = some (toAddressMasked to) ∧ msg.codeAddress = some (toAddressMasked to) ∧
    msg.code = calleeCode ∧ msg.data = data ∧ msg.value = 0 ∧
    msg.shouldTransferValue = true ∧ msg.depth = message.depth + 1 ∧
    msg.isStatic = message.isStatic ∧ msg.reservoir = 0 ∧ msg.disablePrecompiles = false ∧
    msg.blockEnv = message.blockEnv ∧ msg.txEnv = message.txEnv

/-! ## The rule of the call -/

/-- CALL of 0 wei with an input range inside memory and an output range of size 0. The frame may
be static. The message carries the bytes of the input range. The rule holds for every frame
`child` that ends the message and meets the assumption `callee`. The caller pushes 1 when
`child` ends with no error and 0 otherwise, keeps its memory, gets back the gas that `child`
leaves, and takes its state and its substate from `child`. -/
theorem callInS (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callExtra fork state substate to 0 ≤ gas) :
    HoareUnder fork callee
      (At code message pc
        (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧ child.gas ≤ msg.gas ∧
        SentIn message gas state substate asked to
          (memoryReadBytes memory inputStart.toNat inputSize.toNat) calleeCode caller msg ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (callGas fork state substate asked to 0 gas).cost + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  refine HoareUnder.of_exists (R := fun rd => Logic.At code message pc
    (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: 0 :: rest) memory gas state
    substate rd) (fun evm h => ⟨evm.returnData, h.toLogic⟩) fun rd => ?_
  have hx := callExtra_zero hfork hglam state substate to
  have hext := extendMemory_in (outputStart := outputStart) hin
  have hE : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) none =
      callExtra fork state substate to 0 := by
    rw [hx, callBaseCost_of_berlin hfork hglam] <;> rfl
  have hme : memoryExtend memory (ExtendMemory.expandBy ⟨0, 0⟩) = memory :=
    memoryExtend_zero memory
  have hw : ∀ out : ByteArray, memoryWrite memory outputStart.toNat
      (out.extract 0 (min (0 : U256).toNat out.size)) = memory := by
    intro out
    simp [memoryWrite]
  have h := (callRoute (callee := callee) (asked := asked) (inputStart := inputStart)
    (inputSize := inputSize) (outputStart := outputStart) (outputSize := 0) (rest := rest)
    (returnData := rd) (route := none) hfork hlt hbyte hcode hdel hdepth
    (by rw [hext, hE]; exact hgas)).toUnder
  refine h.consequence (fun _ hp => hp) ?_
  rintro after ⟨caller, msg, child,
    ⟨s1, s2, m1, mr, m2, m3, mt, mca, mc, mdp, md, m5, mst, m6, m7, mb, mtx⟩, hc, hle, hat⟩
  rw [hext, hE] at m1 hat
  rw [hext, hme] at md
  rw [hme] at hat
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := At.ofLogic hat
  exact ⟨caller, msg, child, hc, hle,
    ⟨s1, s2, m1, m2, m3, mt, mca, mc, md, m5, mst, m6, m7, mr, mdp, mb, mtx⟩,
    a1, a2, a3, a4, a5, a6.trans (hw child.output), a7, a8, a9, a10, a11, a12⟩

/-! ## Every outcome of a run from the frame at the CALL -/

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a CALL of 0 wei, with an input range inside memory and an
output range of size 0, that returns a frame `s`. One of three holds.

1. `s` has an error. This is the case when the state fails to give the code of the callee, and
   when the gas is below the price of the call.
2. No message was sent: the loop went on from the next opcode with 0 pushed. This is the case at
   the depth limit.
3. The runner ran the message of `SentIn`, with the bytes of the input range as its data, to a
   frame `child`, and the loop went on from the next opcode with the flag of `child` pushed, the
   memory as it was, the gas of `child` given back, and its state taken in.

`hdel`: the code of the callee is no EIP-7702 delegation (from Pectra). -/
theorem callIn_outcome (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc
      (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: 0 :: rest)
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
      SentIn message gas state substate asked to
        (memoryReadBytes memory inputStart.toNat inputSize.toNat) calleeCode caller msg ∧
      At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
        (gas - (callGas fork state substate asked to 0 gas).cost + child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .call evm := step_at_call start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss⟩ := id start
  have hext : extendMemory evm.memory.size [(inputStart, inputSize), (outputStart, 0)] =
      ⟨0, 0⟩ := by
    rw [hmem]
    exact extendMemory_in hin
  -- a step that fails gives an error
  have fails : StepFails (callStep .call evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have hcases : (∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash =
        .error e) ∨
      ∃ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c := by
    cases state.getCode (state.getAccount (toAddressMasked to)).codeHash with
    | error e => exact .inl ⟨e, rfl⟩
    | ok c => exact .inr ⟨c, rfl⟩
  rcases hcases with ⟨e, hcode⟩ | ⟨calleeCode, hcode⟩
  · exact .inl (fails (callStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  · have hd := hdel calleeCode hcode
    have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
        .ok calleeCode := by rw [hs]; exact hcode
    have hx := callExtra_zero hfork hglam state substate to
    have hcb : callBaseCost fork
        (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) =
        callExtra fork state substate to 0 := by
      rw [hx, callBaseCost_of_berlin hfork hglam, hss]
    have hst0 : evm.stack.val = asked :: to ::
        ((if CallKind.call.sendsValue then [0] else []) ++
          inputStart :: inputSize :: outputStart :: 0 :: rest) := hst
    by_cases hgas : callExtra fork state substate to 0 ≤ gas
    · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
      · -- the message is sent
        obtain ⟨after, ⟨caller, msg, child, hch, hle, hsend, hat⟩, w, h⟩ :=
          HoareOn.runFrame_of_ok
            (HoareUnder.toOn (callInS (callee := Ran runChild) (asked := asked)
              (inputStart := inputStart) (inputSize := inputSize) (outputStart := outputStart)
              (rest := rest) hfork hglam hlt hbyte hin hcode hd hdepth hgas))
            (meetsOk_ran runChild) start within hrun
        exact .inr (.inr ⟨calleeCode, caller, msg, child, after, hcode, hch, hle, hsend, hat,
          w, h⟩)
      · -- the depth limit: no message, 0 pushed
        obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
          callStep_deep_of_routes (kind := .call) (route := none) hfork hst0 hcode' hd
            (by rw [hm]; omega)
            (by
              rw [hext, hcb, hg]
              show callExtra fork state substate to 0 + 0 + 0 ≤ gas
              omega)
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        exact .inr (.inl ⟨after.memory, after.gas, after.state, after.substate, after,
          ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, rfl, rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout, rfl, rfl⟩, _, hrun⟩)
    · -- the gas is below the price
      refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := none) hfork hst0
        hcode' hd ?_))
      rw [hext, hcb, hg]
      show gas < callExtra fork state substate to 0 + 0 + 0
      omega

/-! ## Every outcome, for any callee -/

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a CALL of 0 wei, with an input range inside memory and an
output range of size 0, that returns a frame `s`. No assumption on the code of the callee, which
may be an EIP-7702 delegation. One of three holds.

1. `s` has an error. This is the case when the state fails to give the code of the callee or,
   from Pectra, of the address it delegates to, and when the gas is below the price of the call
   (the access to the callee and, for a delegation, to the delegate).
2. No message was sent: the loop went on from the next opcode with 0 pushed (depth limit).
3. The runner ran a message `msg` from a frame `caller` to a frame `child`. The state of
   `caller` reads as the state before the call (only reads were recorded: of the callee, of the
   delegate if any, of the calling account). The message goes to the address of `to`, also when
   that account delegates: the delegate gives the code only. Its data are the bytes of the input
   range. The loop went on from the next opcode with the flag of `child` pushed, the memory as it
   was, some gas `g`, and the state of `child` taken in. -/
theorem callIn_outcome_any (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc
      (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: 0 :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ mem g st ss after, At code message (pc + 1) (0 :: rest) mem g st ss after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s) ∨
    ∃ caller msg child after g,
      Ran runChild caller msg child ∧
      Logic.ReadsAs caller.state state ∧
      msg.currentTarget = toAddressMasked to ∧ msg.target = some (toAddressMasked to) ∧
      msg.data = memoryReadBytes memory inputStart.toNat inputSize.toNat ∧
      At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory g
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .call evm := step_at_call start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss⟩ := id start
  have hext := extendMemory_in (size := memory.size) (outputStart := outputStart) hin
  have hme : memoryExtend memory (ExtendMemory.expandBy ⟨0, 0⟩) = memory :=
    memoryExtend_zero memory
  have hw : ∀ out : ByteArray, memoryWrite memory outputStart.toNat
      (out.extract 0 (min (0 : U256).toNat out.size)) = memory := by
    intro out
    simp [memoryWrite]
  have fails : StepFails (callStep .call evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have hst0 : evm.stack.val = asked :: to ::
      ((if CallKind.call.sendsValue then [0] else []) ++
        inputStart :: inputSize :: outputStart :: 0 :: rest) := hst
  -- the code of the callee
  rcases hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash with
    e | calleeCode
  · exact .inl (fails (callStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
      .ok calleeCode := by rw [hs]; exact hcode
  -- the route: the code itself, or the code of the delegate
  have hroutes : (∃ route, Routes fork state calleeCode route) ∨
      StepFails (callStep .call evm) := by
    by_cases hpectra : .pectra ≤ fork
    · rcases hdel : delegatedAddress calleeCode with _ | d
      · exact .inl ⟨none, fun _ => hdel⟩
      · rcases hd : state.getCode (state.getAccount d).codeHash with e | c'
        · exact .inr (callStep_fails_of_missing (kind := .call) hst0 hcode' hpectra hdel
            (by rw [hs]; exact hd))
        · exact .inl ⟨some (d, c'), hpectra, hdel, hd⟩
    · exact .inl ⟨none, fun h => absurd h hpectra⟩
  rcases hroutes with ⟨route, hroute⟩ | hfail
  · have hroute' : Routes fork evm.state calleeCode route := by rw [hs]; exact hroute
    by_cases hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) route +
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, 0)]).cost ≤ gas
    · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
      · -- the message is sent, along the route
        obtain ⟨after, ⟨caller, msg, child, hsend, hch, -, hat⟩, w, h⟩ :=
          HoareOn.runFrame_of_ok
            (callRoute (callee := Ran runChild) (asked := asked) (inputStart := inputStart)
              (inputSize := inputSize) (outputStart := outputStart) (outputSize := 0)
              (rest := rest) (returnData := evm.returnData) (route := route) hfork hlt hbyte
              hcode hroute hdepth hgas)
            (meetsOk_ran runChild) start.toLogic within hrun
        obtain ⟨-, -, -, -, hreads, -, hcur, htar, -⟩ := CallSends.sentVia hcode hroute hsend
        obtain ⟨-, -, -, -, -, -, -, -, -, -, md, -⟩ := hsend
        rw [hext, hme] at md
        rw [hext, hme] at hat
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := At.ofLogic hat
        exact .inr (.inr ⟨caller, msg, child, after, _, hch, hreads, hcur, htar, md,
          ⟨a1, a2, a3, a4, a5, a6.trans (hw child.output), a7, a8, a9, a10, a11, a12⟩, w, h⟩)
      · -- the depth limit: no message, 0 pushed
        obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
          callStep_deep_of_routes (kind := .call) (route := route) hfork hst0 hcode' hroute'
            (by rw [hm]; omega) (by rw [hmem, hss, hg]; exact hgas)
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        exact .inr (.inl ⟨after.memory, after.gas, after.state, after.substate, after,
          ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, rfl, rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout, rfl, rfl⟩, _, hrun⟩)
    · -- the gas is below the price
      refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := route) hfork hst0
        hcode' hroute' ?_))
      rw [hmem, hss, hg]
      omega
  · exact .inl (fails hfail)

end TokenKit

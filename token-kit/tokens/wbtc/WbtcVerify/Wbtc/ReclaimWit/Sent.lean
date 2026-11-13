import WbtcVerify.Wbtc.Trace
import WbtcVerify.Wbtc.Reclaim.Good

/-!
# The messages that a successful `reclaimToken` sends, at the level of steps

Written by hand (not generated). `ok_reclaim` and `reclaim_two_calls` (Reclaim/) say that a run
of `reclaimToken` that ends with no error ran two messages (`Ran`). They do not say that these
are the ONLY messages that the frame hands to its runner. The run-local conditions of
`Trace.lean` (`CleanFrame`) speak of every message that the frame sends (`Trace.Sent`), so this
file rebuilds the decomposition with the list of sent messages.

What is proved, for every runner and every bound:

- `hoare_sent`: a rule `Logic.Hoare` moves a run of the loop to the frame of its postcondition,
  and every message that the first frame sends is sent by that frame.
- `gas_sent`, `extcodesize_sent`: the same for the opcodes GAS and EXTCODESIZE of a run that
  ends with no error.
- `run_child`: a frame whose step hands a message to the runner, in a run that returns a frame:
  the runner ended the message, the loop went on from the resumed frame, and a message that the
  frame sends is that message or one that the resumed frame sends.
- `callOut_sent`: the form of `callOut_outcome` (CallOut.lean) with the sent messages: at a
  CALL of 0 wei with both ranges inside the memory, the run ends with an error, or no message
  was sent (depth limit), or ONE message was handed to the runner (`SentVia`, `Ran`), and each
  message that the frame at the CALL sends is that one or is sent by the frame after the call.
- `rc_tail1_rule`, `rc_tail2_rule`: the code after each CALL of `reclaimToken`, as rules.
- `reclaim_sent_first`, `reclaim_sent_second`, `reclaim_sent`: a run of `reclaimToken` that ends
  with no error hands EXACTLY two messages to its runner: each message that the frame sends is
  `msg1` from `caller1` or `msg2` from `caller2`, both described by `SentVia` (to the token,
  value 0, the second from the state that the first child left).

Assumed: Berlin ≤ fork < Glamsterdam, call data below 2^256 bytes, one counter of gas, and that
the run ends with no error.
Not covered: the runs of `reclaimToken` that end with an error (the list of their sent messages
is not built here); what the two children do.

Stronger forms of existing lemmas, added here because the existing ones are too weak for
`Trace.Sent`: `callOut_sent` (of `callOut_outcome`: it ties the message to the step of the
frame), `gas_sent` (of `gas_outcome`), `extcodesize_sent` (of `extcodesize_outcome`).
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## Rules move the run and keep the sent messages -/

/-- A rule over the steps moves a run of the loop to the frame of its postcondition, and each
message that the first frame sends is sent by that frame. -/
theorem hoare_sent {P Q : Evm fork Nat → Prop} (h : Logic.Hoare fork P Q) {evm s : Evm fork Nat}
    (hp : P evm) (hrun : EndsL runChild evm s) :
    ∃ z, Q z ∧ EndsL runChild z s ∧
      ∀ (c : Evm fork Nat) (m : Message fork),
        Trace.Sent runChild evm c m → Trace.Sent runChild z c m := by
  obtain ⟨z, hreach, hq⟩ := h evm hp
  obtain ⟨within, hr⟩ := hrun
  have e := runFrame_eq_of_reaches (runChild := runChild) Step.gasHeld_le Step.runFrame_eq
    hreach within
  exact ⟨z, hq, ⟨_, e.symm.trans hr⟩, fun c m hs => Trace.Sent.of_reaches hreach hs⟩

/-- GAS in a run that ends with no error: the run goes on with the gas left pushed, and the
sent messages are those of the next frame. -/
theorem gas_sent {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x5a)
    (hstack : stack.length < STACK_LIMIT) {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ z, At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2) state
        substate z ∧ EndsL runChild z s ∧
      ∀ (c : Evm fork Nat) (m : Message fork),
        Trace.Sent runChild evm c m → Trace.Sent runChild z c m := by
  by_cases hg : 2 ≤ gas
  · exact hoare_sent (At.gas_rule hlt hbyte hg hstack) start hrun
  · obtain ⟨w, hr⟩ := hrun
    exact absurd hok (error_ne_none_of_stepFails start.2.2.2.2.2.2.2.1
      (.inl ⟨_, step_gas_low hlt hbyte (by omega) start⟩) hr)

/-- EXTCODESIZE in a run that ends with no error: the state gave the code of the account, the
run goes on with its size pushed, and the sent messages are those of the next frame. -/
theorem extcodesize_sent {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    (hfork : .berlin ≤ fork) {U : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3b) {evm s : Evm fork Nat}
    (start : At code message pc (U :: rest) memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ (c : ByteArray) (z : Evm fork Nat),
      state.getCode (state.getAccount (toAddressMasked U)).codeHash = .ok c ∧
      At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork (decide (toAddressMasked U ∉ substate.accessedAddresses)))
        (state.recordAccountRead (toAddressMasked U))
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked U) } z ∧
      EndsL runChild z s ∧
      ∀ (c : Evm fork Nat) (m : Message fork),
        Trace.Sent runChild evm c m → Trace.Sent runChild z c m := by
  obtain ⟨w, hr⟩ := hrun
  rcases extcodesize_outcome hfork hlt hbyte start w hr with herr | ⟨c, _, hc, hg, -, -, -⟩
  · exact absurd hok herr
  obtain ⟨z, hz, e, t⟩ := hoare_sent (runChild := runChild)
    (Logic.extcodesize_of_berlin_le hfork hlt hbyte hc rfl hg) start.toLogic ⟨w, hr⟩
  exact ⟨c, z, hc, At.ofLogic hz, e, t⟩

/-! ## A step that hands a message to the runner -/

/-- A frame whose step hands the message `msg` to the runner from `caller`, in a run that
returns a frame: the runner ended the message, and from every frame that the resume gives the
loop goes on to the same end; a message that the frame sends is `msg` from `caller`, or is sent
by the resumed frame. -/
theorem run_child {evm caller s : Evm fork Nat} {msg : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (running : evm.running = true)
    (hstep : step fork evm = .ok (.child caller msg resume))
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    ∃ (lt : msg.gas < bound)
      (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
      runChild caller msg lt = .ok child ∧
      ∀ after, resume child.val = .ok after →
        EndsL runChild after s ∧
        ∀ (c : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c m →
          (c = caller ∧ m = msg) ∨ Trace.Sent runChild after c m := by
  have lt : msg.gas < bound :=
    Nat.lt_of_lt_of_le (step_decreases fork running hstep).1 within
  rcases hran : runChild caller msg lt with e | child
  · rw [runFrame_of_runChild_eq_error running hstep lt hran] at hrun
    cases hrun
  · refine ⟨lt, child, hran, fun after hres => ⟨?_, ?_⟩⟩
    · rw [runFrame_of_step_eq_child running hstep lt hran hres] at hrun
      exact ⟨_, hrun⟩
    · intro c m hs
      rcases Trace.Sent.of_step_child hstep hs with h | ⟨lt2, child2, after2, hr2, hres2, hs2⟩
      · exact .inl h
      · have e1 : child2 = child := Except.ok.inj (hr2.symm.trans hran)
        subst e1
        have e2 : after2 = after := Except.ok.inj (hres2.symm.trans hres)
        subst e2
        exact .inr hs2

/-! ## The CALL, with the sent messages -/

/-- The form of `callOut_outcome` with the sent messages. From Berlin and before Glamsterdam,
for every runner and every bound: a run of the loop from the frame at a CALL of 0 wei whose
input range and output range lie inside the memory, that returns a frame `s`. One of three
holds.

1. `s` has an error.
2. No message was sent (depth limit): the loop went on from the next opcode with 0 pushed.
3. The step of the frame handed the message `msg` to the runner from `caller` (`SentVia`), the
   runner ended it with the frame `child` (`Ran`), the loop went on from the frame `after` at
   the next opcode, with the flag of `child` pushed, the start of its output written, its state
   taken in, and each message that the frame at the CALL sends is `msg` from `caller` or is
   sent by `after`. -/
theorem callOut_sent {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    (hout : outputStart.toNat + outputSize.toNat ≤ memory.size)
    (hrest : rest.length < STACK_LIMIT)
    {evm s : Evm fork Nat}
    (start : At code message pc
      (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ g st ss after,
      Logic.At code message (pc + 1) (0 :: rest) memory g st ss .empty after ∧
      EndsL runChild after s) ∨
    ∃ (caller : Evm fork Nat) (msg : Message fork) (child after : Evm fork Nat) (g : Nat),
      SentVia message state (toAddressMasked to) caller msg ∧
      Ran runChild caller msg child ∧
      Logic.At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite memory outputStart.toNat
          (child.output.extract 0 (min outputSize.toNat child.output.size)))
        g (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        child.output after ∧
      EndsL runChild after s ∧
      ∀ (c : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c m →
        (c = caller ∧ m = msg) ∨ Trace.Sent runChild after c m := by
  have hstep : step fork evm = callStep .call evm := step_at_call start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout', hs, hss⟩ := id start
  have hext := extendMemory_inout (size := memory.size) hin hout
  have hme : memoryExtend memory (ExtendMemory.expandBy ⟨0, 0⟩) = memory :=
    memoryExtend_zero memory
  have fails : StepFails (callStep .call evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have hst0 : evm.stack.val = asked :: to ::
      ((if CallKind.call.sendsValue then [0] else []) ++
        inputStart :: inputSize :: outputStart :: outputSize :: rest) := hst
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
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
          gas
    · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
      · -- the message is sent, along the route
        obtain ⟨caller, msg, hcs, c1, c2, c3, c4, c5, c6, -, c8, c9, c10, hsend⟩ :=
          callStep_child_of_routes (kind := .call) (route := route) hfork hst0 hcode' hroute'
            (by rw [hm]; exact hdepth) (by rw [hmem, hss, hg]; exact hgas)
        rw [← hstep] at hcs
        obtain ⟨lt, child, hran, hafter⟩ := run_child hrunning hcs hrun
        obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, -, a8, a9, a10, a11, a12, a13⟩ :=
          resumeCall_eq (fork := fork) (caller := caller) (child := child.val)
            (o := outputStart) (osz := outputSize) (by rw [c5]; exact hrest)
        obtain ⟨e, t⟩ := hafter after hres
        have hsend2 : CallSends .call message memory gas state substate asked to inputStart
            inputSize outputStart outputSize calleeCode route caller msg := by
          rw [hm, hmem, hg, hs, hss] at hsend
          exact hsend
        have hvia := CallSends.sentVia hcode hroute hsend2
        exact .inr (.inr ⟨caller, msg, child.val, after, after.gas, hvia, ⟨lt, child, hran, rfl⟩,
          ⟨(a1.trans c1).trans hc, (a2.trans c2).trans hj, (a3.trans c3).trans hm,
            by rw [a4, c4, hp], by rw [a5, c5], by rw [a6, c6, hmem, hext, hme], rfl,
            (a8.trans c8).trans hrunning, (a9.trans c9).trans herr, (a10.trans c10).trans hout',
            a11, a12, a13⟩, e, t⟩)
      · -- the depth limit: no message, 0 pushed
        obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
          callStep_deep_of_routes (kind := .call) (route := route) hfork hst0 hcode' hroute'
            (by rw [hm]; omega) (by rw [hmem, hss, hg]; exact hgas)
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        exact .inr (.inl ⟨after.gas, after.state, after.substate, after,
          ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5,
            by rw [a10, hmem, hext, hme], rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout', rfl, rfl, a9⟩, _, hrun⟩)
    · -- the gas is below the price
      refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := route) hfork hst0
        hcode' hroute' ?_))
      rw [hmem, hss, hg]
      omega
  · exact .inl (fails hfail)

/-! ## The code after each CALL of `reclaimToken`, as rules -/

/-- The code after the first CALL (1537..1561), with the flag 1 on top. -/
theorem rc_tail1_rule (hfork : .byzantium ≤ fork) {a b c fp : U256} {rest : List U256}
    {rd mem : ByteArray} {sz gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hs : mem.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT) (hgas : 39 ≤ gas) :
    Logic.HoareG fork
      (Logic.At CODE message 1537 (1 :: a :: b :: c :: rest) mem gas st ss rd)
      (Logic.At CODE message 1562 (BitVec.ofNat 256 rd.size :: fp :: rest) mem (gas - 39) st ss
        rd) :=
  callTail_rule (pc := 1537) (D := (1553 : U256)) hfork (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by decide) (by code_fact)
    (by valid_dest) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) hs hfit hfp hrest hgas

/-- The code after the second CALL (3212..3236), with the flag 1 on top. -/
theorem rc_tail2_rule (hfork : .byzantium ≤ fork) {a b c fp : U256} {rest : List U256}
    {rd mem : ByteArray} {sz gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hs : mem.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT) (hgas : 39 ≤ gas) :
    Logic.HoareG fork
      (Logic.At CODE message 3212 (1 :: a :: b :: c :: rest) mem gas st ss rd)
      (Logic.At CODE message 3237 (BitVec.ofNat 256 rd.size :: fp :: rest) mem (gas - 39) st ss
        rd) :=
  callTail_rule (pc := 3212) (D := (3228 : U256)) hfork (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by decide) (by code_fact)
    (by valid_dest) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) hs hfit hfp hrest hgas

/-! ## From the start to the code after the first call -/

/-- A run of `reclaimToken` that ends with no error, up to the frame `z` after the first call
(pc 1562): the frame handed ONE message to the runner (`msg` from `caller`, to the token), its
child ended with no error, and each message that the first frame sends is that message or is
sent by `z`. -/
theorem reclaim_sent_first (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ (caller : Evm fork Nat) (msg : Message fork) (child : Evm fork Nat) (sel : U256)
      (z : Evm fork Nat),
      SentVia message (rcSt message state (rcToken message)) (rcToken message) caller msg ∧
      Ran runChild caller msg child ∧ child.error = none ∧
      (∃ (g : Nat) (ss : Substate), At CODE message 1562
        [BitVec.ofNat 256 child.output.size, (128 : U256), (0 : U256), rcT message, (570 : U256),
          sel]
        (rcOut (rcMem1 message) child.output) g child.state ss z) ∧
      EndsL runChild z s ∧
      ∀ (c : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c m →
        (c = caller ∧ m = msg) ∨ Trace.Sent runChild z c m := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨hval, hown, hg0, -⟩ := ok_reclaimToken hfork hsize' hsel start hrun hok
  have hsize : 4 ≤ message.data.size := (ends_ok_dispatch hfork hsize' start hrun hok).1
  obtain ⟨z0, hz0, e0, t0⟩ := hoare_sent
    (Logic.HoareG.toHoare (reclaimToken_p2 hfork hsize hsize' hsel hval hown hg0)) start hrun
  have msz := reclaimToken_p2_mem (message := message)
  have hT : toAddressMasked (bitwiseAnd (bitwiseAnd (loadWord message.data 4 32)
      (1461501637330902918203684832716283019655932542975 : U256))
      (1461501637330902918203684832716283019655932542975 : U256)) = rcToken message := by
    rw [and_mask_comm, toAddressMasked_mask]
    rfl
  -- EXTCODESIZE
  obtain ⟨c, z1, hc, hz1, e1, t1⟩ :=
    extcodesize_sent hfork (by code_fact) (by code_fact) hz0 e0 hok
  simp only [hT] at hc hz1
  -- the test of the size
  obtain ⟨hcs, hg2, -⟩ := ok_reclaimCodeA hfork msz.1 msz.2.1 hz1 e1 hok
  obtain ⟨z2, hz2, e2, t2⟩ := hoare_sent
    (Logic.HoareG.toHoare (reclaimCodeA_p1 hfork msz.1 msz.2.1 hcs hg2)) hz1 e1
  -- GAS
  obtain ⟨z3, hz3, e3, t3⟩ :=
    gas_sent (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz2 e2 hok
  obtain ⟨w3, hr3⟩ := e3
  -- CALL
  rcases callOut_sent hfork hglam (by code_fact) (by code_fact)
      (le_size_of msz.1 (by decide)) (le_size_of msz.1 (by decide)) (by simp [STACK_LIMIT])
      hz3 w3 hr3 with
    herr | ⟨g, st, ss, z4, hz4, e4⟩ | ⟨caller, msg, child, z4, g, hvia, hran, hz4, e4, t4⟩
  · exact absurd hok herr
  · exact absurd (rc_tail1 hbyz msz.1 (by decide) msz.2.1 (by simp [STACK_LIMIT]) (.inl rfl)
      hz4 e4 hok).1 (by decide)
  simp only [hT] at hvia
  have hsW := size_rcOut child.output msz.1 (by decide)
  have hfpW := fp_rcOut child.output msz.1 (by decide) msz.2.1
  obtain ⟨hflag, hg5, -⟩ := rc_tail1 hbyz hsW (by decide) hfpW
    (by simp [STACK_LIMIT])
    (by by_cases h : child.error.isNone <;> simp [h]) hz4 e4 hok
  have herr : child.error = none := error_none_of_flag hflag
  rw [hflag] at hz4
  obtain ⟨z5, hz5, e5, t5⟩ := hoare_sent
    (Logic.HoareG.toHoare (rc_tail1_rule hbyz hsW (by decide) hfpW (by simp [STACK_LIMIT]) hg5))
    hz4 e4
  rw [incorporate_state_none herr] at hz5
  exact ⟨caller, msg, child, _, z5, hvia, hran, herr, ⟨_, _, At.ofLogic hz5⟩, e5,
    fun c m hs => (t4 c m (t3 c m (t2 c m (t1 c m (t0 c m hs))))).imp id (t5 c m)⟩

/-! ## From the code after the first call to the end -/

/-- A run from the frame after the first call (pc 1562) that ends with no error: the frame
handed ONE message to the runner (`msg` from `caller`, to the token, from the state of the
frame), and each message that the frame sends is that message. -/
theorem reclaim_sent_second {n t sel bal : U256} {mem : ByteArray} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hmem_size : mem.size = 192)
    (hmem_fp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hmem_w128 : loadWord (memoryReadBytes mem 128 32) 0 32 = bal)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 1562 [n, (128 : U256), (0 : U256), t, (570 : U256), sel] mem gas
      state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ (caller : Evm fork Nat) (msg : Message fork),
      SentVia message (rcSt message state (toAddressMasked t)) (toAddressMasked t) caller msg ∧
      ∀ (c : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c m →
        c = caller ∧ m = msg := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨hn, hg0, -⟩ := ok_reclaimMid hfork hmem_size hmem_fp hmem_w128 start hrun hok
  obtain ⟨z0, hz0, e0, t0⟩ := hoare_sent
    (Logic.HoareG.toHoare (reclaimMid_p1 hfork hmem_size hmem_fp hmem_w128 hn hg0)) start hrun
  have msz := reclaimMid_p1_mem (message := message) (state := state) (n := n) (t := t)
    (sel := sel) hmem_size hmem_fp hmem_w128
  -- EXTCODESIZE
  obtain ⟨c, z1, hc, hz1, e1, t1⟩ :=
    extcodesize_sent hfork (by code_fact) (by code_fact) hz0 e0 hok
  simp only [toAddressMasked_mask] at hc hz1
  -- the test of the size
  obtain ⟨hcs, hg2, -⟩ := ok_reclaimCodeB hfork msz.1 msz.2.1 hz1 e1 hok
  obtain ⟨z2, hz2, e2, t2⟩ := hoare_sent
    (Logic.HoareG.toHoare (reclaimCodeB_p1 hfork msz.1 msz.2.1 hcs hg2)) hz1 e1
  -- GAS
  obtain ⟨z3, hz3, e3, t3⟩ :=
    gas_sent (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz2 e2 hok
  obtain ⟨w3, hr3⟩ := e3
  -- CALL
  rcases callOut_sent hfork hglam (by code_fact) (by code_fact)
      (le_size_of msz.1 (by decide)) (le_size_of msz.1 (by decide)) (by simp [STACK_LIMIT])
      hz3 w3 hr3 with
    herr | ⟨g, st, ss, z4, hz4, e4⟩ | ⟨caller, msg, child, z4, g, hvia, hran, hz4, e4, t4⟩
  · exact absurd hok herr
  · exact absurd (rc_tail2 hbyz msz.1 (by decide) msz.2.1 (by simp [STACK_LIMIT]) (.inl rfl)
      hz4 e4 hok).1 (by decide)
  simp only [toAddressMasked_mask] at hvia
  have hsW := size_rcOut child.output msz.1 (by decide)
  have hfpW := fp_rcOut child.output msz.1 (by decide) msz.2.1
  obtain ⟨hflag, hg5, -⟩ := rc_tail2 hbyz hsW (by decide) hfpW
    (by simp [STACK_LIMIT])
    (by by_cases h : child.error.isNone <;> simp [h]) hz4 e4 hok
  rw [hflag] at hz4
  obtain ⟨z5, hz5, e5, t5⟩ := hoare_sent
    (Logic.HoareG.toHoare (rc_tail2_rule hbyz hsW (by decide) hfpW (by simp [STACK_LIMIT]) hg5))
    hz4 e4
  have hz6 := At.ofLogic hz5
  -- the end: no message
  obtain ⟨hn2, hret, hg6, -⟩ := ok_reclaimEnd hfork hsW hfpW rfl hz6 e5 hok
  have nos := Trace.not_sent_of_specG (reclaimEnd_p2 hfork hsW hfpW rfl hn2 hret hg6) hz6
    runChild
  refine ⟨caller, msg, hvia, fun c m hs => ?_⟩
  rcases t4 c m (t3 c m (t2 c m (t1 c m (t0 c m hs)))) with h | h
  · exact h
  · exact absurd (t5 c m h) (nos c m)

/-! ## The whole function -/

/-- THE MESSAGES OF A SUCCESSFUL `reclaimToken`, for every runner. A run that ends with no
error hands exactly two messages to its runner: each message that the frame sends
(`Trace.Sent`) is `msg1` from `caller1` or `msg2` from `caller2`. Both go to the token with
value 0 (`SentVia`): the first from the state before the call (with two reads recorded), the
second from the state that the child of the first left. -/
theorem reclaim_sent (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ∃ (caller1 : Evm fork Nat) (msg1 : Message fork) (child1 : Evm fork Nat)
      (caller2 : Evm fork Nat) (msg2 : Message fork),
      SentVia message (rcSt message state (rcToken message)) (rcToken message) caller1 msg1 ∧
      Ran runChild caller1 msg1 child1 ∧ child1.error = none ∧
      SentVia message (rcSt message child1.state (rcToken message)) (rcToken message) caller2
        msg2 ∧
      ∀ (c : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c m →
        (c = caller1 ∧ m = msg1) ∨ (c = caller2 ∧ m = msg2) := by
  obtain ⟨caller1, msg1, child1, sel, z, hvia1, hran1, herr1, ⟨g, ss, hz⟩, ez, t1⟩ :=
    reclaim_sent_first hfork hglam hsize' hsel start hrun hok
  have msz := reclaimToken_p2_mem (message := message)
  have hsW : (rcOut (rcMem1 message) child1.output).size = 192 :=
    size_rcOut child1.output msz.1 (by decide)
  have hfpW : loadWord (memoryReadBytes (rcOut (rcMem1 message) child1.output) 64 32) 0 32 =
      (128 : U256) := fp_rcOut child1.output msz.1 (by decide) msz.2.1
  obtain ⟨caller2, msg2, hvia2, t2⟩ := reclaim_sent_second hfork hglam hsW hfpW rfl hz ez hok
  exact ⟨caller1, msg1, child1, caller2, msg2, hvia1, hran1, herr1, hvia2,
    fun c m hs => (t1 c m hs).imp id (t2 c m)⟩

end WbtcVerify

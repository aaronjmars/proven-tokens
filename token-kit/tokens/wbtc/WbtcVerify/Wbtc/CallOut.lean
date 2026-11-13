import TokenKit.Evm.Tail
import TokenKit.Evm.Precompile
import TokenKit.Evm.CallOutcome
import EthLib.Execution.Proofs.Evm.Logic.Route
import EthLib.Execution.Proofs.Evm.Logic.Keeps

/-!
# A CALL with no value whose input and output ranges lie inside memory, and the code after it

`CallIn.lean` covers a CALL of 0 wei with an output range of size 0. The code that solc 0.4 emits
for `token.balanceOf(this)` and `token.transfer(to, value)` asks for 32 bytes of output, written
over the start of the input. This file gives the rules for that shape. Nothing here is about one
token.

What is proved:

- `extendMemory_inout`: two ranges inside the memory grow nothing and cost nothing.
- `size_callWrite`, `read_callWrite_other`, `load_callWrite_word`: the memory after the write of
  the start of the output of the child: same size, same bytes outside the output range, and,
  when the child returned at least 32 bytes to an output range of 32 bytes, the first word of
  its output at the start of the range.
- `callOut_outcome`: every outcome of a run of the interpreter loop from the frame at
  `CALL(asked, to, 0, inputStart, inputSize, outputStart, outputSize)`, for ANY callee (its code
  may be an EIP-7702 delegation): (1) the run ends with an error; (2) no message was sent (depth
  limit), 0 was pushed, the memory is as before and the return data is empty; (3) the runner ran
  one message. In case (3) the lemma gives `Ran`, EthLib's `SentVia` (the state of the frame
  handed to the runner reads as the state before the call, the message goes to the address of
  `to` with value 0, and its code is the code that the state holds for the address the call
  resolves to), the exact data of the message (the bytes of the input range), its exact gas, the
  memory after (the first `min outputSize (size of the output)` bytes of the output of the child
  written at the output start), the return data of the frame (the output of the child) and the
  exact gas after the call.
- `ends_step`: a rule over `Logic.StepG`, held for every gas from `c` on, moves a run that ends
  with no error, with the exact gas (and the run had at least `c` gas).
- `callTail_rule`, `callTail_ok`: the code that solc 0.4 puts after an outside call,
  `ISZERO DUP1 ISZERO PUSH2 dest JUMPI <bubble> JUMPDEST POP POP POP POP PUSH1 0x40 MLOAD
  RETURNDATASIZE`. A run from the opcode after the CALL that ends with no error had the flag 1
  (a flag 0 goes to the bubble that reverts with the return data, by the kit's `bubble_no_ok`),
  paid 39 gas, and went on with the size of the return data and the free memory pointer pushed.

Assumed: the fork is from Berlin and before Glamsterdam (`callOut_outcome`), from Byzantium
(the tail); one counter of gas; value 0; both ranges inside the memory (`hin`, `hout`).

Not covered: a value that is not 0; a range that ends past the memory; Glamsterdam and later;
what the child does (the rules hold for every frame that the runner gives).
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
  {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## The growth of memory and the write of the output -/

/-- Two ranges inside a memory of `size` bytes grow nothing and cost nothing. -/
theorem extendMemory_inout {size : Nat} {inputStart inputSize outputStart outputSize : U256}
    (hin : inputStart.toNat + inputSize.toNat ≤ size)
    (hout : outputStart.toNat + outputSize.toNat ≤ size) :
    extendMemory size [(inputStart, inputSize), (outputStart, outputSize)] = ⟨0, 0⟩ :=
  extendMemory_two hin hout

/-- The write of the start of the output of a child to an output range inside the memory keeps
the size of the memory. -/
theorem size_callWrite {m : ByteArray} (out : ByteArray) {o n : Nat} (hfit : o + n ≤ m.size) :
    (memoryWrite m o (out.extract 0 (min n out.size))).size = m.size :=
  size_memoryWrite (by rw [ByteArray.size_extract]; omega)

/-- The write of the start of the output of a child keeps the bytes outside the output range. -/
theorem read_callWrite_other {m : ByteArray} (out : ByteArray) {o n a k : Nat}
    (hfit : o + n ≤ m.size) (hd : a + k ≤ o ∨ o + n ≤ a) :
    memoryReadBytes (memoryWrite m o (out.extract 0 (min n out.size))) a k =
      memoryReadBytes m a k :=
  memoryReadBytes_memoryWrite_of_disjoint (by rw [ByteArray.size_extract]; omega)
    (by rw [ByteArray.size_extract]; omega)

/-- An output range of 32 bytes inside the memory and a child that returned at least 32 bytes:
the word at the start of the range is the first word of the output. -/
theorem load_callWrite_word {m : ByteArray} (out : ByteArray) {o : Nat}
    (hfit : o + 32 ≤ m.size) (hout : 32 ≤ out.size) :
    loadWord (memoryReadBytes (memoryWrite m o (out.extract 0 (min 32 out.size))) o 32) 0 32 =
      loadWord (memoryReadBytes out 0 32) 0 32 := by
  have hmin : min 32 out.size = 32 := Nat.min_eq_left hout
  have hr : out.extract 0 (min 32 out.size) = memoryReadBytes out 0 32 := by
    rw [hmin]
    simp [memoryReadBytes]
  have key := loadWord_memoryWrite_wordBytes (memory := m) (start := o)
    (loadWord (memoryReadBytes out 0 32) 0 32) hfit
  rw [wordBytes_loadWord (size_memoryReadBytes (by omega))] at key
  rw [hr]
  exact key

/-! ## Every outcome of the CALL, for any callee -/

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a CALL of 0 wei whose input range and output range lie inside
the memory, that returns a frame `s`. No assumption on the code of the callee, which may be an
EIP-7702 delegation. One of three holds.

1. `s` has an error (the state fails to give the code of the callee or of its delegate, or the
   gas is below the price of the call).
2. No message was sent (depth limit): the loop went on from the next opcode with 0 pushed, the
   memory as it was, no return data and at most the gas of before.
3. The runner ran the message `msg` from the frame `caller` to a frame `child`. `SentVia` says
   that the state of `caller` reads as the state before the call, that the message goes to the
   address of `to` with value 0 and that its code is the code the state holds for the address
   the call resolves to (`routeCode calleeCode route`). The data of the message are the bytes of
   the input range and its gas is the `subCall` part of the 63/64 rule. The loop went on from
   the next opcode with the flag of `child` pushed, the start of its output written to the
   output range, its output as return data, the exact gas, and its state taken in. -/
theorem callOut_outcome (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    (hout : outputStart.toNat + outputSize.toNat ≤ memory.size)
    {evm s : Evm fork Nat}
    (start : At code message pc
      (asked :: to :: 0 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ g st ss after,
      Logic.At code message (pc + 1) (0 :: rest) memory g st ss .empty after ∧ g ≤ gas ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s) ∨
    ∃ calleeCode route caller msg child after,
      state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode ∧
      Routes fork state calleeCode route ∧
      SentVia message state (toAddressMasked to) caller msg ∧
      caller.substate = routeSub { substate with
        accessedAddresses := substate.accessedAddresses.insert (toAddressMasked to) } route ∧
      msg.data = memoryReadBytes memory inputStart.toNat inputSize.toNat ∧
      msg.gas = (messageCallGas fork 0 asked.toNat gas 0
        (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
          routeCost fork (substate.accessedAddresses.insert (toAddressMasked to))
            route)).subCall ∧
      Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
      Logic.At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite memory outputStart.toNat
          (child.output.extract 0 (min outputSize.toNat child.output.size)))
        (gas - (messageCallGas fork 0 asked.toNat gas 0
          (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
            routeCost fork (substate.accessedAddresses.insert (toAddressMasked to))
              route)).cost + child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        child.output after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
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
        obtain ⟨after, ⟨caller, msg, child, hsend, hch, hle, hat⟩, w, h⟩ :=
          HoareOn.runFrame_of_ok
            (callRoute (callee := Ran runChild) (asked := asked) (inputStart := inputStart)
              (inputSize := inputSize) (outputStart := outputStart) (outputSize := outputSize)
              (rest := rest) (returnData := evm.returnData) (route := route) hfork hlt hbyte
              hcode hroute hdepth hgas)
            (meetsOk_ran runChild) start.toLogic within hrun
        have hvia := CallSends.sentVia hcode hroute hsend
        obtain ⟨-, css, mg, -, -, -, -, -, -, -, md, -⟩ := id hsend
        rw [hext, hme] at md
        rw [hext] at mg
        rw [hext, hme] at hat
        exact .inr (.inr ⟨calleeCode, route, caller, msg, child, after, rfl, hroute, hvia, css,
          md, mg, hch, hle, hat, w, h⟩)
      · -- the depth limit: no message, 0 pushed
        obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
          callStep_deep_of_routes (kind := .call) (route := route) hfork hst0 hcode' hroute'
            (by rw [hm]; omega) (by rw [hmem, hss, hg]; exact hgas)
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        refine .inr (.inl ⟨after.gas, after.state, after.substate, after,
          ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5,
            by rw [a10, hmem, hext, hme], rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout', rfl, rfl, a9⟩, ?_, _, hrun⟩)
        rw [a11, hg]
        exact Nat.sub_le _ _
    · -- the gas is below the price
      refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := route) hfork hst0
        hcode' hroute' ?_))
      rw [hmem, hss, hg]
      omega
  · exact .inl (fails hfail)

/-! ## Steps after the call, with the exact gas -/

/-- A rule over `Logic.StepG`, held for every gas from `c` on, moves a run that ends with no
error: the run had at least `c` gas and goes through the frame of the postcondition with exactly
`c` less. -/
theorem ends_step {c pcr : Nat} {stack stack' : List U256} {memory' : ByteArray}
    {state' : State.TransactionState} {substate' : Substate} {rd rd' : ByteArray}
    {l s : Evm fork Nat}
    (h0 : Logic.At code message pc stack memory gas state substate rd l)
    (e : EndsL runChild l s) (hok : s.error = none)
    (rule : ∀ G, c ≤ G →
      Logic.HoareG fork (Logic.At code message pc stack memory G state substate rd)
        (Logic.At code message pcr stack' memory' (G - c) state' substate' rd')) :
    c ≤ gas ∧ ∃ l', Logic.At code message pcr stack' memory' (gas - c) state' substate' rd' l' ∧
      EndsL runChild l' s := by
  obtain ⟨within, hr⟩ := e
  obtain ⟨z, hreach, hz⟩ := rule (gas + c) (by omega) _ (h0.addGas c)
  obtain ⟨l', w, rfl, e'⟩ := reaches_low hreach c l rfl within hr hok
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hz
  have h7' : l'.gas + c = gas + c - c := h7
  exact ⟨by omega, l', ⟨h1, h2, h3, h4, h5, h6, by omega, h8, h9, h10, h11, h12, h13⟩, w, e'⟩

/-- The code after an outside call that succeeded, as solc 0.4 emits it:
`ISZERO DUP1 ISZERO PUSH2 dest JUMPI`, 9 bytes of bubble, then at `dest = pc + 16`
`JUMPDEST POP POP POP POP PUSH1 0x40 MLOAD RETURNDATASIZE`. With the flag 1 on top it drops the
flag and three more words, and pushes the free memory pointer and the size of the return data,
for 39 gas. Memory, state, substate and return data stay. -/
theorem callTail_rule (hfork : .byzantium ≤ fork) {a b c fp D : U256} {rest : List U256}
    {rd : ByteArray} {sz : Nat}
    (hlt : pc + 24 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (hD : pushData code (pc + 3) 2 = D) (hDn : D.toNat = pc + 16)
    (b6 : code[pc + 6]'(by omega) = 0x57)
    (valid : isValidJumpDest (validJumpDestinations code) (pc + 16) = true)
    (b16 : code[pc + 16]'(by omega) = 0x5b) (b17 : code[pc + 17]'(by omega) = 0x50)
    (b18 : code[pc + 18]'(by omega) = 0x50) (b19 : code[pc + 19]'(by omega) = 0x50)
    (b20 : code[pc + 20]'(by omega) = 0x50) (b21 : code[pc + 21]'(by omega) = 0x60)
    (b22 : code[pc + 22]'(by omega) = 0x40) (b23 : code[pc + 23]'(by omega) = 0x51)
    (b24 : code[pc + 24]'(by omega) = 0x3d)
    (hs : memory.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes memory 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT) (hgas : 39 ≤ gas) :
    Logic.HoareG fork
      (Logic.At code message pc (1 :: a :: b :: c :: rest) memory gas state substate rd)
      (Logic.At code message (pc + 25) (BitVec.ofNat 256 rd.size :: fp :: rest) memory
        (gas - 39) state substate rd) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : U256, BitVec.ofNat 256 (0x40 : UInt8).toNat = Z := ⟨_, rfl⟩
  have hZ64 : Z.toNat = 64 := by rw [← hZ]; rfl
  have hz1 : isZero (0 : U256) = 1 := by decide
  have hz2 : isZero (1 : U256) = 0 := by decide
  have hlim : STACK_LIMIT = 1024 := rfl
  rw [hlim] at hrest
  have e : gas - 39 = gas - 3 - 3 - 3 - 3 - 10 - 1 - 2 - 2 - 2 - 2 - 3 - 3 - 2 := by omega
  rw [e]
  -- ISZERO
  refine Triple.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b0
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz2]
  -- DUP1
  refine Triple.seq (Logic.dup1G (by omega) b1 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- ISZERO
  refine Triple.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b2
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz1]
  -- PUSH2
  refine Triple.seq (Logic.pushG (n := 2) (by decide) (by omega)
    (by rw [b3]; decide) (by decide) hD (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- JUMPI, taken
  refine Triple.seq (Logic.jumpi_takenG (pc := pc + 6) (by omega) b6 (by omega) (by decide)
    (by rw [hDn]; exact valid)) ?_
  rw [hDn]
  -- JUMPDEST
  refine Triple.seq (Logic.jumpdestG (pc := pc + 16) (by omega) b16 (by omega)) ?_
  -- POP, four times
  refine Triple.seq (Logic.popG (pc := pc + 17) (by omega) b17 (by omega)) ?_
  refine Triple.seq (Logic.popG (pc := pc + 18) (by omega) b18 (by omega)) ?_
  refine Triple.seq (Logic.popG (pc := pc + 19) (by omega) b19 (by omega)) ?_
  refine Triple.seq (Logic.popG (pc := pc + 20) (by omega) b20 (by omega)) ?_
  -- PUSH1 0x40
  refine Triple.seq (Logic.push1G (pc := pc + 21) (by omega) b21 b22 (by omega)
    (by rw [hlim]; omega)) ?_
  rw [hZ]
  -- MLOAD
  refine Triple.seq (mloadInG (pc := pc + 23) hs (by rw [hZ64]; omega) (by omega) b23
    (by omega)) ?_
  rw [hZ64, hfp]
  -- RETURNDATASIZE
  exact Logic.returndatasizeG (pc := pc + 24) hfork (by omega) b24 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)

/-- A run from the opcode after an outside call (the code of `callTail_rule`, with the bubble
`RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY RETURNDATASIZE PUSH1 0 REVERT` in between) that
ends with no error: the flag was 1, the run had 39 gas, and it went on after the
RETURNDATASIZE with the size of the return data and the free memory pointer pushed. The frame
keeps the return data. -/
theorem callTail_ok (hfork : .byzantium ≤ fork) {flag a b c fp D : U256} {rest : List U256}
    {rd : ByteArray} {sz : Nat}
    (hlt : pc + 24 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (hD : pushData code (pc + 3) 2 = D) (hDn : D.toNat = pc + 16)
    (b6 : code[pc + 6]'(by omega) = 0x57) (b7 : code[pc + 7]'(by omega) = 0x3d)
    (b8 : code[pc + 8]'(by omega) = 0x60) (b9 : code[pc + 9]'(by omega) = 0x00)
    (b10 : code[pc + 10]'(by omega) = 0x80) (b11 : code[pc + 11]'(by omega) = 0x3e)
    (b12 : code[pc + 12]'(by omega) = 0x3d) (b13 : code[pc + 13]'(by omega) = 0x60)
    (b14 : code[pc + 14]'(by omega) = 0x00) (b15 : code[pc + 15]'(by omega) = 0xfd)
    (valid : isValidJumpDest (validJumpDestinations code) (pc + 16) = true)
    (b16 : code[pc + 16]'(by omega) = 0x5b) (b17 : code[pc + 17]'(by omega) = 0x50)
    (b18 : code[pc + 18]'(by omega) = 0x50) (b19 : code[pc + 19]'(by omega) = 0x50)
    (b20 : code[pc + 20]'(by omega) = 0x50) (b21 : code[pc + 21]'(by omega) = 0x60)
    (b22 : code[pc + 22]'(by omega) = 0x40) (b23 : code[pc + 23]'(by omega) = 0x51)
    (b24 : code[pc + 24]'(by omega) = 0x3d)
    (hs : memory.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes memory 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT)
    (hflag : flag = 0 ∨ flag = 1)
    {l s : Evm fork Nat}
    (start : Logic.At code message pc (flag :: a :: b :: c :: rest) memory gas state substate
      rd l)
    (e : EndsL runChild l s) (hok : s.error = none) :
    flag = 1 ∧ 39 ≤ gas ∧
    ∃ z, At code message (pc + 25) (BitVec.ofNat 256 rd.size :: fp :: rest) memory (gas - 39)
        state substate z ∧ z.returnData = rd ∧ EndsL runChild z s := by
  rcases hflag with rfl | rfl
  · obtain ⟨within, hr⟩ := e
    exact absurd hok (bubble_no_ok hfork (by omega) b0 b1 b2 b3 b6 b7 b8 b9 b10 b11 b12 b13 b14
      b15 (by simp only [List.length_cons]; omega) start within hr)
  · obtain ⟨hg, z, hz, ez⟩ := ends_step start e hok fun G hG =>
      callTail_rule hfork hlt b0 b1 b2 b3 hD hDn b6 valid b16 b17 b18 b19 b20 b21 b22 b23 b24
        hs hfit hfp hrest hG
    exact ⟨rfl, hg, z, At.ofLogic hz, hz.2.2.2.2.2.2.2.2.2.2.2.2, ez⟩

end TokenKit

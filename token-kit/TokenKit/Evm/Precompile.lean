import TokenKit.Evm.CallOutcome
import TokenKit.Evm.Payee
import TokenKit.Evm.RawMem
import EthLib.Execution.Proofs.Evm.Logic.Copy
import EthLib.Execution.Proofs.Evm.Logic.Route
import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# STATICCALL to a precompile, and the ECRECOVER call of Solidity

A token with `permit` calls the precompile at address 1 (ECRECOVER) with STATICCALL. This file
says what that call does under EthLib's real runner (`processRunner`), with no assumption on
what the precompile returns: the output is EthLib's own `Precompiles.Ecrecover.compute` on the
bytes of the input range.

- `gas_outcome`: a run from a frame at GAS has an error or goes on with the gas left pushed.
- `staticcallStep_missing`, `staticcall_outcome`: every outcome of a run from a frame at a
  STATICCALL, for ANY runner: an error; no message and 0 pushed (depth limit); or the runner ran
  the message of `CallSends` and the loop went on with the flag of the child pushed, its output
  written to the output range and kept as return data.
- `returndatacopyG`, `bubble_no_ok`: the code that Solidity puts after a call of a precompile
  (`ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY
  RETURNDATASIZE PUSH1 0 REVERT`), from a frame with the flag 0: no run ends with no error.
- `processMessage_precompile`, `runPrecompile_ecrecover`, `ecrecover_ran`: `processRunner` on a
  message to the precompile at address 1 with no value: with less than 3000 gas the frame of the
  message has an error; otherwise it has no error, the state it started from, no log, the output
  `Ecrecover.compute` of its data, and 3000 gas less.
- `incorporateChild_precompile`: from Paris, the caller has its own substate back.
- `ecrecover_call_ok`: the join. From Paris and before Glamsterdam, a run of the real runner
  from the frame at `GAS STATICCALL` to address 1 followed by the code above, that ends with no
  error: the call was made, it succeeded, and the loop went on from the opcode after STATICCALL
  with 1 pushed, the output of `Ecrecover.compute` written to the output range, the state and
  the logs as before (address 1 is now accessed), and the exact gas.
- `extendMemory_two`, `size_ecrecover_write`, `read_ecrecover_other`: the memory around the
  output range.
- `recoveredWord`, `load_ecrecover`: the word that the caller reads from an output range of 32
  bytes that held 0 before the call: the 32 bytes of the output, or 0 for an empty output.

Scope: `hdel` (the account at address 1 holds no EIP-7702 delegation code; a state fact, true
on chain since precompile accounts hold no code). Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## GAS -/

/-- A run of the loop from a frame at GAS that returns a frame `s`: `s` has an error (less than
2 gas), or the loop went on from the next opcode with the gas left pushed. -/
theorem gas_outcome {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x5a)
    (hstack : stack.length < STACK_LIMIT)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    ∃ after, At code message (pc + 1) (BitVec.ofNat 256 (gas - 2) :: stack) memory (gas - 2)
        state substate after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  by_cases hg : 2 ≤ gas
  · exact .inr (Hoare.runFrame_of_ok (At.gas_rule hlt hbyte hg hstack) start within hrun)
  · exact .inl (error_ne_none_of_stepFails start.2.2.2.2.2.2.2.1
      (.inl ⟨_, UsdtVerify.Complete.step_gas_low hlt hbyte (by omega) start⟩) hrun)

/-! ## STATICCALL -/

/-- Before Glamsterdam, a STATICCALL to an address whose code the state fails to give: the step
fails. -/
theorem staticcallStep_missing (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {e : State.StateError}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest)
    (hmissing : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .error e) :
    StepFails (callStep .staticcall evm) := by
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

/-- The step of a frame at a STATICCALL is the step of the static call. -/
theorem step_at_staticcall (hfork : .berlin ≤ fork) {stack : List U256} {rd : ByteArray}
    {evm : Evm fork Nat}
    (start : Logic.At code message pc stack memory gas state substate rd evm)
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfa) :
    step fork evm = callStep .staticcall evm := by
  obtain ⟨hc, -, -, hp, -⟩ := start
  subst hc hp
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  have hdec : Op.ofByte fork evm.code[evm.pc] = some .staticcall := by
    rw [hbyte]
    exact ofByte_of_decode (op := .staticcall) rfl hbyz
  exact step_of_messageInstruction hlt hdec
    instruction_staticcall (messageInstruction_staticcall (Nat.le_trans (by decide) hfork))

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a STATICCALL that returns a frame `s`. One of three holds.

1. `s` has an error (the state fails to give the code of the callee, or the gas is below the
   price of the call).
2. No message was sent (depth limit): the loop went on from the next opcode with 0 pushed.
3. The runner ran the message of `CallSends` to a frame `child`, and the loop went on from the
   next opcode with the flag of `child` pushed, the start of its output written to the output
   range, its output as return data, its gas given back, and its state taken in.

`hdel`: the code of the callee is no EIP-7702 delegation (from Pectra). -/
theorem staticcall_outcome (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {rd : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : Logic.At code message pc
      (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ mem g st ss rd' after, Logic.At code message (pc + 1) (0 :: rest) mem g st ss rd' after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s) ∨
    ∃ calleeCode caller msg child after,
      CallSends .staticcall message memory gas state substate asked to inputStart inputSize
        outputStart outputSize calleeCode none caller msg ∧
      Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
      Logic.At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
        (gas - ((messageCallGas fork 0 asked.toNat gas
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
            routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) none)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          child.gas)
        (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        child.output after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .staticcall evm := step_at_staticcall hfork start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss, hrd⟩ := id start
  have fails : StepFails (callStep .staticcall evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have hst0 : evm.stack.val = asked :: to ::
      ((if CallKind.staticcall.sendsValue then [0] else []) ++
        inputStart :: inputSize :: outputStart :: outputSize :: rest) := hst
  have hcases : (∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash =
        .error e) ∨
      ∃ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c := by
    cases state.getCode (state.getAccount (toAddressMasked to)).codeHash with
    | error e => exact .inl ⟨e, rfl⟩
    | ok c => exact .inr ⟨c, rfl⟩
  rcases hcases with ⟨e, hcode⟩ | ⟨calleeCode, hcode⟩
  · exact .inl (fails (staticcallStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  · have hroute : Routes fork state calleeCode none := hdel calleeCode hcode
    have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
        .ok calleeCode := by rw [hs]; exact hcode
    have hroute' : Routes fork evm.state calleeCode none := hdel calleeCode hcode
    by_cases hgas : callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
        routeCost fork (substate.accessedAddresses.insert (toAddressMasked to)) none +
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost ≤
          gas
    · by_cases hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT
      · obtain ⟨after, ⟨caller, msg, child, hsend, hch, hle, hat⟩, w, h⟩ :=
          HoareOn.runFrame_of_ok
            (callKindRoute (kind := .staticcall) (callee := Ran runChild) (asked := asked)
              (inputStart := inputStart) (inputSize := inputSize) (outputStart := outputStart)
              (outputSize := outputSize) (rest := rest) (returnData := rd) (route := none)
              hfork hlt hbyte
              (ofByte_of_decode (op := .staticcall) rfl (Nat.le_trans (by decide) hfork))
              instruction_staticcall
              (messageInstruction_staticcall (Nat.le_trans (by decide) hfork))
              hcode hroute hdepth hgas)
            (meetsOk_ran runChild) start within hrun
        exact .inr (.inr ⟨calleeCode, caller, msg, child, after, hsend, hch, hle, hat, w, h⟩)
      · obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, -⟩ :=
          callStep_deep_of_routes (kind := .staticcall) (route := none) hfork hst0 hcode' hroute'
            (by rw [hm]; omega) (by rw [hmem, hss, hg]; exact hgas)
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        exact .inr (.inl ⟨after.memory, after.gas, after.state, after.substate, after.returnData,
          after, ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, rfl, rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout, rfl, rfl, rfl⟩, _, hrun⟩)
    · refine .inl (fails (callStep_fails_of_routes (kind := .staticcall) (route := none) hfork
        hst0 hcode' hroute' ?_))
      rw [hmem, hss, hg]
      omega

/-! ## The code after a call that failed -/

/-- From Byzantium, RETURNDATACOPY of a range inside the return data, over the steps that are
monotone in gas. -/
theorem returndatacopyG (hfork : .byzantium ≤ fork) {start offset size : U256}
    {rest : List U256} {returnData : ByteArray} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x3e) (fit : offset.toNat + size.toNat ≤ returnData.size)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Logic.HoareG fork
      (Logic.At code message pc (start :: offset :: size :: rest) memory gas state substate
        returnData)
      (Logic.At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat (memoryReadBytes returnData offset.toNat size.toNat))
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) := by
  refine Logic.At.ruleG_of_follows hlt hbyte
    (ofByte_of_decode (op := .returndatacopy) rfl hfork) instruction_returndatacopy ?_ ?_
  · rintro evm ⟨-, -, -, -, hst, -, -, -, -, -, -, -, hrd⟩ k low rfl
    have hst' : low.stack.val = start :: offset :: size :: rest := hst
    have hrd' : low.returnData = returnData := hrd
    have fit' : offset.toNat + size.toNat ≤ low.returnData.size := by rw [hrd']; exact fit
    rw [returndatacopyStep_cons hst' fit',
      returndatacopyStep_cons (evm := addGas k low) hst' fit']
    exact follows_map_charge fun _ => rfl
  · rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
    have hcost : OPCODE_RETURNDATACOPY_BASE = 3 := rfl
    have hword : OPCODE_RETURNDATACOPY_PER_WORD = 3 := rfl
    have ok := returndatacopyStep_cons hst (by rw [hrd]; exact fit)
    rw [hrd] at ok
    dsimp only at ok
    rw [hcost, hword, hmem, hg, charge_nat hgas] at ok
    exact ⟨_, ok, ⟨hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, rfl⟩⟩

/-- The code that Solidity puts after a call whose failure it passes on:
`ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY RETURNDATASIZE
PUSH1 0 REVERT`. From a frame with the flag 0 on top (the call failed), no run of the loop
returns a frame with no error: with enough gas it reverts with the return data, with less it
runs out of gas. For every runner. -/
theorem bubble_no_ok (hfork : .byzantium ≤ fork) {rest : List U256} {rd : ByteArray}
    (hlt : pc + 15 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (b6 : code[pc + 6]'(by omega) = 0x57) (b7 : code[pc + 7]'(by omega) = 0x3d)
    (b8 : code[pc + 8]'(by omega) = 0x60) (b9 : code[pc + 9]'(by omega) = 0x00)
    (b10 : code[pc + 10]'(by omega) = 0x80) (b11 : code[pc + 11]'(by omega) = 0x3e)
    (b12 : code[pc + 12]'(by omega) = 0x3d) (b13 : code[pc + 13]'(by omega) = 0x60)
    (b14 : code[pc + 14]'(by omega) = 0x00) (b15 : code[pc + 15]'(by omega) = 0xfd)
    (hrest : rest.length + 4 < STACK_LIMIT)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : Logic.At code message pc (0 :: rest) memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  obtain ⟨Z, hZ⟩ : ∃ Z : U256, BitVec.ofNat 256 (0x00 : UInt8).toNat = Z := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : U256, BitVec.ofNat 256 rd.size = N := ⟨_, rfl⟩
  have hZ0 : Z.toNat = 0 := by rw [← hZ]; rfl
  have hNle : N.toNat ≤ rd.size := by
    rw [← hN, BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  have hz1 : isZero (0 : U256) = 1 := by decide
  have hz2 : isZero (1 : U256) = 0 := by decide
  have hlim : STACK_LIMIT = 1024 := rfl
  rw [hlim] at hrest
  refine no_ok_of_specG
    (B := 3 * wordCount N.toNat + (extendMemory memory.size [(Z, N)]).cost +
      (extendMemory (memoryWrite (memoryExtend memory
        (extendMemory memory.size [(Z, N)]).expandBy) Z.toNat
        (memoryReadBytes rd Z.toNat N.toNat)).size [(Z, N)]).cost + 40)
    (Q := fun _ evm => evm.error ≠ none) (fun g hg => ?_) (fun _ _ h => h) start within hrun
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b0
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz1]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (by omega) b1 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b2
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz2]
  -- PUSH2
  refine Logic.SpecG.seq (Logic.pushG (n := 2) (by decide) (by omega)
    (by rw [b3]; decide) (by decide) rfl (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- JUMPI, not taken
  refine Logic.SpecG.seq (Logic.jumpi_zeroG (pc := pc + 6) (by omega) b6 (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 7) hfork (by omega) b7 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH1 0
  refine Logic.SpecG.seq (Logic.push1G (pc := pc + 8) (by omega) b8 b9 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hZ]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (pc := pc + 10) (by omega) b10 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- RETURNDATACOPY
  refine Logic.SpecG.seq (returndatacopyG (pc := pc + 11) hfork (by omega) b11
    (by rw [hZ0]; omega) (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 12) hfork (by omega) b12 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH1 0
  refine Logic.SpecG.seq (Logic.push1G (pc := pc + 13) (by omega) b13 b14 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hZ]
  -- REVERT
  refine Logic.SpecG.consequence (Logic.revertG (pc := pc + 15) hfork (by omega) b15 (by omega))
    (fun _ h => h) ?_
  rintro evm ⟨-, he, -⟩
  rw [he]
  simp

/-! ## The precompile at address 1 under the real runner -/

/-- A message with no value to a precompile that is not disabled: the frame that ends it is the
frame of the precompile (or the start frame, stopped, when the fork has no such precompile),
rolled back on a failure. -/
theorem processMessage_precompile {msg : Message fork} {st : State.TransactionState}
    {ss : Substate} {address : Nat}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (noValue : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0))
    (hpre : precompileAddress fork msg = some address)
    (enabled : msg.disablePrecompiles = false)
    (h : processMessage fork msg st ss = .ok ended) :
    ended.1 = rollbackOnError st
      ((runPrecompile fork address
        (startFrame msg (startState fork msg st) ss
          (GasMeter.start msg.gas msg.reservoir))).getD
        { startFrame msg (startState fork msg st) ss (GasMeter.start msg.gas msg.reservoir) with
          running := false }) := by
  rw [processMessage] at h
  simp only [Except.map, hpre, noValue, enabled, ite_false, bind, pure, Except.bind,
    Except.pure, Bool.false_eq_true] at h
  split at h <;> rename_i heq
  · cases h
  · cases h
    split at heq <;> rename_i h3
    · cases heq
      rw [if_neg noValue] at h3
      show rollbackOnError st _ = rollbackOnError st _
      rw [h3]
      rfl
    · cases heq
      rw [if_neg noValue] at h3
      rw [h3]
      rfl

/-- The frame of the precompile at address 1: with less than 3000 gas it halts with an error,
otherwise it stops with the output of `Ecrecover.compute` and 3000 gas less. -/
theorem runPrecompile_ecrecover (evm : Evm fork Nat) :
    runPrecompile fork 1 evm = some
      (if evm.gas < 3000 then exceptionalHalt evm .precompile
        else { evm with gas := evm.gas - 3000,
                        output := Precompiles.Ecrecover.compute evm.message.data,
                        running := false }) := by
  have hp : Precompiles.isPrecompile fork 1 = true := by
    simp [Precompiles.isPrecompile, Precompiles.addedAt, Fork.frontier_le]
  by_cases hg : evm.gas < 3000
  · simp [runPrecompile, Precompiles.run, hp, Precompiles.Ecrecover.ecrecover,
      Precompiles.Ecrecover.GAS_ECRECOVER, GasMeter.gasLeft, hg, Except.mapError]
  · simp [runPrecompile, Precompiles.run, Precompiles.price, hp, Precompiles.Ecrecover.ecrecover,
      Precompiles.Ecrecover.GAS_ECRECOVER, GasMeter.gasLeft, GasMeter.charge, hg,
      Except.mapError]

/-- The message of a call to address 1 calls the precompile at 1. -/
theorem precompileAddress_one {msg : Message fork}
    (hca : msg.codeAddress = some (toAddressMasked 1)) : precompileAddress fork msg = some 1 := by
  have hn : (toAddressMasked (1 : U256)).toU256.toNat = 1 := by decide +kernel
  have hp : Precompiles.isPrecompile fork 1 = true := by
    simp [Precompiles.isPrecompile, Precompiles.addedAt, Fork.frontier_le]
  unfold precompileAddress
  rw [hca]
  show (if Precompiles.isPrecompile fork (toAddressMasked (1 : U256)).toU256.toNat = true then
    some (toAddressMasked (1 : U256)).toU256.toNat else none) = some 1
  rw [hn, hp]
  rfl

/-- `processRunner` on a message with no value to the precompile at address 1. With less than
3000 gas the frame that ends the message has an error. Otherwise it has no error, the state the
message started from, the substate of a child with no log, the output of `Ecrecover.compute` on
the data of the message, and 3000 gas less than the message. -/
theorem ecrecover_ran {bound : Nat} {caller child : Evm fork Nat} {msg : Message fork}
    {to : Address} (hran : Ran (processRunner fork bound) caller msg child)
    (htarget : msg.target = some to) (hca : msg.codeAddress = some (toAddressMasked 1))
    (enabled : msg.disablePrecompiles = false) (hvalue : msg.value = 0) :
    (msg.gas < 3000 ∧ child.error ≠ none) ∨
    (3000 ≤ msg.gas ∧ child.error = none ∧ child.state = startState fork msg caller.state ∧
      child.substate = caller.substate.child ∧
      child.output = Precompiles.Ecrecover.compute msg.data ∧ child.gas = msg.gas - 3000) := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  rw [hp] at hrun
  have h := processMessage_precompile (fun h => h.2 hvalue) (precompileAddress_one hca) enabled
    hrun
  rw [runPrecompile_ecrecover, Option.getD_some] at h
  have hF : (startFrame msg (startState fork msg caller.state) caller.substate.child
      (GasMeter.start msg.gas msg.reservoir)).gas = msg.gas := rfl
  rw [hF] at h
  by_cases hg : msg.gas < 3000
  · rw [if_pos hg] at h
    refine .inl ⟨hg, ?_⟩
    rw [h]
    simp [rollbackOnError, exceptionalHalt]
  · rw [if_neg hg, rollbackOnError_of_error_eq_none rfl] at h
    refine .inr ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h] <;>
      first
        | (simp only [startFrame]; done)
        | rfl

/-- A set with its own elements inserted is the set. -/
theorem insertMany_self (t : Std.ExtTreeSet Address) : t.insertMany t.toList = t :=
  Std.ExtTreeSet.ext_contains fun k => by
    rw [Std.ExtTreeSet.contains_insertMany_list, Std.ExtTreeSet.contains_toList, Bool.or_self]

/-- From Paris, a caller that takes in a child with no error, which ran in the substate of a
child and left it as it was (a precompile): the caller has its own substate back, and the state
of the child. -/
theorem incorporateChild_precompile (hparis : .paris ≤ fork) {caller child : Evm fork Nat}
    (herr : child.error = none) (hsub : child.substate = caller.substate.child) :
    (incorporateChild fork caller child).state = child.state ∧
      (incorporateChild fork caller child).substate = caller.substate := by
  have hnp : ¬fork < Fork.paris := Nat.not_lt.mpr hparis
  have ht : touchedOnSuccess fork caller child = caller.substate.touchedAccounts := by
    simp [touchedOnSuccess, hnp]
  refine ⟨by simp [incorporateChild, herr], ?_⟩
  simp only [incorporateChild, herr, Option.isNone_none, ite_true, ht, hsub]
  generalize caller.substate = cs
  cases cs
  simp [Substate.child, Substate.empty, insertMany_self]

/-! ## The word read from the output range -/

/-- The word that a caller reads from an output range of 32 bytes that held 0 before the call
of ECRECOVER: the 32 bytes of the output (12 zero bytes and the address), or 0 when the output
is empty (the signature was rejected). -/
def recoveredWord (data : ByteArray) : U256 :=
  if (Precompiles.Ecrecover.compute data).size = 32 then
    loadWord (Precompiles.Ecrecover.compute data) 0 32
  else 0

/-- The output of ECRECOVER has 32 bytes or none. -/
theorem size_compute (data : ByteArray) :
    (Precompiles.Ecrecover.compute data).size = 32 ∨
      (Precompiles.Ecrecover.compute data).size = 0 := by
  unfold Precompiles.Ecrecover.compute Precompiles.Ecrecover.output
  split
  · split
    · left
      simp [ByteArray.size]
    · right
      rfl
  · right
    rfl

/-- The word at an output range of 32 bytes that held 0, after the write of the output of
ECRECOVER. -/
theorem load_ecrecover {m : ByteArray} {o : Nat} (data : ByteArray) (hfit : o + 32 ≤ m.size)
    (h0 : loadWord (memoryReadBytes m o 32) 0 32 = 0) :
    loadWord (memoryReadBytes (memoryWrite m o
      ((Precompiles.Ecrecover.compute data).extract 0
        (min 32 (Precompiles.Ecrecover.compute data).size))) o 32) 0 32 = recoveredWord data := by
  unfold recoveredWord
  rcases size_compute data with h | h
  · rw [if_pos h, h, Nat.min_self]
    have hx : (Precompiles.Ecrecover.compute data).extract 0 32 =
        Precompiles.Ecrecover.compute data := by
      have := ByteArray.extract_zero_size (b := Precompiles.Ecrecover.compute data)
      rwa [h] at this
    rw [hx, ← wordBytes_loadWord h]
    rw [loadWord_memoryWrite_wordBytes _ hfit, wordBytes_loadWord h]
  · have hne : ¬(Precompiles.Ecrecover.compute data).size = 32 := by omega
    rw [if_neg hne, h]
    have hw : memoryWrite m o ((Precompiles.Ecrecover.compute data).extract 0 (min 32 0)) =
        m := by
      have hsz : ((Precompiles.Ecrecover.compute data).extract 0 (min 32 0)).size = 0 := by
        rw [ByteArray.size_extract]
        omega
      simp [memoryWrite, hsz]
    rw [hw]
    exact h0

/-- Two ranges inside the memory grow it by nothing. -/
theorem extendMemory_two {size : Nat} {s1 l1 s2 l2 : U256} (h1 : s1.toNat + l1.toNat ≤ size)
    (h2 : s2.toNat + l2.toNat ≤ size) : extendMemory size [(s1, l1), (s2, l2)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero size _ fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans h1 (le_ceil32 size)))
    · rw [List.mem_singleton.mp hp]
      exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans h2 (le_ceil32 size)))

/-- The write of the output of ECRECOVER to a range of 32 bytes inside the memory keeps its
size. -/
theorem size_ecrecover_write {m : ByteArray} {o : Nat} (data : ByteArray)
    (hfit : o + 32 ≤ m.size) :
    (memoryWrite m o ((Precompiles.Ecrecover.compute data).extract 0
      (min 32 (Precompiles.Ecrecover.compute data).size))).size = m.size :=
  size_memoryWrite (by rw [ByteArray.size_extract]; omega)

/-- The write of the output of ECRECOVER keeps the bytes outside its range of 32 bytes. -/
theorem read_ecrecover_other {m : ByteArray} {o a k : Nat} (data : ByteArray)
    (hfit : o + 32 ≤ m.size) (hd : a + k ≤ o ∨ o + 32 ≤ a) :
    memoryReadBytes (memoryWrite m o ((Precompiles.Ecrecover.compute data).extract 0
      (min 32 (Precompiles.Ecrecover.compute data).size))) a k = memoryReadBytes m a k := by
  rcases size_compute data with h | h
  · exact memoryReadBytes_memoryWrite_of_disjoint (by rw [ByteArray.size_extract]; omega)
      (by rw [ByteArray.size_extract]; omega)
  · have hsz : ((Precompiles.Ecrecover.compute data).extract 0
        (min 32 (Precompiles.Ecrecover.compute data).size)).size = 0 := by
      rw [ByteArray.size_extract]
      omega
    have hw : memoryWrite m o ((Precompiles.Ecrecover.compute data).extract 0
        (min 32 (Precompiles.Ecrecover.compute data).size)) = m := by
      simp [memoryWrite, hsz]
    rw [hw]

/-! ## The join: GAS STATICCALL to address 1 and the code after it -/

/-- From Paris and before Glamsterdam, under EthLib's real runner: a run from the frame at
`GAS STATICCALL` with the address 1 on top, followed by the code that passes a failure on
(`bubble_no_ok`), that returns a frame `s` with no error.

Then the call was made and the precompile had its 3000 gas, and the loop went on from the opcode
after STATICCALL with 1 pushed. The memory is the one before, grown for both ranges, with the
start of the output of `Ecrecover.compute` (on the bytes of the input range) written to the
output range. The state is the one before with the two reads recorded, the substate is the one
before with address 1 accessed (no log, no refund), and the gas is exact.

`hdel`: the account at address 1 holds no EIP-7702 delegation code (a state fact). -/
theorem ecrecover_call_ok (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {inputStart inputSize outputStart outputSize : U256} {rest : List U256} {q : Nat}
    (hq : q = pc + 2) (hlt : q + 15 < code.size)
    (bg : code[pc]'(by omega) = 0x5a) (bs : code[pc + 1]'(by omega) = 0xfa)
    (b0 : code[q]'(by omega) = 0x15) (b1 : code[q + 1]'(by omega) = 0x80)
    (b2 : code[q + 2]'(by omega) = 0x15) (b3 : code[q + 3]'(by omega) = 0x61)
    (b6 : code[q + 6]'(by omega) = 0x57) (b7 : code[q + 7]'(by omega) = 0x3d)
    (b8 : code[q + 8]'(by omega) = 0x60) (b9 : code[q + 9]'(by omega) = 0x00)
    (b10 : code[q + 10]'(by omega) = 0x80) (b11 : code[q + 11]'(by omega) = 0x3e)
    (b12 : code[q + 12]'(by omega) = 0x3d) (b13 : code[q + 13]'(by omega) = 0x60)
    (b14 : code[q + 14]'(by omega) = 0x00) (b15 : code[q + 15]'(by omega) = 0xfd)
    (hrest : rest.length + 6 < STACK_LIMIT)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {evm s : Evm fork Nat}
    (start : At code message pc
      (1 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
        (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
          routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)).subCall ∧
    ∃ after,
      At code message q (1 :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat
          ((Precompiles.Ecrecover.compute (memoryReadBytes (memoryExtend memory
              (extendMemory memory.size
                [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
              inputStart.toNat inputSize.toNat)).extract 0
            (min outputSize.toNat (Precompiles.Ecrecover.compute (memoryReadBytes
              (memoryExtend memory (extendMemory memory.size
                [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
              inputStart.toNat inputSize.toNat)).size)))
        (gas - 2 - ((messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
            routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          ((messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1))
                none)).subCall - 3000))
        ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after
          within' = .ok s := by
  subst hq
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hparis
  have hlim : STACK_LIMIT = 1024 := rfl
  have hnp : ¬fork < Fork.paris := Nat.not_lt.mpr hparis
  -- the code after a failed call gives no run with no error
  have bubble : ∀ {mem g st ss rd after}
      (_ : Logic.At code message (pc + 1 + 1) (0 :: rest) mem g st ss rd after)
      (w : GasMeter.gasHeld after.gas ≤ bound),
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after w =
        .ok s → False := by
    intro mem g st ss rd after hat w h
    have hat' : Logic.At code message (pc + 2) (0 :: rest) mem g st ss rd after := hat
    exact bubble_no_ok hbyz hlt b0 b1 b2 b3 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
      (by rw [hlim] at hrest ⊢; omega) hat' w h hok
  -- GAS
  rcases gas_outcome (by omega) bg (by rw [hlim] at hrest ⊢; simp only [List.length_cons]; omega)
    start within hrun with herr | ⟨a1, hat1, w1, hrun1⟩
  · exact (herr hok).elim
  -- STATICCALL
  rcases staticcall_outcome hberlin hglam (by omega) bs hdel hat1.toLogic w1 hrun1 with
    herr | ⟨mem, g, st, ss, rd, a2, hat2, w2, hrun2⟩ |
    ⟨calleeCode, caller, msg, child, a2, hsend, hran, -, hat2, w2, hrun2⟩
  · exact (herr hok).elim
  · exact (bubble hat2 w2 hrun2).elim
  · obtain ⟨cs, css, cgas, -, -, -, ctarget, cca, -, cdis, cdata, cvalue, -⟩ := hsend
    rcases ecrecover_ran hran ctarget cca cdis (by rw [cvalue]; rfl) with
      ⟨-, herr⟩ | ⟨hg, herr, hstate, hsub, hout, hcg⟩
    · have hflag : (if child.error.isNone then (1 : U256) else 0) = 0 := by
        cases hce : child.error with
        | none => exact (herr hce).elim
        | some e => rfl
      rw [hflag] at hat2
      exact (bubble hat2 w2 hrun2).elim
    · have hflag : (if child.error.isNone then (1 : U256) else 0) = 1 := by rw [herr]; rfl
      obtain ⟨istate, isub⟩ := incorporateChild_precompile hparis herr hsub
      have hstart : startState fork msg caller.state = caller.state := by
        simp only [startState, hnp, ite_false]
      rw [cgas] at hg hcg
      refine ⟨hg, a2, ?_, w2, hrun2⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hat2
      refine ⟨h1, h2, h3, h4, by rw [h5, hflag], ?_, ?_, h8, h9, h10, ?_, ?_⟩
      · rw [h6, hout, cdata]
      · rw [h7, hcg]
      · rw [h11, istate, hstate, hstart, cs]
        rfl
      · rw [h12, isub, css]
        rfl

end TokenKit

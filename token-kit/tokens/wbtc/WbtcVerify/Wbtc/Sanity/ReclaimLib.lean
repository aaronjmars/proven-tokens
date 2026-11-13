import WbtcVerify.Wbtc.Steps
import TokenKit.Evm.Payee
import TokenKit.Evm.WitnessOpt
import TokenKit.Evm.Precompile
import TokenKit.Evm.Tail

/-!
# Tools for the witnesses of reclaimToken: the runner and four tiny callees

Written by hand (not generated). Nothing here is about the code of WBTC; `Sanity/ReclaimSeg.lean`
and `Sanity/Reclaim*.lean` use these.

Proved:
- `mcg_exact`: the 63/64 rule of a CALL with no value and no growth of memory that asks for at
  least all the gas left: the message gets exactly the gas left after the price minus one 64th.
- `runner_of_run`, `frame_of_ran`: what EthLib's real runner `processRunner` gives for a message
  with a target, no value and no precompile, from Paris: the frame that the loop of the
  interpreter returns for the start frame of the message, rolled back on an error. In both
  directions.
- `tinyCode b last`: the ten bytes `PUSH1 b, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, last`. With
  `last` = RETURN it is a contract that answers every call with the 32 byte word `b`
  (`ONE_CODE`, `ZERO_CODE`); with `last` = REVERT it reverts every call with that word as data
  (`REVERT_CODE`). `tiny_return`, `tiny_revert`: their specifications, 18 gas.
- `tiny_message_runs`, `tiny_message_reverts`, `stop_message_runs`: the real
  runner does run a message to each of these codes (and to the one byte STOP), with the frame it
  gives.
- `tiny_child_keeps`: every frame with no error that the real runner gives for a message to a
  `tinyCode b 0xf3`, with any gas and any data, has the state of the caller.
- `codeState`: a state like `sState` where one more account holds a given code, under the keccak
  hash of that code.

Assumed: nothing beyond the hypotheses written in each statement (fork bounds, the fields of the
message). Not covered: messages with value, precompiles, creation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace WbtcVerify.Sanity

open UsdtVerify
open TokenKit
open WbtcVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The gas of the CALL -/

/-- The 63/64 rule for a CALL with no value and no growth of memory that asks for at least the gas
left after the price `E`: the message gets that gas minus one 64th, and the frame pays that and
the price. -/
theorem mcg_exact (htw : Fork.tangerineWhistle ≤ fork) {asked gas E : Nat} (h : E ≤ gas)
    (hask : gas - E ≤ asked) :
    (messageCallGas fork 0 asked gas 0 E).subCall = gas - E - (gas - E) / 64 ∧
      (messageCallGas fork 0 asked gas 0 E).cost = gas - E - (gas - E) / 64 + E := by
  have hc : fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas := ⟨htw, h⟩
  have hs : (messageCallGas fork 0 asked gas 0 E).subCall =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) +
      (if (0 : U256) = 0 then 0 else CALL_STIPEND) := rfl
  have hk : (messageCallGas fork 0 asked gas 0 E).cost =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) + E := rfl
  have hx : maxMessageCallGas (gas - 0 - E) = gas - 0 - E - (gas - 0 - E) / 64 := rfl
  have hm : min asked (maxMessageCallGas (gas - 0 - E)) = gas - E - (gas - E) / 64 := by
    rw [hx, Nat.min_eq_right (by omega)]
    simp
  rw [hs, hk, if_pos hc, if_pos (rfl : (0 : U256) = 0), hm]
  omega

/-! ## The real runner on a message with no value -/

/-- A message whose code address is no precompile runs no precompile. -/
theorem noPre_of {msg : Message fork} {a : Address} (h : msg.codeAddress = some a)
    (hnp : Precompiles.isPrecompile fork a.toU256.toNat = false) :
    precompileAddress fork msg = none := by
  simp [precompileAddress, h, hnp]

/-- A frame that the message layer rolls back keeps its error. -/
theorem error_rollbackOnError (snapshot : State.TransactionState) (evm : Evm fork Nat) :
    (rollbackOnError snapshot evm).error = evm.error := by
  unfold rollbackOnError
  split <;> rfl

/-- A frame that the message layer rolls back keeps its output. -/
theorem output_rollbackOnError (snapshot : State.TransactionState) (evm : Evm fork Nat) :
    (rollbackOnError snapshot evm).output = evm.output := by
  unfold rollbackOnError
  split <;> rfl

/-- The state of a frame with an error, after the message layer rolled it back. -/
theorem state_rollbackOnError_of_error {snapshot : State.TransactionState} {evm : Evm fork Nat}
    {e : EvmError} (h : evm.error = some e) :
    (rollbackOnError snapshot evm).state = evm.state.restoreTxState snapshot := by
  simp [rollbackOnError, h]

/-- From Paris the state at the start of a message is the state it is given. -/
theorem startState_of_paris (hparis : .paris ≤ fork) (msg : Message fork)
    (S : State.TransactionState) : startState fork msg S = S := by
  simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]

/-- The start frame of a message holds the gas of the message. -/
theorem start_within (msg : Message fork) (S : State.TransactionState) (ss : Substate) :
    GasMeter.gasHeld (startFrame (fork := fork) msg S ss
      (GasMeter.start (Meter := Nat) msg.gas msg.reservoir)).gas ≤ msg.gas := Nat.le_refl _

/-- `processRunner` on a message with a target, no value and no precompile, whose start frame the
loop of the interpreter runs to `stopped`: it gives `stopped`, rolled back on an error. -/
theorem runner_of_run {bound : Nat} {caller : Evm fork Nat} {msg : Message fork} {to : Address}
    (lt : msg.gas < bound) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    {within} {stopped : Evm fork Nat}
    (hrf : Evm.runFrame (step fork) (step_decreases fork) msg.gas (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) within = .ok stopped) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1 = rollbackOnError caller.state stopped := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  have hmap := processMessage_map_val ht noPre hrf
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    simp only [Except.map, Except.ok.injEq] at hmap
    exact ⟨child, rfl, hmap⟩

/-- The other direction: a frame that `processRunner` gave for a message with a target, no value
and no precompile is the frame that the loop of the interpreter returns for the start frame of
the message, rolled back on an error. -/
theorem frame_of_ran {bound : Nat} {caller child : Evm fork Nat} {msg : Message fork}
    {to : Address} (hran : Ran (processRunner fork bound) caller msg child)
    (htarget : msg.target = some to) (noPre : precompileAddress fork msg = none)
    (hv : msg.value = 0) :
    ∃ stopped, Evm.runFrame (step fork) (step_decreases fork) msg.gas
        (processRunner fork msg.gas)
        (startFrame msg (startState fork msg caller.state) caller.substate.child
          (GasMeter.start msg.gas msg.reservoir)) (start_within msg _ _) = .ok stopped ∧
      child = rollbackOnError caller.state stopped := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  rw [hp] at hrun
  cases hres : Evm.runFrame (step fork) (step_decreases fork) msg.gas
      (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) (start_within msg _ _) with
  | error e =>
    have hmap := processMessage_map_val ht noPre hres
    rw [hrun] at hmap
    simp [Except.map] at hmap
  | ok stopped =>
    have hmap := processMessage_map_val ht noPre hres
    rw [hrun] at hmap
    simp only [Except.map, Except.ok.injEq] at hmap
    exact ⟨stopped, rfl, hmap⟩

/-- `processRunner` on a message with a target, no value and no precompile, from Paris, whose
code meets a specification from its start: it gives a frame `child` that is a frame of the
postcondition, rolled back on an error. -/
theorem runner_of_spec (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} (lt : msg.gas < bound) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    {Q : Evm fork Nat → Prop}
    (spec : Gas.SpecG fork
      (At msg.code msg 0 [] .empty msg.gas caller.state caller.substate.child) Q) :
    ∃ child stopped, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1 = rollbackOnError caller.state stopped ∧ Q stopped := by
  have hst := startState_of_paris hparis msg caller.state
  obtain ⟨stopped, hrf, hq⟩ := Gas.SpecG.runFrame spec
    (bound := msg.gas) (runChild := processRunner fork msg.gas)
    (by
      have h := At.startFrame (message := msg) rfl (startState fork msg caller.state)
        caller.substate.child
      rw [hst] at h
      exact h)
    (Nat.le_refl _)
  rw [← hst] at hrf
  obtain ⟨child, hrun, hc⟩ := runner_of_run lt htarget noPre hv hrf
  exact ⟨child, stopped, hrun, hc, hq⟩

/-! ## Tiny callees -/

/-- The ten bytes `PUSH1 b, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, last`. -/
def tinyCode (b last : UInt8) : ByteArray :=
  ⟨#[0x60, b, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, last]⟩

/-- A contract that answers every call with the 32 byte word 1. -/
def ONE_CODE : ByteArray := tinyCode 0x01 0xf3

/-- A contract that answers every call with the 32 byte word 0. -/
def ZERO_CODE : ByteArray := tinyCode 0x00 0xf3

/-- A contract that reverts every call, with the 32 byte word 0x2a as its data. -/
def REVERT_CODE : ByteArray := tinyCode 0x2a 0xfd

/-- The memory of a `tinyCode b` after its MSTORE. -/
def tinyMem (b : UInt8) : ByteArray :=
  memoryWrite (memoryExtend .empty 32) 0 (wordBytes (BitVec.ofNat 256 b.toNat))

/-- The 32 bytes that a `tinyCode b` gives back. -/
def tinyOut (b : UInt8) : ByteArray := memoryReadBytes (tinyMem b) 0 32

theorem size_tinyCode (b last : UInt8) : (tinyCode b last).size = 10 := rfl

theorem size_tinyMem (b : UInt8) : (tinyMem b).size = 32 := by
  have h : (ByteArray.empty).size = 0 := rfl
  exact size_rawW (n := 32) h (by decide)

theorem tinyOut_one : tinyOut 0x01 = wordBytes 1 := by decide +kernel

theorem tinyOut_zero : tinyOut 0x00 = wordBytes 0 := by decide +kernel

theorem tinyOut_revert : tinyOut 0x2a = wordBytes 42 := by decide +kernel

theorem delegatedAddress_one : delegatedAddress ONE_CODE = none := by decide

theorem delegatedAddress_zero : delegatedAddress ZERO_CODE = none := by decide

theorem delegatedAddress_revert : delegatedAddress REVERT_CODE = none := by decide

/-- The first five opcodes of a `tinyCode`: the word `b` is in the memory, 12 gas. -/
theorem tiny_head (b last : UInt8) {msg : Message fork} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} (hg : 18 ≤ gas) :
    Gas.HoareG fork (At (tinyCode b last) msg 0 [] .empty gas st ss)
      (At (tinyCode b last) msg 9 [0, 32] (tinyMem b) (gas - 18) st ss) := by
  have hcost : (extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))]).cost = 3 := by
    decide
  have hexp : (extendMemory ByteArray.empty.size [((0 : U256), (32 : U256))]).expandBy = 32 := by
    decide
  have hcost2 : (extendMemory (tinyMem b).size [((0 : U256), (32 : U256))]).cost = 0 := by
    rw [size_tinyMem]
    decide
  have s1 : Gas.HoareG fork (At (tinyCode b last) msg 0 [] .empty gas st ss)
      (At (tinyCode b last) msg 2 [BitVec.ofNat 256 b.toNat] .empty (gas - 3) st ss) :=
    Gas.push1G (by rw [size_tinyCode]; decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have s2 : Gas.HoareG fork
      (At (tinyCode b last) msg 2 [BitVec.ofNat 256 b.toNat] .empty (gas - 3) st ss)
      (At (tinyCode b last) msg 4 [0, BitVec.ofNat 256 b.toNat] .empty (gas - 3 - 3) st ss) :=
    Gas.push1G (by rw [size_tinyCode]; decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have s3 : Gas.HoareG fork
      (At (tinyCode b last) msg 4 [0, BitVec.ofNat 256 b.toNat] .empty (gas - 3 - 3) st ss)
      (At (tinyCode b last) msg 5 [] (tinyMem b) (gas - 3 - 3 - (3 + 3)) st ss) := by
    have r := Gas.mstoreG (fork := fork) (code := tinyCode b last) (message := msg) (pc := 4)
      (start := 0) (value := BitVec.ofNat 256 b.toNat) (rest := []) (memory := .empty)
      (gas := gas - 3 - 3) (state := st) (substate := ss) (by rw [size_tinyCode]; decide) rfl
      (by rw [hcost]; omega)
    rw [hcost, hexp] at r
    exact r
  have s4 : Gas.HoareG fork
      (At (tinyCode b last) msg 5 [] (tinyMem b) (gas - 3 - 3 - (3 + 3)) st ss)
      (At (tinyCode b last) msg 7 [32] (tinyMem b) (gas - 3 - 3 - (3 + 3) - 3) st ss) :=
    Gas.push1G (by rw [size_tinyCode]; decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have s5 : Gas.HoareG fork
      (At (tinyCode b last) msg 7 [32] (tinyMem b) (gas - 3 - 3 - (3 + 3) - 3) st ss)
      (At (tinyCode b last) msg 9 [0, 32] (tinyMem b) (gas - 3 - 3 - (3 + 3) - 3 - 3) st ss) :=
    Gas.push1G (by rw [size_tinyCode]; decide) rfl rfl (by omega) (by simp [STACK_LIMIT])
  have e : gas - 3 - 3 - (3 + 3) - 3 - 3 = gas - 18 := by omega
  rw [e] at s5
  exact Triple.seq s1 (Triple.seq s2 (Triple.seq s3 (Triple.seq s4 s5)))

/-- A `tinyCode b` that ends with RETURN: it returns the word `b`, for 18 gas, and keeps the
state and the substate. -/
theorem tiny_return (b : UInt8) {msg : Message fork} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} (hg : 18 ≤ gas) :
    Gas.SpecG fork (At (tinyCode b 0xf3) msg 0 [] .empty gas st ss)
      (Halted false (tinyOut b) (gas - 18) st ss) := by
  have hcost2 : (extendMemory (tinyMem b).size [((0 : U256), (32 : U256))]).cost = 0 := by
    rw [size_tinyMem]
    decide
  have hexp2 : (extendMemory (tinyMem b).size [((0 : U256), (32 : U256))]).expandBy = 0 := by
    rw [size_tinyMem]
    decide
  have r := Gas.returnG (fork := fork) (code := tinyCode b 0xf3) (message := msg) (pc := 9)
    (start := 0) (size := 32) (rest := []) (memory := tinyMem b) (gas := gas - 18) (state := st)
    (substate := ss) (by rw [size_tinyCode]; decide) rfl (by rw [hcost2]; omega)
  rw [hcost2, hexp2, memoryExtend_zero] at r
  exact Gas.SpecG.seq (tiny_head b 0xf3 hg) r

/-- A `tinyCode b` that ends with REVERT: it reverts with the word `b` as data, for 18 gas. -/
theorem tiny_revert (hfork : .byzantium ≤ fork) (b : UInt8) {msg : Message fork} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} (hg : 18 ≤ gas) :
    Gas.SpecG fork (At (tinyCode b 0xfd) msg 0 [] .empty gas st ss)
      (Halted true (tinyOut b) (gas - 18) st ss) := by
  have hcost2 : (extendMemory (tinyMem b).size [((0 : U256), (32 : U256))]).cost = 0 := by
    rw [size_tinyMem]
    decide
  have hexp2 : (extendMemory (tinyMem b).size [((0 : U256), (32 : U256))]).expandBy = 0 := by
    rw [size_tinyMem]
    decide
  have r := Gas.revertG (fork := fork) hfork (code := tinyCode b 0xfd) (message := msg) (pc := 9)
    (start := 0) (size := 32) (rest := []) (memory := tinyMem b) (gas := gas - 18) (state := st)
    (substate := ss) (by rw [size_tinyCode]; decide) rfl (by rw [hcost2]; omega)
  rw [hcost2, hexp2, memoryExtend_zero] at r
  exact Gas.SpecG.seq (tiny_head b 0xfd hg) r

/-! ## The real runner on the tiny callees -/

/-- From Paris, `processRunner` does run a message with no value and at least 18 gas whose code
is a `tinyCode b` that returns, to a target that is no precompile: it gives a frame with no
error, the word `b` as output, and the state of the caller. -/
theorem tiny_message_runs (hparis : .paris ≤ fork) (b : UInt8) {bound : Nat}
    {caller : Evm fork Nat} {msg : Message fork} {to : Address} (lt : msg.gas < bound)
    (hcode : msg.code = tinyCode b 0xf3) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) (hg : 18 ≤ msg.gas) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = tinyOut b ∧ child.1.state = caller.state ∧
      child.1.substate = caller.substate.child := by
  obtain ⟨child, stopped, hrun, hc, -, he, ho, -, hs, hss⟩ :=
    runner_of_spec hparis (caller := caller) lt htarget noPre hv
      (by rw [hcode]; exact tiny_return b hg)
  have he' : stopped.error = none := by simpa using he
  rw [rollbackOnError_of_error_eq_none he'] at hc
  exact ⟨child, hrun, by rw [hc]; exact he', by rw [hc]; exact ho, by rw [hc]; exact hs,
    by rw [hc]; exact hss⟩

/-- From Paris, `processRunner` does run a message with no value and at least 18 gas whose code
is a `tinyCode b` that reverts: it gives a frame with the revert error, the word `b` as
output, and the state of the caller put back. -/
theorem tiny_message_reverts (hparis : .paris ≤ fork) (b : UInt8) {bound : Nat}
    {caller : Evm fork Nat} {msg : Message fork} {to : Address} (lt : msg.gas < bound)
    (hcode : msg.code = tinyCode b 0xfd) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) (hg : 18 ≤ msg.gas) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = some .revert ∧ child.1.output = tinyOut b ∧
      child.1.state = caller.state.restoreTxState caller.state := by
  obtain ⟨child, stopped, hrun, hc, -, he, ho, -, hs, -⟩ :=
    runner_of_spec hparis (caller := caller) lt htarget noPre hv
      (by rw [hcode]; exact tiny_revert (Nat.le_trans (by decide) hparis) b hg)
  have he' : stopped.error = some .revert := by simpa using he
  exact ⟨child, hrun, by rw [hc, error_rollbackOnError]; exact he',
    by rw [hc, output_rollbackOnError]; exact ho,
    by rw [hc, state_rollbackOnError_of_error he', hs]⟩

/-- From Paris, `processRunner` does run a message with no value whose code is the one byte STOP:
it gives a frame with no error, an empty output, and the state of the caller. -/
theorem stop_message_runs (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} (lt : msg.gas < bound)
    (hcode : msg.code = Payee.STOP_CODE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = .empty ∧ child.1.state = caller.state ∧
      child.1.substate = caller.substate.child := by
  obtain ⟨child, stopped, hrun, hc, -, he, ho, -, hs, hss⟩ :=
    runner_of_spec hparis (caller := caller) lt htarget noPre hv
      (by
        rw [hcode]
        exact Gas.stopG (by decide) rfl)
  have he' : stopped.error = none := by simpa using he
  rw [rollbackOnError_of_error_eq_none he'] at hc
  exact ⟨child, hrun, by rw [hc]; exact he', by rw [hc]; exact ho, by rw [hc]; exact hs,
    by rw [hc]; exact hss⟩

/-- Every frame with no error that `processRunner` gave, from Paris, for a message with no value
whose code is a `tinyCode b` that returns: it has the state of the caller and the word `b` as
output. For any gas of the message and any call data. -/
theorem tiny_child_keeps (hparis : .paris ≤ fork) (b : UInt8) {bound : Nat}
    {caller child : Evm fork Nat} {msg : Message fork} {to : Address}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = tinyCode b 0xf3) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (herr : child.error = none) :
    child.state = caller.state ∧ child.output = tinyOut b := by
  obtain ⟨stopped, hrf, rfl⟩ := frame_of_ran hran htarget noPre hv
  rw [error_rollbackOnError] at herr
  rw [rollbackOnError_of_error_eq_none herr]
  have hst := startState_of_paris hparis msg caller.state
  have hat : At (tinyCode b 0xf3) msg 0 [] .empty msg.gas caller.state caller.substate.child
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) := by
    have h := At.startFrame (message := msg) hcode caller.state caller.substate.child
    rw [hst]
    exact h
  have hends : Gas.Ends fork
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir)) stopped := Gas.Ends.run hrf
  obtain ⟨-, ho, -, hs, -⟩ := Gas.SpecG.haltedE (k := 18)
    (tiny_return (fork := fork) b (msg := msg) (gas := msg.gas + 18) (st := caller.state)
      (ss := caller.substate.child) (by omega)) hat hends herr
  exact ⟨hs, ho⟩

/-! ## A state where one more account holds code -/

/-- The keccak hash under which the state keeps a code. -/
abbrev hashOf (code : ByteArray) : EthLib.Base.Hash32 :=
  EthLib.Cryptography.Hash.Keccak.keccak256 code

/-- `sState C kvs` with one more account, at `a`, that holds the code `code` (nonce 1, no ether),
kept under its keccak hash as EthLib's `setCode` keeps it. -/
def codeState (C : Address) (kvs : List (U256 × U256)) (a : Address) (code : ByteArray) :
    State.TransactionState :=
  { (sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩) with
    codeWrites := ((sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code }

/-- The storage of `codeState` is that of `sState`. -/
theorem storageAt_codeState (C : Address) (kvs : List (U256 × U256)) (a : Address)
    (code : ByteArray) (C' : Address) (n : U256) :
    storageAt (codeState C kvs a code) C' n = storageAt (sState C kvs) C' n := rfl

/-- `codeState` has the account of the contract, when the account with code is another one. -/
theorem hasAccount_codeState {C : Address} (kvs : List (U256 × U256)) {a : Address}
    (code : ByteArray) (h : C ≠ a) : hasAccount (codeState C kvs a code) C := by
  have e : (codeState C kvs a code).getAccountOptional C = (sState C kvs).getAccountOptional C :=
    getAccountOptional_setAccount_of_ne (sState C kvs) (some ⟨1, 0, hashOf code⟩) h
  have h0 := hasAccount_sState C kvs
  unfold hasAccount at h0 ⊢
  rw [e]
  exact h0

/-- `codeState` gives the code for its account, when the hash of the code is not the hash of the
empty code. -/
theorem getCode_codeState (C : Address) (kvs : List (U256 × U256)) (a : Address)
    {code : ByteArray} (hH : hashOf code ≠ EMPTY_CODE_HASH) :
    (codeState C kvs a code).getCode ((codeState C kvs a code).getAccount a).codeHash =
      .ok code := by
  have e : (codeState C kvs a code).getAccountOptional a = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self (sState C kvs) a (some ⟨1, 0, hashOf code⟩)
  have hacct : ((codeState C kvs a code).getAccount a).codeHash = hashOf code := by
    unfold State.TransactionState.getAccount
    rw [e] <;> rfl
  have e2 : (codeState C kvs a code).codeWrites[hashOf code]? = some code := by
    show (((sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[hashOf code]? = some code
    simp
  rw [hacct]
  unfold State.TransactionState.getCode
  rw [if_neg hH, e2]

/-- A record of an account read keeps every storage word. -/
theorem storageAt_rar (S : State.TransactionState) (a C : Address) (n : U256) :
    storageAt (S.recordAccountRead a) C n = storageAt S C n := rfl

end WbtcVerify.Sanity

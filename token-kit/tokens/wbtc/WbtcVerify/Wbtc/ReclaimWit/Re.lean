import WbtcVerify.Wbtc.Trace
import WbtcVerify.Wbtc.Sanity.ReclaimSelf

/-!
# A contract that calls back into its caller: the code `RE`

Written by hand (not generated). Fix of audit 4 (the gap of LINK-4, here for WBTC). The witnesses
of `reclaimToken` so far use tokens that do nothing or WBTC itself. Here is a contract that really
calls back into the contract that called it, as a tool for a witness of reentry. Same code and
same lemmas as `RE` of the LINK proofs.

`RE` (45 bytes, written by hand):

    pc  0  PUSH4 a9059cbb   PUSH1 00  MSTORE     memory[0..32)  = the selector of transfer
    pc  8  PUSH2 2000       PUSH1 20  MSTORE     memory[32..64) = the address word 0x2000
    pc 14  PUSH1 01         PUSH1 40  MSTORE     memory[64..96) = the amount 1
    pc 19  PUSH1 00  PUSH1 00  PUSH1 44  PUSH1 1c  PUSH1 00  CALLER  PUSH3 030d40  CALL
    pc 35  PUSH1 01  PUSH1 00  MSTORE  PUSH1 20  PUSH1 00  RETURN

So for every call: it CALLs its caller with the call data `transfer(0x2000, 1)` (68 bytes), no
value and 200000 gas asked, drops the flag of that call, and returns the word 1.

What is proved, with nothing about a particular token:

- `re_prefix`: the frame of `RE` runs from pc 0 to the CALL at pc 34.
- `re_tail`: from pc 35 the frame halts normally with the output `reOut` (the word 1,
  `reOut_eq`), for every flag, state and substate.
- `re_call`: THE FRAME OF `RE`, for every runner and every bound. From 5000 gas, when the state
  holds a code `c` (no delegation) for the caller of the message and the depth limit is not
  reached: the loop goes to the CALL and hands ONE message `msg` to the runner from the frame
  `cl` (`ReSends`: to the caller of the message, from the current target, the call data
  `reData`, no value; 200000 gas when the frame has 210000). For every frame that the runner
  gives for it, the run ends with no error, the output `reOut`, and the state that the CALL took
  in. And each message that the frame sends (`Trace.Sent`) is that one message.
- `spec_message_runs`: `processRunner` runs a message with no value whose frame has a
  specification `Logic.SpecG` to a normal halt: no error, the state of the specification.
- `re_message_runs`: `processRunner` runs a message with no value whose code is `RE`, when it
  runs the message of the CALL of `RE` with no error.

- `clean_of_spec`, `re_clean`, `cleanRun_call`: the events (`Trace.Occurs`) of these runs, so
  the run-local condition `Trace.Clean` can be shown for them.

Assumed: Berlin ≤ fork < Glamsterdam (`re_call`), from Paris for the two `processRunner` lemmas.
Not covered: runs of `RE` with less than 5000 gas, or at the depth limit.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace WbtcVerify.Sanity

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete
  UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## The 63/64 rule -/

/-- The 63/64 rule for a CALL with no value and no growth of memory, when the gas left covers the
price `E`: the message gets at most the gas left after the price, and what the frame pays leaves
it at least one 64th of that. -/
theorem mcg_keep (htw : Fork.tangerineWhistle ≤ fork) {asked gas E : Nat} (h : E ≤ gas) :
    (messageCallGas fork 0 asked gas 0 E).subCall ≤ gas - E ∧
      (messageCallGas fork 0 asked gas 0 E).cost + (gas - E) / 64 ≤ gas := by
  have hc : fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas := ⟨htw, h⟩
  have hs : (messageCallGas fork 0 asked gas 0 E).subCall =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) +
      (if (0 : U256) = 0 then 0 else CALL_STIPEND) := rfl
  have hk : (messageCallGas fork 0 asked gas 0 E).cost =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) + E := rfl
  have hx : maxMessageCallGas (gas - 0 - E) = gas - 0 - E - (gas - 0 - E) / 64 := rfl
  have hm := Nat.min_le_right asked (maxMessageCallGas (gas - 0 - E))
  rw [hs, hk, if_pos hc, if_pos (rfl : (0 : U256) = 0)]
  omega

/-! ## The code -/

/-- The receiver that calls back: see the head of the file. -/
def RE : ByteArray := ⟨#[0x63, 0xa9, 0x05, 0x9c, 0xbb, 0x60, 0x00, 0x52, 0x61, 0x20, 0x00, 0x60,
  0x20, 0x52, 0x60, 0x01, 0x60, 0x40, 0x52, 0x60, 0x00, 0x60, 0x00, 0x60, 0x44, 0x60, 0x1c, 0x60,
  0x00, 0x33, 0x62, 0x03, 0x0d, 0x40, 0xf1, 0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00,
  0xf3]⟩

theorem size_RE : RE.size = 45 := rfl

/-- `RE` is no EIP-7702 delegation indicator. -/
theorem re_not_delegated : delegatedAddress RE = none := by
  have h : isValidDelegation RE = false := by
    simp [isValidDelegation, size_RE, DELEGATION_SIZE]
  simp [delegatedAddress, h]

/-- The word that PUSH1 00 pushes. -/
def reW00 : U256 := BitVec.ofNat 256 (0x00 : UInt8).toNat

/-- The word that PUSH1 01 pushes. -/
def reW01 : U256 := BitVec.ofNat 256 (0x01 : UInt8).toNat

/-- The word that PUSH1 1c pushes. -/
def reW1c : U256 := BitVec.ofNat 256 (0x1c : UInt8).toNat

/-- The word that PUSH1 20 pushes. -/
def reW20 : U256 := BitVec.ofNat 256 (0x20 : UInt8).toNat

/-- The word that PUSH1 40 pushes. -/
def reW40 : U256 := BitVec.ofNat 256 (0x40 : UInt8).toNat

/-- The word that PUSH1 44 pushes. -/
def reW44 : U256 := BitVec.ofNat 256 (0x44 : UInt8).toNat

/-- The selector of `transfer(address,uint256)`, as PUSH4 pushes it. -/
def reSel : U256 := 0xa9059cbb

/-- The address word that the call back sends tokens to. -/
def reDst : U256 := 0x2000

/-- The gas that the CALL asks for: 200000. -/
def reAsk : U256 := 0x030d40

/-- The memory after the first MSTORE. -/
def reM1 : ByteArray :=
  memoryWrite (memoryExtend ByteArray.empty
    (extendMemory ByteArray.empty.size [(reW00, 32)]).expandBy) reW00.toNat (wordBytes reSel)

/-- The gas of the growth of memory at the first MSTORE. -/
def reC1 : Nat := (extendMemory ByteArray.empty.size [(reW00, 32)]).cost

/-- The memory after the second MSTORE. -/
def reM2 : ByteArray :=
  memoryWrite (memoryExtend reM1 (extendMemory reM1.size [(reW20, 32)]).expandBy) reW20.toNat
    (wordBytes reDst)

/-- The gas of the growth of memory at the second MSTORE. -/
def reC2 : Nat := (extendMemory reM1.size [(reW20, 32)]).cost

/-- The memory after the third MSTORE: the memory at the CALL. -/
def reM3 : ByteArray :=
  memoryWrite (memoryExtend reM2 (extendMemory reM2.size [(reW40, 32)]).expandBy) reW40.toNat
    (wordBytes reW01)

/-- The gas of the growth of memory at the third MSTORE. -/
def reC3 : Nat := (extendMemory reM2.size [(reW40, 32)]).cost

/-- The gas from pc 0 to the CALL. -/
def reCost0 : Nat :=
  3 + 3 + (3 + reC1) + 3 + 3 + (3 + reC2) + 3 + 3 + (3 + reC3) + 3 + 3 + 3 + 3 + 3 + 2 + 3

/-- The memory after the MSTORE of the answer. -/
def reM4 : ByteArray :=
  memoryWrite (memoryExtend reM3 (extendMemory reM3.size [(reW00, 32)]).expandBy) reW00.toNat
    (wordBytes reW01)

/-- The gas of the growth of memory at the MSTORE of the answer. -/
def reC4 : Nat := (extendMemory reM3.size [(reW00, 32)]).cost

/-- The gas of the growth of memory at RETURN. -/
def reC5 : Nat := (extendMemory reM4.size [(reW00, reW20)]).cost

/-- The output of `RE`. -/
def reOut : ByteArray :=
  memoryReadBytes (memoryExtend reM4 (extendMemory reM4.size [(reW00, reW20)]).expandBy)
    reW00.toNat reW20.toNat

/-- The gas from the code after the CALL to the end. -/
def reCost1 : Nat := 3 + 3 + (3 + reC4) + 3 + 3 + reC5

/-- The call data of the call back: 68 bytes of the memory from 28. -/
def reData : ByteArray := memoryReadBytes reM3 reW1c.toNat reW44.toNat

/-! ## Closed facts -/

theorem reCost0_le : reCost0 ≤ 100 := by decide +kernel

theorem reCost0_pos : 1 ≤ reCost0 := by decide +kernel

theorem reCost1_le : reCost1 ≤ 30 := by decide +kernel

theorem reAsk_toNat : reAsk.toNat = 200000 := by decide +kernel

/-- The output of `RE` is the word 1. -/
theorem reOut_eq : reOut = wordBytes (1 : U256) := by decide +kernel

theorem reData_size : reData.size = 68 := by decide +kernel

theorem reData_sel : selector reData = 0xa9059cbb := by decide +kernel

/-- The first argument of the call back: the address word 0x2000. -/
theorem reData_arg1 : loadWord reData 4 32 = (0x2000 : U256) := by decide +kernel

/-- The second argument of the call back: the amount 1. -/
theorem reData_arg2 : loadWord reData 36 32 = (1 : U256) := by decide +kernel

/-- The CALL of `RE` grows no memory: its input range is inside, its output range is empty. -/
theorem re_ext : extendMemory reM3.size [(reW1c, reW44), (reW00, reW00)] = ⟨0, 0⟩ := by
  decide +kernel

/-! ## The frame, before and after the CALL -/

/-- From pc 0 to the CALL at pc 34: the seven arguments of the CALL on the stack, the call data
in memory. Every fork. -/
theorem re_prefix {gas : Nat} (hg : reCost0 ≤ gas) :
    Logic.HoareG fork (At RE message 0 [] .empty gas state substate)
      (At RE message 34 [reAsk, message.caller.toU256, reW00, reW1c, reW44, reW00, reW00] reM3
        (gas - reCost0) state substate) := by
  have hg' : 3 + 3 + (3 + reC1) + 3 + 3 + (3 + reC2) + 3 + 3 + (3 + reC3) + 3 + 3 + 3 + 3 + 3 +
      2 + 3 ≤ gas := hg
  have e : reCost0 = 3 + 3 + (3 + reC1) + 3 + 3 + (3 + reC2) + 3 + 3 + (3 + reC3) + 3 + 3 + 3 +
      3 + 3 + 2 + 3 := rfl
  step Gas.pushG (n := 4) (word := reSel) (by decide) (by decide) (by decide) rfl (by decide)
    (by omega) (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide) (by omega) (by stk_ok)
  step Gas.mstoreG (by decide) (by decide) (show 3 + reC1 ≤ gas - 3 - 3 by omega)
  step Gas.pushG (n := 2) (word := reDst) (by decide) (by decide) (by decide) rfl (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) by omega) (by stk_ok)
  step Gas.push1G (byte := 0x20) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 by omega) (by stk_ok)
  step Gas.mstoreG (by decide) (by decide)
    (show 3 + reC2 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 by omega)
  step Gas.push1G (byte := 0x01) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) by omega) (by stk_ok)
  step Gas.push1G (byte := 0x40) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 by omega) (by stk_ok)
  step Gas.mstoreG (by decide) (by decide)
    (show 3 + reC3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 by omega)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) by omega)
    (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 by omega)
    (by stk_ok)
  step Gas.push1G (byte := 0x44) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 by omega)
    (by stk_ok)
  step Gas.push1G (byte := 0x1c) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 - 3 by
      omega)
    (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 - 3 -
      3 by omega)
    (by stk_ok)
  step Gas.callerG (by decide) (by decide)
    (show 2 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 - 3 -
      3 - 3 by omega)
    (by stk_ok)
  step Gas.pushG (n := 3) (word := reAsk) (by decide) (by decide) (by decide) rfl (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 - 3 -
      3 - 3 - 2 by omega)
    (by stk_ok)
  exact Gas.Triple.lift (R' := Logic.StepG fork)
    (restate (by decide) rfl rfl
      (show gas - 3 - 3 - (3 + reC1) - 3 - 3 - (3 + reC2) - 3 - 3 - (3 + reC3) - 3 - 3 - 3 - 3 -
        3 - 2 - 3 = gas - reCost0 by omega) rfl rfl)

/-- From the code after the CALL (pc 35) to the end: the frame halts normally with the output
`reOut`, whatever the flag of the CALL, in the state and the substate it has. Every fork. -/
theorem re_tail {flag : U256} {gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hg : reCost1 ≤ gas) :
    Logic.SpecG fork (At RE message 35 [flag] reM3 gas st ss)
      (Halted false reOut (gas - reCost1) st ss) := by
  have hg' : 3 + 3 + (3 + reC4) + 3 + 3 + reC5 ≤ gas := hg
  step Gas.push1G (byte := 0x01) (by decide) (by decide) (by decide) (by omega) (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide) (by omega) (by stk_ok)
  step Gas.mstoreG (by decide) (by decide) (show 3 + reC4 ≤ gas - 3 - 3 by omega)
  step Gas.push1G (byte := 0x20) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC4) by omega) (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + reC4) - 3 by omega) (by stk_ok)
  exact haltGasL (specL (Gas.returnG (by decide) (by decide)
    (show reC5 ≤ gas - 3 - 3 - (3 + reC4) - 3 - 3 by omega)))
    (show gas - 3 - 3 - (3 + reC4) - 3 - 3 - reC5 =
      gas - (3 + 3 + (3 + reC4) + 3 + 3 + reC5) by omega)

/-! ## The gas of the CALL -/

/-- The 63/64 rule for a CALL with no value and no growth of memory, when the gas left covers the
price `E`: the message gets the gas asked, or all the gas left but one 64th. -/
theorem mcg_sub (htw : Fork.tangerineWhistle ≤ fork) {asked gas E : Nat} (h : E ≤ gas) :
    (messageCallGas fork 0 asked gas 0 E).subCall = min asked (gas - E - (gas - E) / 64) := by
  have hc : fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas := ⟨htw, h⟩
  have hs : (messageCallGas fork 0 asked gas 0 E).subCall =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) +
      (if (0 : U256) = 0 then 0 else CALL_STIPEND) := rfl
  have hx : maxMessageCallGas (gas - 0 - E) = gas - 0 - E - (gas - 0 - E) / 64 := rfl
  rw [hs, if_pos hc, if_pos (rfl : (0 : U256) = 0), hx]
  simp only [Nat.sub_zero, Nat.add_zero]

/-! ## The frame of `RE` -/

/-- What the CALL of `RE` sends: the message `msg` from the frame `cl`. The message goes to the
caller of the message of the frame, from its current target, with the code `c`, the call data
`reData` and no value, one level deeper. The frame `cl` has the state of the frame with two more
reads recorded. -/
def ReSends (message : Message fork) (state : State.TransactionState) (substate : Substate)
    (c : ByteArray) (cl : Evm fork Nat) (msg : Message fork) : Prop :=
  cl.state = (state.recordAccountRead message.caller).recordAccountRead message.currentTarget ∧
    cl.substate = { substate with
      accessedAddresses := substate.accessedAddresses.insert message.caller } ∧
    msg.reservoir = 0 ∧ msg.caller = message.currentTarget ∧
    msg.currentTarget = message.caller ∧ msg.target = some message.caller ∧
    msg.codeAddress = some message.caller ∧ msg.code = c ∧ msg.data = reData ∧ msg.value = 0 ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic

/-- THE FRAME OF `RE`, for every runner and every bound, from Berlin and before Glamsterdam. With
at least 5000 gas, a code `c` with no delegation for the caller of the message, and below the
depth limit: the loop of the interpreter goes to the CALL and hands the message `msg` to the
runner from the frame `cl` (`ReSends`); `msg` has less gas than the frame, and 200000 when the
frame has at least 210000. For every frame `child` that the runner gives for `msg`, the run of
the frame ends with no error, the output `reOut`, and the state that the CALL took in from
`child`. Each message that the frame sends (`Trace.Sent`) is `msg` from `cl`. -/
theorem re_call (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {c : ByteArray}
    (hcode : state.getCode (state.getAccount message.caller).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas : Nat} (hg : 5000 ≤ gas)
    {bound : Nat} (runChild : MessageRunner fork Nat bound) (hb : gas ≤ bound)
    {evm : Evm fork Nat} (start : At RE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ (cl : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧ msg.gas < gas ∧
      (210000 ≤ gas → msg.gas = 200000) ∧
      ReSends message state substate c cl msg ∧
      (∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild cl msg lt = .ok child →
        ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
          s.error = none ∧ s.output = reOut ∧
          s.state = (incorporateChild fork cl child.1).state) ∧
      ∀ (c' : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c' m →
        c' = cl ∧ m = msg := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hc0 := reCost0_le
  have hp0 := reCost0_pos
  have hc1 := reCost1_le
  obtain ⟨z, hr, hz⟩ := (Logic.HoareG.toHoare (re_prefix (fork := fork) (message := message)
    (state := state) (substate := substate) (gas := gas) (by omega))) evm start
  have hz' : At RE message 34 [reAsk, message.caller.toU256, reW00, reW1c, reW44, reW00, reW00]
      reM3 (gas - reCost0) state substate z := hz
  obtain ⟨zc, zj, zm, zp, zst, zmem, zg, zrun, zerr, zout, zs, zss⟩ := id hz'
  have hrun1 := runFrame_eq_of_reaches (bound := bound) (runChild := runChild)
    Step.gasHeld_le Step.runFrame_eq hr within
  have hstep : step fork z = callStep .call z := step_at_call hz' (by decide) (by decide)
  have hext : extendMemory z.memory.size [(reW1c, reW44), (reW00, reW00)] = ⟨0, 0⟩ := by
    rw [zmem]
    exact re_ext
  have h0 : (extendMemory z.memory.size [(reW1c, reW44), (reW00, reW00)]).cost = 0 := by
    rw [hext]
  have hto : toAddressMasked message.caller.toU256 = message.caller :=
    EthLib.Base.toAddressMasked_toU256 _
  have hEle : callBaseCost fork
        (decide (toAddressMasked message.caller.toU256 ∉ z.substate.accessedAddresses)) +
      routeCost fork (z.substate.accessedAddresses.insert (toAddressMasked message.caller.toU256))
        none ≤ 2600 := by
    have hr0 : routeCost fork
        (z.substate.accessedAddresses.insert (toAddressMasked message.caller.toU256)) none =
          0 := rfl
    rw [callBaseCost_of_berlin hfork hglam, hr0]
    split <;> omega
  generalize hEdef : callBaseCost fork
        (decide (toAddressMasked message.caller.toU256 ∉ z.substate.accessedAddresses)) +
      routeCost fork (z.substate.accessedAddresses.insert (toAddressMasked message.caller.toU256))
        none = E at hEle
  have hst0 : z.stack.val = reAsk :: message.caller.toU256 ::
      ((if CallKind.call.sendsValue then [0] else []) ++
        reW1c :: reW44 :: reW00 :: reW00 :: []) := zst
  obtain ⟨cl, msg, hsent, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
      s1, s2, m1, mr, m2, m3, mt, mca, mc, mdp, md, m5, mst, m6, m7, mb, mtx⟩ :=
    callStep_child_of_routes (kind := .call) (route := none) hfork hst0
      (by rw [zs, hto]; exact hcode)
      (show Routes fork z.state c none from fun hp => hdel hp)
      (by rw [zm]; exact hdepth)
      (by rw [h0, hEdef, zg]; omega)
  rw [h0, hEdef] at m1 c7
  have hEg : E ≤ z.gas := by rw [zg]; omega
  have hk := mcg_keep (fork := fork) htw (asked := reAsk.toNat) (gas := z.gas) (E := E) hEg
  have hmg : msg.gas = min 200000 (z.gas - E - (z.gas - E) / 64) := by
    rw [m1, mcg_sub htw hEg, reAsk_toNat]
  rw [zg] at hmg hk c7
  have hlt2 : msg.gas < gas := by omega
  have hclg : reCost1 ≤ cl.gas := by
    rw [c7]
    omega
  have hme : memoryExtend reM3 (ExtendMemory.expandBy ⟨0, 0⟩) = reM3 := memoryExtend_zero _
  -- the frame after the CALL, for every frame of the callee
  have key : ∀ (child after : Evm fork Nat),
      resumeCall fork cl 0 reW00 reW00 child = .ok after →
      At RE message 35 [(if child.error.isNone then 1 else 0)] reM3 after.gas
        (incorporateChild fork cl child).state (incorporateChild fork cl child).substate after ∧
      reCost1 ≤ after.gas := by
    intro child after hres
    obtain ⟨after', hres', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
      resumeCall_eq (fork := fork) (caller := cl) (child := child) (o := reW00) (osz := reW00)
        (by rw [c5]; simp [STACK_LIMIT])
    have e : after' = after := Except.ok.inj (hres'.symm.trans hres)
    subst e
    have hw : memoryWrite reM3 reW00.toNat
        (child.output.extract 0 (min reW00.toNat child.output.size)) = reM3 := by
      rw [show reW00.toNat = 0 from rfl]
      simp [memoryWrite]
    have hmem : after'.memory = reM3 := by
      rw [a6, c6, hext, zmem, hme]
      exact hw
    refine ⟨⟨a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
      by rw [a4, c4, zp], by rw [a5, c5], hmem, rfl, a8.trans (c8.trans zrun),
      a9.trans (c9.trans zerr), a10.trans (c10.trans zout), a11, a12⟩, ?_⟩
    rw [a7]
    omega
  refine ⟨cl, msg, Nat.lt_of_lt_of_le hlt2 hb, hlt2, fun h => by omega,
    ⟨by rw [s1, zs, zm, hto] <;> rfl, by rw [s2, zss, hto] <;> rfl, mr,
      m2.trans (by simp [zm]), m3.trans (by simp [hto]), mt.trans (by simp [hto]),
      mca.trans (by rw [hto] <;> rfl), mc, ?_, m5.trans (by simp), by rw [m6, zm],
      m7.trans (by simp [zm])⟩, ?_, ?_⟩
  · rw [md, hext, zmem]
    exact congrArg (fun mem => memoryReadBytes mem reW1c.toNat reW44.toNat) hme
  · intro lt child hch
    obtain ⟨after, hres, -⟩ :=
      resumeCall_eq (fork := fork) (caller := cl) (child := child.1) (o := reW00) (osz := reW00)
        (by rw [c5]; simp [STACK_LIMIT])
    obtain ⟨hat, hga⟩ := key child.1 after hres
    obtain ⟨w, hrun2⟩ : ∃ w : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild z
          (Nat.le_trans (hr.gasHeld_le Step.gasHeld_le) within) =
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after w :=
      ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) lt hch hres⟩
    obtain ⟨s, hrf, hH⟩ := (re_tail (fork := fork) (message := message) hga).runFrame
      (runChild := runChild) hat w
    obtain ⟨-, he, ho, -, hs, -⟩ := hH
    exact ⟨s, (hrun1.trans hrun2).trans hrf, by simpa using he, ho, hs⟩
  · intro c' m hs
    have hs1 := Trace.Sent.of_reaches hr hs
    rcases Trace.Sent.of_step_child (by rw [hstep]; exact hsent) hs1 with
      h | ⟨lt, child, after, hch, hres, hs2⟩
    · exact h
    · obtain ⟨hat, hga⟩ := key child.1 after hres
      exact absurd hs2 (Trace.not_sent_of_specG (re_tail (fork := fork) (message := message) hga)
        hat runChild c' m)

/-! ## Messages under the real runner -/

/-- From Paris, `processRunner` does run a message with no value, to a target that is no
precompile, whose frame has a specification to a normal halt (`Logic.SpecG`, the form of the path
theorems): it gives a frame with no error, with the state and the output of the
specification. -/
theorem spec_message_runs (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} {code out : ByteArray} {cost : Nat}
    {st' : State.TransactionState} {ss' : Substate} (lt : msg.gas < bound)
    (hcode : msg.code = code) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (spec : Logic.SpecG fork
      (At code msg 0 [] .empty msg.gas caller.state caller.substate.child)
      (Halted false out (msg.gas - cost) st' ss')) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.state = st' ∧ child.1.output = out := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  have spec' : Logic.SpecG fork
      (At code msg 0 [] .empty msg.gas (startState fork msg caller.state) caller.substate.child)
      (Halted false out (msg.gas - cost) st' ss') := by
    rw [hst]
    exact spec
  obtain ⟨stopped, hrf, hq⟩ := spec'.runFrame
    (bound := msg.gas) (runChild := processRunner fork msg.gas)
    (At.startFrame hcode (startState fork msg caller.state) caller.substate.child)
    (Nat.le_refl _)
  have hmap := processMessage_map_val ht noPre hrf
  obtain ⟨-, he, ho, -, hs, -⟩ := hq
  have he' : stopped.error = none := by simpa using he
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    have hc : child.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none he']
    exact ⟨child, rfl, by rw [hc]; exact he', by rw [hc, hs], by rw [hc, ho]⟩

/-- From Paris and before Glamsterdam, `processRunner` does run a message with no value whose
code is `RE`, to a target that is no precompile, with at least 210000 gas, from a state that
holds a code `c` (no delegation) for the caller of the message, when it runs the message of the
call back with no error (`inner`: only asked of the ONE message that the CALL of `RE` sends). The
run ends with no error and the output `reOut`, in the state that the call back left. -/
theorem re_message_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {caller : Evm fork Nat} {msg : Message fork} {to : Address} {c : ByteArray}
    (lt : msg.gas < bound) (hcode : msg.code = RE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (hc : caller.state.getCode (caller.state.getAccount msg.caller).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT) (hg : 210000 ≤ msg.gas)
    (inner : ∀ (cl : Evm fork Nat) (im : Message fork) (lt' : im.gas < msg.gas),
      ReSends msg caller.state caller.substate.child c cl im → im.gas = 200000 →
      ∃ ch, processRunner (Meter := Nat) fork msg.gas cl im lt' = .ok ch ∧ ch.1.error = none) :
    ∃ (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas })
      (cl : Evm fork Nat) (im : Message fork) (lt' : im.gas < msg.gas)
      (ch : { ch : Evm fork Nat // GasMeter.gasHeld ch.gas ≤ im.gas }),
      processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = reOut ∧
      ReSends msg caller.state caller.substate.child c cl im ∧ im.gas = 200000 ∧
      processRunner (Meter := Nat) fork msg.gas cl im lt' = .ok ch ∧ ch.1.error = none ∧
      child.1.state = ch.1.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  obtain ⟨cl, im, hlt, -, hgas, hsends, hrunAll, -⟩ :=
    re_call hfork hglam (message := msg) (state := startState fork msg caller.state)
      (substate := caller.substate.child) (c := c) (by rw [hst]; exact hc) hdel hdepth
      (gas := msg.gas) (by omega) (processRunner fork msg.gas) (Nat.le_refl _)
      (At.startFrame hcode (startState fork msg caller.state) caller.substate.child)
      (Nat.le_refl _)
  rw [hst] at hsends
  obtain ⟨ch, hch, hche⟩ := inner cl im hlt hsends (hgas hg)
  obtain ⟨s, hrf, hse, hso, hss⟩ := hrunAll hlt ch hch
  have hmap := processMessage_map_val ht noPre hrf
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    have hcs : child.1 = s := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none hse]
    exact ⟨child, cl, im, hlt, ch, rfl, by rw [hcs]; exact hse, by rw [hcs]; exact hso, hsends,
      hgas hg, hch, hche, by rw [hcs, hss, inc_state]⟩

/-! ## The events of the runs -/

/-- The frame that a message starts with `meter` gas is at pc 0 of its code. -/
theorem at_startFrame {code : ByteArray} (hcode : message.code = code) (meter : Nat) :
    At code message 0 [] .empty meter state substate
      (startFrame message state substate meter) :=
  ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- From Paris, the frame that `processMessage` runs for a message with no value starts from the
state and the substate of the message. -/
theorem frameOf_noValue (hparis : .paris ≤ fork) {meter : Nat} (hv : message.value = 0)
    {evm0 : Evm fork Nat} (fo : Trace.FrameOf message state substate meter evm0) :
    evm0 = startFrame message state substate meter := by
  obtain ⟨-, state1, hst, rfl⟩ := fo
  have ht : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) := fun h => h.2 hv
  have hsub : Trace.startSub message substate = substate := by
    unfold Trace.startSub
    rw [if_neg ht]
  have h2 : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hs1 : state1 = state := by
    unfold Trace.startSt at hst
    rw [if_neg ht] at hst
    exact (Except.ok.inj hst).symm.trans h2
  rw [hsub, hs1]

/-- The run of a call is clean when the run of its message is. -/
theorem cleanRun_call {L : Address} {CODE' : ByteArray} {Q : Message fork → Prop}
    {caller : Evm fork Nat} {msg : Message fork} (ht : msg.target.isSome = true)
    (h : Trace.Clean L CODE' Q msg caller.state caller.substate.child
      (GasMeter.start msg.gas msg.reservoir : Nat)) :
    Trace.CleanRun L CODE' Q caller msg := by
  intro e he
  cases he with
  | call _ ho => exact h e ho
  | create hn _ =>
    rw [hn] at ht
    cases ht

/-- From Paris, the run of a message with no value whose frame has a specification to a halt
(`Logic.SpecG`: the frame sends no message) is clean as soon as its own message is ok. -/
theorem clean_of_spec (hparis : .paris ≤ fork) {L : Address} {CODE' code : ByteArray}
    {Q : Message fork → Prop} {meter : Nat} {Post : Evm fork Nat → Prop}
    (hv : message.value = 0) (hcode : message.code = code)
    (spec : Logic.SpecG fork (At code message 0 [] .empty meter state substate) Post)
    (hq : message.currentTarget = L → Q message) :
    Trace.Clean L CODE' Q message state substate meter :=
  Trace.clean_of_no_sent
    (fun evm0 fo c m => by
      rw [frameOf_noValue hparis hv fo]
      exact Trace.not_sent_of_specG spec (at_startFrame hcode meter) _ c m) hq

/-- From Paris and before Glamsterdam, the run of a message with no value whose code is `RE` is
clean as soon as its own message is ok and the run of the ONE message that its CALL sends is
clean. -/
theorem re_clean (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {L : Address}
    {CODE' c : ByteArray} {Q : Message fork → Prop} {meter : Nat}
    (hcode : message.code = RE) (hv : message.value = 0)
    (hc : state.getCode (state.getAccount message.caller).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT) (hg : 5000 ≤ meter)
    (hm : meter ≤ message.gas)
    (hq : message.currentTarget = L → Q message)
    (inner : ∀ (cl : Evm fork Nat) (im : Message fork),
      ReSends message state substate c cl im → (210000 ≤ meter → im.gas = 200000) →
      Trace.CleanRun L CODE' Q cl im) :
    Trace.Clean L CODE' Q message state substate meter := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  intro e he
  cases he with
  | self => exact hq
  | sub fo hs hrun =>
    rw [frameOf_noValue hparis hv fo] at hs
    obtain ⟨cl, im, -, -, hgas, hsends, -, honly⟩ :=
      re_call hfork hglam hc hdel hdepth hg (processRunner fork message.gas) hm
        (at_startFrame hcode meter) hm
    obtain ⟨rfl, rfl⟩ := honly _ _ hs
    exact inner _ _ hsends hgas e hrun

end WbtcVerify.Sanity

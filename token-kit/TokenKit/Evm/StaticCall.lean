import TokenKit.Evm.Precompile
import EthLib.Execution.Proofs.Evm.Call.StaticMessage
import EthLib.Execution.Proofs.Evm.Logic.CallSteps

/-!
# STATICCALL into arbitrary code

A token whose `permit` checks an ERC-1271 signature makes a STATICCALL to the code of the owner:
code that the token does not know. This file says what such a call can do under EthLib's real
runner (`processRunner`), with NO assumption on the code of the callee.

- `quietPart`, `QuietStep`: the logs, the accounts to delete and the refund counter of a
  substate; a step that is a static step of EthLib and keeps them. `quietStep_*`: each
  instruction that gives the next frame is a quiet step in a static frame (the proofs follow
  EthLib's `staticStep_*` line by line).
- `QuietResult`, `quietResult_callStep`, `quietResult_step`: the step of a call, in a static
  frame or not, is quiet up to the frame of the caller, and the caller that takes in a quiet
  child is quiet; so is each step of a static frame.
- `quiet_runFrame`, `processMessage_quiet_static`: the run of a static frame, and the induction
  on the gas of a message: a static message emits no log, deletes no account and gives no
  refund, across all its nested calls, whether it fails or not, at every fork. (EthLib proves
  the state half: `processMessage_touchesOnly_static`, `processMessage_static`.)
- `staticMessage_of_callSends`: the message that a STATICCALL sends is a static message of
  EthLib, with or without an EIP-7702 delegation. `staticMessage_of_noValue`: the same from
  plain facts on a message.
- `static_ran`: from Paris, the frame that ends a static message under the real runner leaves
  every address as it was, up to the records of reads, and keeps the block.
- `static_ran_quiet`, `static_ran_logs`, `static_ran_incorporate`: that frame has no log, and
  the caller that takes it in has the logs, accounts to delete and refund counter it had.
- `staticcallStep_delegate_missing`, `staticcall_route_outcome`: every outcome of a run from a
  frame at a STATICCALL, for any runner, with no hypothesis on the code of the callee: an error;
  no message sent (depth limit), with the exact memory, no return data, and a state and
  substate that differ only by records of reads and warm addresses; or the message of
  `CallSends` along a route (the code itself, or the code of its EIP-7702 delegate) ran.
- `staticcall_kept`: the join. From Paris and before Glamsterdam, under the real runner, a
  STATICCALL into ANY code either ends the run with an error or goes on with a flag 0 or 1, the
  return data written to the output range, at most the gas of before, every address of the
  state as before (up to records of reads), the same block and the same logs.

No hypothesis on the callee: no `hdel` (a delegated owner is covered), no code, no gas bound.
Scope: `hparis` (before Paris a call touches its target) and `hglam` (the call rules of EthLib
used here are stated before Glamsterdam). Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address Bytes32 toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## The quiet part of a substate, and quiet steps -/

/-- The part of a substate that a static frame never changes: the logs, the accounts to delete
and the refund counter. (The accessed addresses and storage keys do change: a read warms them.) -/
def quietPart (s : Substate) : Array Blocks.Log × Std.ExtTreeSet Address × Int :=
  (s.logs, s.accountsToDelete, s.refundCounter)

/-- A quiet step: a static step of EthLib (the state is kept up to the records of reads, and the
message, the code, the block and the touched accounts are kept) that also keeps the quiet part
of the substate. -/
structure QuietStep (before after : Evm fork Nat) : Prop where
  /-- The step is a static step. -/
  static : StaticStep before after
  /-- The step keeps the logs, the accounts to delete and the refund counter. -/
  quiet : quietPart after.substate = quietPart before.substate

/-- A frame is a quiet step from itself. -/
theorem QuietStep.refl (evm : Evm fork Nat) : QuietStep evm evm := ⟨.refl _, rfl⟩

/-- Two quiet steps make one. -/
theorem QuietStep.trans {a b c : Evm fork Nat} (hab : QuietStep a b) (hbc : QuietStep b c) :
    QuietStep a c :=
  ⟨hab.static.trans hbc.static, hbc.quiet.trans hab.quiet⟩

/-- A step that keeps the message, the state and the substate is a quiet step. -/
theorem QuietStep.of_sameContext {a b : Evm fork Nat} (h : SameContext a b) : QuietStep a b :=
  ⟨.of_sameContext h, by rw [h.substate]⟩

/-- A change of the memory is a quiet step. -/
theorem QuietStep.withMemory (evm : Evm fork Nat) (memory : ByteArray) :
    QuietStep evm { evm with memory } := ⟨.withMemory _ _, rfl⟩

/-- A move of the program counter is a quiet step. -/
theorem QuietStep.advance {a b : Evm fork Nat} (h : QuietStep a b) (n : Nat := 1) :
    QuietStep a (Evm.advance b n) := ⟨h.static.advance n, h.quiet⟩

/-- A record of the read of an account is a quiet step. -/
theorem quietStep_recordAccountRead (evm : Evm fork Nat) (address : Address) :
    QuietStep evm (recordAccountRead evm address) := ⟨staticStep_recordAccountRead _ _, rfl⟩

/-- A record of the read of a storage key is a quiet step. -/
theorem quietStep_recordStorageRead (evm : Evm fork Nat) (address : Address) (key : Bytes32) :
    QuietStep evm (recordStorageRead evm address key) :=
  ⟨staticStep_recordStorageRead _ _ _, rfl⟩

/-- An access to an address is a quiet step. -/
theorem quietStep_accessAddress (evm : Evm fork Nat) (address : Address) :
    QuietStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  exact ⟨staticStep_accessAddress evm address, by rw [h]; rfl⟩

/-- An access to a storage key is a quiet step. -/
theorem quietStep_accessStorageKey (evm : Evm fork Nat) (address : Address) (key : Bytes32) :
    QuietStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  exact ⟨staticStep_accessStorageKey evm address key, by rw [h]; rfl⟩

/-- An exceptional halt is a quiet step. -/
theorem quietStep_exceptionalHalt (evm : Evm fork Nat) (e : EvmError) :
    QuietStep evm (exceptionalHalt evm e) := ⟨staticStep_exceptionalHalt _ _, rfl⟩

/-! ## The instructions that give the next frame

The proofs follow EthLib's `staticStep_*` proofs line by line, with the quiet part added. -/

/-- BALANCE is a quiet step. -/
theorem quietStep_balanceStep {evm after : Evm fork Nat} (h : balanceStep evm = .ok after) :
    QuietStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QuietStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QuietStep.of_sameContext (chargeGas_sameContext h3))).trans
    (quietStep_recordAccountRead _ _)).trans
    (QuietStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODESIZE is a quiet step. -/
theorem quietStep_extcodesizeStep {evm after : Evm fork Nat}
    (h : extcodesizeStep evm = .ok after) : QuietStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨code, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QuietStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QuietStep.of_sameContext (chargeGas_sameContext h3))).trans
    (quietStep_recordAccountRead _ _)).trans
    (QuietStep.of_sameContext (pushWord_sameContext h5)) |>.advance

/-- EXTCODEHASH is a quiet step. -/
theorem quietStep_extcodehashStep {evm after : Evm fork Nat}
    (h : extcodehashStep evm = .ok after) : QuietStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QuietStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QuietStep.of_sameContext (chargeGas_sameContext h3))).trans
    (quietStep_recordAccountRead _ _)).trans
    (QuietStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODECOPY is a quiet step. -/
theorem quietStep_extcodecopyStep {evm after : Evm fork Nat}
    (h : extcodecopyStep evm = .ok after) : QuietStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have ha : QuietStep e4 e5 := by
    have := quietStep_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((QuietStep.of_sameContext (popWord_sameContext h1)).trans
    (QuietStep.of_sameContext (popWord_sameContext h2))).trans
    (QuietStep.of_sameContext (popWord_sameContext h3))).trans
    (QuietStep.of_sameContext (popWord_sameContext h4))).trans ha).trans
    (QuietStep.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
    (quietStep_recordAccountRead _ _)).trans (QuietStep.withMemory _ _) |>.advance

/-- Each instruction that reads another account is a quiet step. -/
theorem quietStep_accountStep {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Nat}
    (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact quietStep_balanceStep h
  case extcodesize => subst hstep; exact quietStep_extcodesizeStep h
  case extcodecopy => subst hstep; exact quietStep_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (quietStep_recordAccountRead _ _).trans
        (QuietStep.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact quietStep_extcodehashStep h
    · cases hstep

/-- SLOAD is a quiet step. -/
theorem quietStep_sloadStep {evm after : Evm fork Nat} (h : sloadStep evm = .ok after) :
    QuietStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((QuietStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QuietStep.of_sameContext (chargeGas_sameContext h3))).trans
    (quietStep_recordStorageRead _ _ _)).trans
    (QuietStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- SSTORE in a static frame is a quiet step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem quietStep_sstoreStep_of_isStatic {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : sstoreStep evm = .ok after) :
    QuietStep evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
  have c2 := (QuietStep.of_sameContext (popWord_sameContext h1)).trans
    (QuietStep.of_sameContext (popWord_sameContext h2))
  have m2 : e2.message = evm.message :=
    (popWord_sameContext h2).message.trans (popWord_sameContext h1).message
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
      rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      rw [hpair] at hacc
      simp only [hpair] at h
      obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
      have m5 : e5.message = evm.message := by
        obtain ⟨_, -, h5⟩ := EthLib.Base.bind_ok_iff.mp h5
        cases h5
        rw [(chargeGas_sameContext h4).message]
        cases hacc
        exact m2
      simp [m5, static, throw, throwThe, MonadExceptOf.throw] at h
    · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      have ha : QuietStep e2 e3 := by
        have := quietStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
        rwa [hpair] at this
      exact ((c2.trans ha).trans (quietStep_recordStorageRead _ _ _)).trans
        (quietStep_exceptionalHalt _ _)

/-- Each instruction that uses storage is a quiet step in a static frame. -/
theorem quietStep_storageStep_of_isStatic {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : storageStep op = some step) {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact quietStep_sloadStep h
  case sstore => subst hstep; exact quietStep_sstoreStep_of_isStatic static h

/-- SELFDESTRUCT in a static frame is a quiet step.

Before Glamsterdam it halts the frame with its reads.

From Glamsterdam it fails before any read. -/
theorem quietStep_selfdestructStep_of_isStatic {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : selfdestructStep fork evm = .ok after) :
    QuietStep evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  have c := ((QuietStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (quietStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeStateGas_sameContext h4).message, (chargeGas_sameContext h3).message]
      exact c.static.message
    unfold finishSelfdestruct at h
    simp [m4, static] at h
  · exact c.trans (quietStep_exceptionalHalt _ _)

/-- Each instruction of transient storage is a quiet step in a static frame. -/
theorem quietStep_transientStorageStep_of_isStatic {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload => exact QuietStep.of_sameContext (tloadStep_sameContext h)
  case tstore => exact absurd h (tstoreStep_ne_ok_of_isStatic static)

/-- RETURN and REVERT are quiet steps. -/
theorem quietStep_returnOpStep {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Nat}
    (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact QuietStep.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep; exact QuietStep.of_sameContext (revertStep_sameContext h)
    · cases hstep

/-- The instruction of SELFDESTRUCT is a quiet step in a static frame. -/
theorem quietStep_selfdestructOpStep_of_isStatic {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact quietStep_selfdestructStep_of_isStatic static h

/-- The instructions of LOG are quiet steps in a static frame, as none completes. -/
theorem quietStep_logOpStep_of_isStatic {op : Op}
    {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : logOpStep op = some step) {evm after : Evm fork Nat}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) : QuietStep evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact absurd h (logStep_ne_ok_of_isStatic static)

/-- Each instruction that gives the next frame is a quiet step in a static frame. -/
theorem quietStep_instruction_of_isStatic {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {evm after : Evm fork Nat}
    (hrun : instruction fork op = some run) (static : evm.message.isStatic = true)
    (h : run evm = .ok after) : QuietStep evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact QuietStep.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact QuietStep.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact QuietStep.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact quietStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact QuietStep.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact quietStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact quietStep_storageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hrun
  · exact quietStep_transientStorageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hf
  · exact quietStep_logOpStep_of_isStatic hf static h
  · exact quietStep_selfdestructOpStep_of_isStatic hf static h


/-! ## The calls -/

/-- The pops of the operands of a call are a static step.

A call that sends no value pops none. -/
theorem quietStep_popCallOperands {kind : CallKind} {evm after : Evm fork Nat}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    QuietStep evm after ∧ (kind.sendsValue = false → call.value = 0) := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have p3 : QuietStep e2 e3 ∧ (kind.sendsValue = false → v = 0) := by
    unfold popCallValue at h3
    split at h3
    · exact ⟨QuietStep.of_sameContext (popWord_sameContext h3), fun h => by simp_all⟩
    · cases h3
      exact ⟨QuietStep.refl _, fun _ => rfl⟩
  refine ⟨?_, p3.2⟩
  exact (((((((QuietStep.of_sameContext (popWord_sameContext h1)).trans
    (QuietStep.of_sameContext (popWord_sameContext h2))).trans p3.1).trans
    (QuietStep.of_sameContext (popWord_sameContext h4))).trans
    (QuietStep.of_sameContext (popWord_sameContext h5))).trans
    (QuietStep.of_sameContext (popWord_sameContext h6))).trans
    (QuietStep.of_sameContext (popWord_sameContext h7)))

/-- The access to a delegate is a quiet step. -/
theorem quietStep_accessDelegation {evm after : Evm fork Nat} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    QuietStep evm after := by
  obtain ⟨code, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
    cases h
    exact (quietStep_accessAddress _ _).trans (quietStep_recordAccountRead _ _)
  · cases h
    exact QuietStep.refl _

/-- The payment of a call is a quiet step. -/
theorem quietStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Nat}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    QuietStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := EthLib.Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := EthLib.Base.bind_ok_iff.mp h
    cases h
    exact ((QuietStep.of_sameContext (chargeGas_sameContext h1)).trans
      (QuietStep.of_sameContext (chargeStateGas_sameContext h2))).trans
      (QuietStep.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
    cases h
    exact QuietStep.of_sameContext (chargeGas_sameContext h1)

/-- A call that runs no message is a quiet step. -/
theorem quietStep_skipCall {evm after : Evm fork Nat} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : QuietStep evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- The caller that resumes after a child has the substate that `incorporateChild` gives. -/
theorem substate_resumeCall {caller child after : Evm fork Nat} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.substate = (incorporateChild fork caller child).substate := by
  obtain ⟨e, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  show e.substate = _
  rw [hp.substate]
  split <;> rfl

/-- A caller that takes in a child whose quiet part is that of a fresh child substate (no log,
no refund, the accounts to delete of the caller) keeps its own quiet part, whether the child
failed or not. -/
theorem quietPart_incorporateChild {caller child : Evm fork Nat}
    (h : quietPart child.substate = quietPart caller.substate.child) :
    quietPart (incorporateChild fork caller child).substate = quietPart caller.substate := by
  have h1 : child.substate.logs = #[] := congrArg Prod.fst h
  have h2 : child.substate.accountsToDelete = caller.substate.accountsToDelete :=
    congrArg (fun p => p.2.1) h
  have h3 : child.substate.refundCounter = 0 := congrArg (fun p => p.2.2) h
  unfold incorporateChild
  split
  · simp only [quietPart, h1, h2, h3, insertMany_self, Array.append_empty, Int.add_zero]
  · rfl

/-- What the step of a call gives, static frame or not.

A step that gives the next frame (the call sent no message) is a quiet step.

A step that sends a message is a quiet step up to the frame of the caller; and when the frame
that ends the message has the quiet part of a fresh child substate, the frame that resumes has
the quiet part of the frame before the call. -/
def QuietResult (evm : Evm fork Nat) : StepResult fork Nat → Prop
  | .next after => QuietStep evm after
  | .child caller _ resume => QuietStep evm caller ∧
      ∀ child after, resume child = .ok after →
        quietPart child.substate = quietPart caller.substate.child →
        quietPart after.substate = quietPart evm.substate

/-- A frame reached by a quiet step gives the same result. -/
theorem QuietResult.lift {evm evm' : Evm fork Nat} {result : StepResult fork Nat}
    (h : QuietStep evm evm') (r : QuietResult evm' result) : QuietResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    exact ⟨h.trans r.1, fun child after hres hq => (r.2 child after hres hq).trans h.quiet⟩

/-- A call that has paid gives a quiet result. -/
theorem quietResult_genericCall {evm : Evm fork Nat} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Nat}
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    QuietResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact (⟨⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩, rfl⟩ : QuietStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans
        (quietStep_skipCall hs)
  · cases h
    refine ⟨⟨⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩, rfl⟩, ?_⟩
    intro child after hres hq
    rw [substate_resumeCall hres]
    exact quietPart_incorporateChild hq

/-- A paid call gives a quiet result. -/
theorem quietResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Nat} {result : StepResult fork Nat}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    QuietResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : QuietStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩, rfl⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have refill : QuietStep (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget)
          (refillStateGas (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) := ⟨⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩, rfl⟩
      exact (pre.trans refill).trans (quietStep_skipCall hs)
  · exact QuietResult.lift pre (quietResult_genericCall h)

/-- Each call gives a quiet result, in a static frame or not: before its message runs, a call
changes the state only by records of reads, and keeps the logs. -/
theorem quietResult_callStep {kind : CallKind} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (h : callStep kind evm = .ok result) :
    QuietResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := EthLib.Base.bind_ok_iff.mp h
  obtain ⟨c1, -⟩ := quietStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : QuietStep e1 e2 := by
    have := quietStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : QuietStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (quietStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := EthLib.Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := EthLib.Base.bind_ok_iff.mp h
    have s4 : QuietStep evm e4 := s3.trans (quietStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := EthLib.Base.bind_ok_iff.mp h
      have s5 : QuietStep evm e5 := s4.trans (quietStep_payCall h5)
      exact QuietResult.lift s5 (quietResult_finishCall h)
    · exact s4.trans (quietStep_exceptionalHalt _ _)
  · exact s3.trans (quietStep_exceptionalHalt _ _)

/-- Each instruction that may send a message gives a quiet result in a static frame: a call
does, and a creation never completes. -/
theorem quietResult_messageInstruction {op : Op}
    {run : Evm fork Nat → Except EvmError (StepResult fork Nat)} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (hrun : messageInstruction fork op = some run)
    (static : evm.message.isStatic = true) (h : run evm = .ok result) :
    QuietResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Nat) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact quietResult_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact quietResult_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact absurd h (createStep_ne_ok_of_isStatic static))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact absurd h (createStep_ne_ok_of_isStatic static)
         · cases hrun)

/-- A step of a static frame gives a quiet result. -/
theorem quietResult_step {evm : Evm fork Nat} {result : StepResult fork Nat}
    (static : evm.message.isStatic = true) (h : step fork evm = .ok result) :
    QuietResult evm result := by
  unfold step at h
  split at h
  · rename_i hlt
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Nat → Except EvmError (Evm fork Nat)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact quietStep_instruction_of_isStatic hop static hr
      · split at h
        · rename_i hcall
          exact quietResult_messageInstruction hcall static h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact QuietStep.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

/-! ## The run of a static frame, and the induction on the gas of a message -/

section Loop

variable {stepf : Evm fork Nat → Except EvmError (StepResult fork Nat)}
  {decreases : ∀ {evm result}, evm.running = true → stepf evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A whole run of a static frame keeps the quiet part of the substate.

The step must give quiet steps, and EthLib's static touch children with a quiet result, from a
static frame. The runner must end each static child as EthLib's `staticTouchStep_runFrame` asks
(a state that differs by touches), with the quiet part of a fresh child substate. -/
theorem quiet_runFrame
    (next : ∀ {evm after : Evm fork Nat}, StaticFrame evm → stepf evm = .ok (.next after) →
      QuietStep evm after)
    (child : ∀ {evm caller : Evm fork Nat} {message : Message fork}
      {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}, StaticFrame evm →
      stepf evm = .ok (.child caller message resume) →
      StaticTouchChild evm caller message resume ∧
        QuietResult evm (.child caller message resume))
    (runs : ∀ {caller : Evm fork Nat} {message : Message fork} {lt : message.gas < bound}
      {c : Evm fork Nat} {used : GasMeter.gasHeld c.gas ≤ message.gas},
      StaticFrame caller → StaticMessage caller.state message →
      runChild caller message lt = .ok ⟨c, used⟩ →
      (∃ touched, TouchesOnly touched caller.state c.state ∧
        c.state.parent = caller.state.parent ∧
        ∀ address ∈ touched, c.error = none ∧ fork < .paris ∧
          ((.spuriousDragon ≤ fork → address ∈ c.substate.touchedAccounts) ∨
            address = c.message.currentTarget)) ∧
      quietPart c.substate = quietPart caller.substate.child)
    {evm after : Evm fork Nat} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hf : StaticFrame evm)
    (h : runFrame stepf decreases bound runChild evm within = .ok after) :
    quietPart after.substate = quietPart evm.substate := by
  fun_induction runFrame stepf decreases bound runChild evm within
  case case1 => cases h
  case case2 => cases h; rfl
  case case3 =>
    rename_i result _ ih
    have n := next hf result
    exact (ih (StaticFrame.of_staticStep n.static hf) h).trans n.quiet
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; rfl
  case case7 =>
    obtain ⟨⟨c0, hmsg, hres⟩, q0, hq⟩ := child hf ‹stepf _ = .ok (.child _ _ _)›
    obtain ⟨⟨tc, kept, parent, hrec⟩, qc⟩ :=
      runs (StaticFrame.of_staticStep c0 hf) hmsg ‹runChild _ _ _ = .ok _›
    have n := hres tc _ _ (by assumption) kept parent hrec
    have qn := hq _ _ (by assumption) qc
    exact (‹StaticFrame _ → runFrame _ _ _ _ _ _ = Except.ok after →
      quietPart _ = quietPart _› (StaticFrame.of_touchStep n hf) h).trans qn
  case case8 => cases h; rfl

end Loop

/-- A precompile keeps the quiet part of the substate. -/
theorem quiet_runPrecompile {address : Nat} {evm after : Evm fork Nat}
    (h : runPrecompile fork address evm = some after) :
    quietPart after.substate = quietPart evm.substate := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    rfl
  · split at h
    · cases h
      rfl
    · cases h
      rfl

/-- A static message ends with the quiet part of the substate it started from: no new log, the
same accounts to delete, the same refund counter. That holds whatever its code does, however
deep its calls, whether it fails or not, at every fork.

It is the induction on the gas of the message, next to EthLib's
`processMessage_touchesOnly_static` (which gives the state). -/
theorem processMessage_quiet_static :
    ∀ (n : Nat) (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Nat) (held : GasMeter.gasHeld meter ≤ message.gas),
      message.gas = n → StaticMessage state message →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
      quietPart ended.val.substate = quietPart substate := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message state substate meter held hn hmsg ended h
    rw [processMessage] at h
    obtain ⟨ended0, hdo, rolled⟩ := EthLib.Base.map_ok_iff.mp h
    obtain ⟨t0, ht0, hpar0, hrec0⟩ := touchesOnly_startState message state
    have hmsg0 : StaticMessage (startState fork message state) message :=
      StaticMessage.of_touchesOnly ht0 hmsg
    -- a value that a static message moves goes to its own sender: no transfer log
    have hqT : message.shouldTransferValue = true ∧ message.value ≠ 0 →
        quietPart { substate with
          logs := pushTransferLog fork substate.logs message.caller message.currentTarget
            message.value } = quietPart substate := by
      intro ht
      obtain ⟨hcaller, -⟩ := hmsg.2.2.2 ht.1 ht.2
      simp only [quietPart]
      rw [hcaller]
      simp [pushTransferLog]
    have hq0 : quietPart (if message.shouldTransferValue = true ∧ message.value ≠ 0 then
        { substate with
          logs := pushTransferLog fork substate.logs message.caller message.currentTarget
            message.value } else substate) = quietPart substate := by
      split
      · exact hqT ‹_›
      · rfl
    have core : quietPart ended0.val.substate = quietPart substate := by
      dsimp only at hdo
      split at hdo
      all_goals obtain ⟨state1, hm, hdo⟩ := EthLib.Base.bind_ok_iff.mp hdo
      all_goals
        have hS1 : StaticMessage state1 message := by
          first
          | (have ht := ‹message.shouldTransferValue = true ∧ message.value ≠ 0›
             have hm' := EthLib.Base.mapError_ok_iff.mp hm
             obtain ⟨hcaller, hcode⟩ := hmsg0.2.2.2 ht.1 ht.2
             rw [hcaller] at hm'
             have so := TransactionState.sameOutside_moveEther_self hcode hm'
             exact StaticMessage.of_sameOutside so hmsg0)
          | (cases hm
             exact hmsg0)
      all_goals
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            have q := quiet_runFrame (hf := StaticFrame.start hS1 _ _) (h := hrun)
              (fun {evm' after'} hf' hstep => quietResult_step hf'.1 hstep)
              (fun {evm' caller' message' resume'} hf' hstep =>
                ⟨staticTouchResult_step hf'.1 hf'.2.1 hf'.2.2 hstep,
                  quietResult_step hf'.1 hstep⟩)
              (by
                intro caller' message' lt c used _ hm hrun'
                split at hrun'
                · obtain ⟨tc, htc, hpc, hmc, hrecc⟩ :=
                    processMessage_touchesOnly_static message'.gas message' caller'.state _ _ _
                      rfl hm ⟨c, used⟩ hrun'
                  refine ⟨⟨tc, htc, hpc, fun addr ha => ?_⟩,
                    ih message'.gas (by omega) message' caller'.state _ _ _ rfl hm ⟨c, used⟩
                      hrun'⟩
                  obtain ⟨herr, hlt, hmem⟩ := hrecc addr ha
                  exact ⟨herr, hlt, by rwa [hmc]⟩
                · have := hm.2.1
                  simp_all)
            exact q.trans (by first | exact hq0 | exact hqT ‹_› | rfl)
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            first | exact hq0 | exact hqT ‹_› | rfl
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact (quiet_runPrecompile hrp).trans (by first | exact hq0 | exact hqT ‹_› | rfl)
            · cases hdo
              first | exact hq0 | exact hqT ‹_› | rfl
    have hval := congrArg Subtype.val rolled
    simp only at hval
    rw [← hval]
    unfold rollbackOnError
    split
    · exact core
    · exact core

/-! ## A static message under the real runner -/

/-- The message that a STATICCALL sends along a route (`CallSends`), for a callee whose code the
state holds, is a static message of EthLib from the state of the caller: it is static, it is a
call, it sends no value, and when it has code, the account called holds code (its code hash is
not the empty one: the code found there is the code that runs, or a delegation to it). -/
theorem staticMessage_of_callSends {asked to i isz o osz : U256} {calleeCode : ByteArray}
    {route : Route} {caller : Evm fork Nat} {msg : Message fork}
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hroute : Routes fork state calleeCode route)
    (hsend : CallSends .staticcall message memory gas state substate asked to i isz o osz
      calleeCode route caller msg) :
    StaticMessage caller.state msg := by
  obtain ⟨cs, -, -, -, -, ccur, ctarget, -, ccode, -, -, cvalue, -, -, cstatic, -, -⟩ := hsend
  have ccur' : msg.currentTarget = toAddressMasked to := by simpa using ccur
  have cvalue' : msg.value = 0 := by simpa using cvalue
  refine ⟨by rw [cstatic]; rfl, by rw [ctarget]; rfl, ?_, fun _ hv => absurd cvalue' hv⟩
  intro nonempty hh
  have hacc : caller.state.getAccount msg.currentTarget =
      state.getAccount (toAddressMasked to) := by
    rw [cs, ccur']
    cases route <;> rfl
  rw [hacc] at hh
  have hempty : calleeCode = ByteArray.empty := by
    rw [hh] at hcode
    simp [State.TransactionState.getCode] at hcode
    exact hcode.symm
  subst hempty
  rcases route with _ | ⟨d, c'⟩
  · exact nonempty (by rw [ccode]; rfl)
  · have h := hroute.2.1
    rw [delegatedAddress_empty] at h
    cases h

/-- A message that is static, is a call, sends no value, and whose code (when it has any) runs at
an account that holds code, is a static message of EthLib. -/
theorem staticMessage_of_noValue {st : State.TransactionState} {msg : Message fork}
    {target : Address} (hstatic : msg.isStatic = true) (htarget : msg.target = some target)
    (hvalue : msg.value = 0) (hcode : StaticCode st msg) : StaticMessage st msg :=
  ⟨hstatic, by rw [htarget]; rfl, hcode, fun _ hv => absurd hvalue hv⟩

/-- From Paris, under EthLib's real runner: the frame `child` that ends a static message leaves
every address as the caller had it (account, storage and transient storage), up to the records
of reads, and keeps the block. Whatever the code of the message does, however deep its calls,
whether it fails or not. -/
theorem static_ran (hparis : .paris ≤ fork) {bound : Nat} {caller child : Evm fork Nat}
    {msg : Message fork} (hran : Ran (processRunner fork bound) caller msg child)
    (hmsg : StaticMessage caller.state msg) :
    State.TransactionState.SameOutside [] caller.state child.state ∧
      child.state.parent = caller.state.parent := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hmsg.2.1
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  rw [hp] at hrun
  exact processMessage_static hparis msg.gas msg caller.state _ _ _ rfl hmsg child' hrun

/-- Under EthLib's real runner, at every fork: the frame `child` that ends a static message has
the quiet part of the substate of a fresh child. -/
theorem static_ran_quiet {bound : Nat} {caller child : Evm fork Nat} {msg : Message fork}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hmsg : StaticMessage caller.state msg) :
    quietPart child.substate = quietPart caller.substate.child := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hmsg.2.1
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, ht]
  rw [hp] at hrun
  exact processMessage_quiet_static msg.gas msg caller.state _ _ _ rfl hmsg child' hrun

/-- Under EthLib's real runner, at every fork: the frame `child` that ends a static message has
no log, the accounts to delete of its caller, and no refund. Whatever the code of the message
does, however deep its calls, whether it fails or not. -/
theorem static_ran_logs {bound : Nat} {caller child : Evm fork Nat} {msg : Message fork}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hmsg : StaticMessage caller.state msg) :
    child.substate.logs = #[] ∧
      child.substate.accountsToDelete = caller.substate.accountsToDelete ∧
      child.substate.refundCounter = 0 := by
  have h := static_ran_quiet hran hmsg
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

/-- Under EthLib's real runner, at every fork: a caller that takes in the frame that ends a
static message has the logs, the accounts to delete and the refund counter it had. -/
theorem static_ran_incorporate {bound : Nat} {caller child : Evm fork Nat} {msg : Message fork}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hmsg : StaticMessage caller.state msg) :
    (incorporateChild fork caller child).substate.logs = caller.substate.logs ∧
      (incorporateChild fork caller child).substate.accountsToDelete =
        caller.substate.accountsToDelete ∧
      (incorporateChild fork caller child).substate.refundCounter =
        caller.substate.refundCounter := by
  have h := quietPart_incorporateChild (static_ran_quiet hran hmsg)
  exact ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

/-! ## STATICCALL, with or without an EIP-7702 delegation -/

/-- Before Glamsterdam and from Pectra, a STATICCALL to an account whose code delegates to an
address whose code the state fails to give: the step fails. -/
theorem staticcallStep_delegate_missing (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hpectra : .pectra ≤ fork)
    {evm : Evm fork Nat} {g a i isz o osz : U256} {rest : List U256} {c : ByteArray}
    {d : Address} {e : State.StateError}
    (hst : evm.stack.val = g :: a :: i :: isz :: o :: osz :: rest)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash = .ok c)
    (hdel : delegatedAddress c = some d)
    (hmissing : evm.state.getCode (evm.state.getAccount d).codeHash = .error e) :
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
  simp only at hmissing hcode ⊢
  have hab : (EvmError.state e).aborts = true := rfl
  refine .inl ⟨.state e, ?_⟩
  simp [hab, callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop,
    bind, Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hcode, hdel, hpectra, hmissing, Except.mapError,
    keepReads]

/-- A write of no byte leaves the memory as it was. -/
theorem memoryWrite_empty_extract (m : ByteArray) (o n : Nat) :
    memoryWrite m o (ByteArray.empty.extract 0 (min n ByteArray.empty.size)) = m := by
  simp [memoryWrite]

/-- The state of the caller of a call along a route reads as the state before the call: only
reads were recorded. -/
theorem callSends_state {kind : CallKind} {asked to i isz o osz : U256} {calleeCode : ByteArray}
    {route : Route} {caller : Evm fork Nat} {msg : Message fork}
    (hsend : CallSends kind message memory gas state substate asked to i isz o osz calleeCode
      route caller msg) :
    State.TransactionState.SameOutside [] state caller.state ∧
      caller.state.parent = state.parent ∧
      quietPart caller.substate = quietPart substate := by
  obtain ⟨cs, css, -⟩ := hsend
  rw [cs, css]
  rcases route with _ | ⟨d, c'⟩ <;>
    exact ⟨fun _ _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩, rfl, rfl⟩

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the
interpreter loop from the frame at a STATICCALL that returns a frame `s`. No assumption on the
code of the callee, which may be an EIP-7702 delegation. One of three holds.

1. `s` has an error (the state fails to give the code of the callee or of its delegate, or the
   gas is below the price of the call).
2. No message was sent (depth limit): the loop went on from the next opcode with 0 pushed, the
   memory grown for both ranges, no return data, less gas, a state that differs only by records
   of reads, and the same logs, accounts to delete and refund counter.
3. The runner ran the message of `CallSends` along a route to a frame `child`, and the loop went
   on from the next opcode with the flag of `child` pushed, the start of its output written to
   the output range, its output as return data, at most the gas of before, and its state taken
   in. -/
theorem staticcall_route_outcome (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {rd : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : Logic.At code message pc
      (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    (∃ g st ss after,
      Logic.At code message (pc + 1) (0 :: rest)
        (memoryExtend memory (extendMemory memory.size
          [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
        g st ss .empty after ∧
      g ≤ gas ∧ State.TransactionState.SameOutside [] state st ∧ st.parent = state.parent ∧
      quietPart ss = quietPart substate ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s) ∨
    ∃ calleeCode route caller msg child after g,
      state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode ∧
      Routes fork state calleeCode route ∧
      CallSends .staticcall message memory gas state substate asked to inputStart inputSize
        outputStart outputSize calleeCode route caller msg ∧
      Ran runChild caller msg child ∧ child.gas ≤ msg.gas ∧
      Logic.At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat (child.output.extract 0 (min outputSize.toNat child.output.size)))
        g (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
        child.output after ∧
      g ≤ gas ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .staticcall evm := step_at_staticcall hfork start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss, hrd⟩ := id start
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have fails : StepFails (callStep .staticcall evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have hst0 : evm.stack.val = asked :: to ::
      ((if CallKind.staticcall.sendsValue then [0] else []) ++
        inputStart :: inputSize :: outputStart :: outputSize :: rest) := hst
  -- the code of the callee
  rcases hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash with e | calleeCode
  · exact .inl (fails (staticcallStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
      .ok calleeCode := by rw [hs]; exact hcode
  -- the route: the code itself, or the code of the delegate
  have hroutes : (∃ route, Routes fork state calleeCode route) ∨
      StepFails (callStep .staticcall evm) := by
    by_cases hpectra : .pectra ≤ fork
    · rcases hdel : delegatedAddress calleeCode with _ | d
      · exact .inl ⟨none, fun _ => hdel⟩
      · rcases hd : state.getCode (state.getAccount d).codeHash with e | c'
        · exact .inr (staticcallStep_delegate_missing hfork hglam hpectra hst hcode' hdel
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
      · obtain ⟨after, ⟨caller, msg, child, hsend, hch, hle, hat⟩, w, h⟩ :=
          HoareOn.runFrame_of_ok
            (callKindRoute (kind := .staticcall) (callee := Ran runChild) (asked := asked)
              (inputStart := inputStart) (inputSize := inputSize) (outputStart := outputStart)
              (outputSize := outputSize) (rest := rest) (returnData := rd) (route := route)
              hfork hlt hbyte
              (ofByte_of_decode (op := .staticcall) rfl (Nat.le_trans (by decide) hfork))
              instruction_staticcall
              (messageInstruction_staticcall (Nat.le_trans (by decide) hfork))
              hcode hroute hdepth hgas)
            (meetsOk_ran runChild) start within hrun
        refine .inr (.inr ⟨calleeCode, route, caller, msg, child, after, _, rfl, hroute, hsend,
          hch, hle, hat, ?_, w, h⟩)
        have h1 := cost_add_memoryCost_le (fork := fork) (value := 0) (gas := asked.toNat)
          (stipend := CALL_STIPEND) htw hgas
        have h2 : (messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to))
                route)).subCall ≤ (messageCallGas fork 0 asked.toNat gas
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked to ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked to))
                route)).cost := by
          simp [messageCallGas]
        have h3 := hsend.2.2.1
        omega
      · obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
          callStep_deep_of_routes (kind := .staticcall) (route := route) hfork hst0 hcode' hroute'
            (by rw [hm]; omega) (by rw [hmem, hss, hg]; exact hgas)
        have q : QuietStep evm after := quietResult_callStep hn
        rw [← hstep] at hn
        rw [runFrame_of_step_eq_next hrunning hn] at hrun
        refine .inr (.inl ⟨after.gas, after.state, after.substate, after,
          ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, by rw [a10, hmem], rfl,
            a6.trans hrunning, a7.trans herr, a8.trans hout, rfl, rfl, a9⟩, ?_, ?_, ?_, ?_,
          _, hrun⟩)
        · rw [a11, hg]
          exact Nat.sub_le _ _
        · rw [← hs]
          exact q.static.state
        · rw [← hs]
          exact q.static.parent
        · rw [← hss]
          exact q.quiet
    · refine .inl (fails (callStep_fails_of_routes (kind := .staticcall) (route := route) hfork
        hst0 hcode' hroute' ?_))
      rw [hmem, hss, hg]
      omega
  · exact .inl (fails hfail)

/-! ## The join: a STATICCALL into arbitrary code changes no storage and emits no log -/

/-- From Paris and before Glamsterdam, under EthLib's real runner, with NO assumption on the code
of the callee (it may be anything, also an EIP-7702 delegation): a run of the interpreter loop
from the frame at a STATICCALL that returns a frame `s`.

Either `s` has an error, or the loop went on from the opcode after the STATICCALL with a flag
0 or 1 pushed, the memory grown for both ranges with the start of the return data `out` written
to the output range, `out` as return data, at most the gas of before, a state where every
address reads as before (account, storage, transient storage; only records of reads differ), the
same block, and the same logs.

After the facts asked for: the accounts to delete and the refund counter are the same too.

When no message was sent (depth limit), the flag is 0 and `out` is empty: the write then leaves
the grown memory as it is (`memoryWrite_empty_extract`). -/
theorem staticcall_kept (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {rd : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    {bound : Nat} {evm s : Evm fork Nat}
    (start : Logic.At code message pc
      (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s) :
    s.error ≠ none ∨
    ∃ (flag : U256) (out : ByteArray) (g : Nat) (st : State.TransactionState) (ss : Substate)
        (after : Evm fork Nat),
      (flag = 0 ∨ flag = 1) ∧
      Logic.At code message (pc + 1) (flag :: rest)
        (memoryWrite (memoryExtend memory (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat (out.extract 0 (min outputSize.toNat out.size)))
        g st ss out after ∧
      g ≤ gas ∧
      State.TransactionState.SameOutside [] state st ∧ st.parent = state.parent ∧
      ss.logs = substate.logs ∧
      (∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after
          within' = .ok s) ∧
      ss.accountsToDelete = substate.accountsToDelete ∧
      ss.refundCounter = substate.refundCounter := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  rcases staticcall_route_outcome hberlin hglam hlt hbyte start within hrun with
    herr | ⟨g, st, ss, after, hat, hle, hso, hpar, hq, w, h⟩ |
    ⟨calleeCode, route, caller, msg, child, after, g, hcode, hroute, hsend, hran, -, hat, hle, w,
      h⟩
  · exact .inl herr
  · refine .inr ⟨0, .empty, g, st, ss, after, .inl rfl, ?_, hle, hso, hpar,
      congrArg Prod.fst hq, ⟨w, h⟩, congrArg (fun p => p.2.1) hq, congrArg (fun p => p.2.2) hq⟩
    rw [memoryWrite_empty_extract]
    exact hat
  · have hmsg := staticMessage_of_callSends hcode hroute hsend
    obtain ⟨so, par⟩ := static_ran hparis hran hmsg
    obtain ⟨i1, i2, i3⟩ := static_ran_incorporate hran hmsg
    obtain ⟨so0, par0, q0⟩ := callSends_state hsend
    refine .inr ⟨if child.error.isNone then 1 else 0, child.output, g,
      (incorporateChild fork caller child).state, (incorporateChild fork caller child).substate,
      after, ?_, hat, hle, ?_, ?_, i1.trans (congrArg Prod.fst q0), ⟨w, h⟩,
      i2.trans (congrArg (fun p => p.2.1) q0), i3.trans (congrArg (fun p => p.2.2) q0)⟩
    · split
      · exact .inr rfl
      · exact .inl rfl
    · rw [state_incorporateChild]
      intro address hmem
      obtain ⟨x, y, z⟩ := so0 address hmem
      obtain ⟨x', y', z'⟩ := so address hmem
      exact ⟨x'.trans x, fun k => (y' k).trans (y k), fun k => (z' k).trans (z k)⟩
    · rw [state_incorporateChild]
      exact par.trans par0

end TokenKit

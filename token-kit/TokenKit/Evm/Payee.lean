import TokenKit.Evm.Move
import TokenKit.Evm.Call
import UsdtVerify.Evm.Gas

/-!
# A payee that only takes ether, under EthLib's real runner

A contract that pays ether with a CALL hands a message to the runner. For EthLib's own runner
`processRunner` and a payee that has no code, or whose code is the one byte STOP, the message
does one thing: the message layer moves its value. This file proves it, so that an assumption on
the runner about such a message can be discharged for real callees.

- `STOP_CODE`: the code of one byte, STOP (a contract that accepts ether and does nothing).
- `stop_message`: from Paris, a message whose code is `STOP_CODE`, to a target that is no
  precompile, run by `processRunner`: it ends with no error, in the state of its caller after
  the move of its value (when it moves one) or in the state of its caller (when it moves none).
- `payee_keeps_storage`: from Paris, a message whose code is empty or `STOP_CODE`, to a target
  that is no precompile, run by `processRunner` to a frame with no error: every storage word of
  a contract `C` that holds code is as in the state of the caller. `C` may be the sender.

`noCode_message` (Ether.lean) is the case of no code. Nothing here is about one token.
-/

namespace TokenKit.Payee

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The code of one byte, STOP. -/
def STOP_CODE : ByteArray := ⟨#[0x00]⟩

theorem delegatedAddress_stop : delegatedAddress STOP_CODE = none := by decide

theorem delegatedAddress_empty : delegatedAddress ByteArray.empty = none := by decide

/-- From Paris, a message whose code is `STOP_CODE`, to a target that is no precompile, run by
`processRunner`: it ends with no error; when it moves a value, the move succeeds and the end
state is the state after the move; when it moves none, the end state is the state of the
caller. -/
theorem stop_message (hparis : .paris ≤ fork) {bound : Nat} {caller child : Evm fork Nat}
    {msg : Message fork} {to : Address} (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = STOP_CODE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) :
    child.error = none ∧
      (msg.shouldTransferValue = true ∧ msg.value ≠ 0 →
        caller.state.moveEther fork msg.caller msg.currentTarget msg.value = .ok child.state) ∧
      (¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) → child.state = caller.state) := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  rw [hp] at hrun
  by_cases ht : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · obtain ⟨moved, hm⟩ := moveEther_of_processMessage_eq_ok ht hrun
    obtain ⟨stopped, hrf, hq⟩ := Gas.SpecG.runFrame
      (Gas.stopG (fork := fork) (code := STOP_CODE) (message := msg) (pc := 0) (stack := [])
        (memory := .empty) (by decide) rfl)
      (bound := msg.gas) (runChild := processRunner fork msg.gas)
      (At.startFrame hcode moved { caller.substate.child with
        logs := pushTransferLog fork caller.substate.child.logs msg.caller msg.currentTarget
          msg.value }) (Nat.le_refl _)
    have hmap := processMessage_map_val_value (substate := caller.substate.child) ht hm noPre hrf
    rw [hrun] at hmap
    obtain ⟨-, he, -, -, hs, -⟩ := hq
    have he' : stopped.error = none := by simpa using he
    have hc : child'.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none he']
    rw [hst] at hm
    exact ⟨by rw [hc]; exact he', fun _ => by rw [hc, hs]; exact hm, fun h => (h ht).elim⟩
  · obtain ⟨stopped, hrf, hq⟩ := Gas.SpecG.runFrame
      (Gas.stopG (fork := fork) (code := STOP_CODE) (message := msg) (pc := 0) (stack := [])
        (memory := .empty) (by decide) rfl)
      (bound := msg.gas) (runChild := processRunner fork msg.gas)
      (At.startFrame hcode (startState fork msg caller.state) caller.substate.child)
      (Nat.le_refl _)
    have hmap := processMessage_map_val ht noPre hrf
    rw [hrun] at hmap
    obtain ⟨-, he, -, -, hs, -⟩ := hq
    have he' : stopped.error = none := by simpa using he
    have hc : child'.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none he']
    exact ⟨by rw [hc]; exact he', fun h => (ht h).elim, fun _ => by rw [hc, hs, hst]⟩

/-- From Paris, a message whose code is empty or `STOP_CODE`, to a target that is no
precompile, run by `processRunner` to a frame with no error: every storage word of a contract
`C` that holds code is as in the state of the caller. The only change is the move of the value
of the message, and `C` may be its sender or its recipient. -/
theorem payee_keeps_storage (hparis : .paris ≤ fork) {bound : Nat} {caller child : Evm fork Nat}
    {msg : Message fork} {to C : Address}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = .empty ∨ msg.code = STOP_CODE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none)
    (hC : (caller.state.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (herr : child.error = none) (n : U256) :
    storageAt child.state C n = storageAt caller.state C n := by
  have key : (msg.shouldTransferValue = true ∧ msg.value ≠ 0 →
        caller.state.moveEther fork msg.caller msg.currentTarget msg.value = .ok child.state) ∧
      (¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) → child.state = caller.state) := by
    rcases hcode with hcode | hcode
    · obtain ⟨h1, h2⟩ := noCode_message hparis hran hcode htarget noPre
      exact ⟨h1, fun h => h2 h herr⟩
    · exact (stop_message hparis hran hcode htarget noPre).2
  by_cases ht : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · exact moveEther_keeps_storage hC (key.1 ht) n
  · rw [key.2 ht]

/-- From Paris, `processRunner` does run a message with value to an address with no code and no
precompile, when the move of its value succeeds: it gives a frame with no error, in the state
after the move. This is the existence half of `noCode_message` (which starts from a frame that
the runner gave). -/
theorem noCode_message_runs (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} {moved : State.TransactionState}
    (lt : msg.gas < bound)
    (hcode : msg.code = .empty) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none)
    (ht : msg.shouldTransferValue = true ∧ msg.value ≠ 0)
    (hm : caller.state.moveEther fork msg.caller msg.currentTarget msg.value = .ok moved) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.state = moved := by
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  obtain ⟨stopped, hrf, hse, hss⟩ := runFrame_startFrame_empty (fork := fork)
    (state := moved) (substate := { caller.substate.child with
      logs := pushTransferLog fork caller.substate.child.logs msg.caller msg.currentTarget
        msg.value })
    (runChild := processRunner fork msg.gas) (within := Nat.le_refl _) hcode
  have hmap := processMessage_map_val_value (substate := caller.substate.child) ht
    (by rw [hst]; exact hm) noPre hrf
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    have hc : child.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none hse]
    exact ⟨child, rfl, by rw [hc]; exact hse, by rw [hc]; exact hss⟩

end TokenKit.Payee

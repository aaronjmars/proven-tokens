import BnbVerify.Bnb.Withdraw
import TokenKit.Evm.Move
import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# The supply invariant over whole messages and finite sequences of them

`supply_preserved` is about one frame: a run of `CODE` from pc 0 that ends with no error, with a
selector other than `withdrawEther`. `Withdraw.supply_withdrawEther` is the same for
`withdrawEther`, under a local assumption on the runner. Here both are lifted to a whole
top-level message as EthLib's `processMessage` runs it (with the rollback of a failed call), and
to any finite sequence of steps. It follows SHIB's `Shib/Seq.lean`. The meter is the one-counter
meter (`Nat`); the two-counter meter of EIP-8037 is not covered.

Two differences with SHIB:

- `withdrawEther` sends a message (CALL to the owner). What the callee does is not known in
  general, so a successful call of `withdrawEther` is its own kind of step, `GoodWithdraw`: it
  carries the local assumption `Withdraw.KeepsInv` on the runner of that run (only the one
  message that the CALL sends, see Bnb/Withdraw.lean), the fork bound of EthLib's rules of CALL
  (before Glamsterdam) and `hdel` (the code of the owner is no EIP-7702 delegation).
  `GoodCall` is every other selector, with no assumption on the runner.
  Bnb/Sanity/Withdraw.lean discharges the assumption for `processRunner` when the owner has no
  code or the code STOP.
- the fallback of BNB is payable, so a top-level message can succeed and move its value. The
  message layer moves the value before the frame starts. That this keeps the storage of the
  contract is a theorem (TokenKit's `moveEther_keeps_storage`, from EthLib's lemmas on
  `moveEther`), for a contract account that holds code: the hypothesis `hcode` of
  `process_step` (the account of `C` has a code hash that is not the hash of no code).
  Before the fix round of audit 3 this was a hypothesis `hmove` of `process_step`.

Scope of the sequence theorems (also in kit-status.json, `sequence_scope`):

- `GoodCall C S S'`: a run of a fresh frame of `CODE` for a message to `C`, from the state `S`,
  that ends with no error in the state `S'`, with the hypotheses of `supply_preserved` for that
  run: its own fork from Berlin, call data below 2^256 bytes, a selector other than
  `withdrawEther`, and the hypothesis on keccak `Sep (callKeys message)` (assumed, not proved).
  It covers every function but `withdrawEther`, and the fallback.
- `GoodWithdraw C S S'`: the same for the selector of `withdrawEther`, with its fork from Berlin
  and before Glamsterdam, `hdel`, and `Withdraw.KeepsInv` for the runner of the run.
- `Untouched C S S'`: any change that keeps every storage word of `C`. This is where the model
  puts what is not a successful run of the code of `C`: a failed call rolled back by the message
  layer, the move of the value of a message, transactions to other accounts, fees. For a failed
  top-level message and for the move of the value it is proved (`untouched_process_failed`,
  `untouched_move`); for the other changes it is the assumption of the step. It excludes a
  change of the storage of `C` by anything but its code (in the EVM only the code of `C` writes
  the storage of `C`, short of SELFDESTRUCT of `C`, which `CODE` does not have).
- `Calls C S S'`: a finite sequence of such steps. `inv_calls`: `Inv C` at its start gives
  `Inv C` at its end.
- `process_step`: from Paris, every top-level message of `CODE` to `C` with a selector other
  than `withdrawEther` that `processMessage` ends is a sequence of steps of `Calls C`.
- `process_step_withdraw`: the same for the selector of `withdrawEther`, before Glamsterdam,
  under `hdel` and `Withdraw.KeepsInv` for `processRunner`.
- `process_step_all`: every selector, with the two hypotheses of `withdrawEther` asked only when
  the selector is its selector.
- `process_step_inv`, `process_step_inv_all`: so `Inv` at the start of the message gives `Inv`
  at its end.
-/

namespace BnbVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- One run of `CODE` for a message to `C`, with a selector other than `withdrawEther`, that ends
with no error, from `S` to `S'`, under the hypotheses of `supply_preserved`. -/
def GoodCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork Nat bound) (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    selector message.data ≠ 0x3bed33ce ∧
    Sep (callKeys message) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One run of `CODE` for a message to `C` with the selector of `withdrawEther` that ends with no
error, from `S` to `S'`, under the hypotheses of `Withdraw.supply_withdrawEther`: its own fork
from Berlin and before Glamsterdam, call data below 2^256 bytes, the code of the owner is no
EIP-7702 delegation, and the local assumption `Withdraw.KeepsInv` on the runner of this run (the
one message that its CALL sends keeps `Inv`). -/
def GoodWithdraw (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork Nat bound) (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ selector message.data = 0x3bed33ce ∧
    (∀ c, S.getCode (S.getAccount (Withdraw.ownerOf message S)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none) ∧
    Withdraw.KeepsInv runChild message S ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A change of state that keeps every storage word of `C`. -/
def Untouched (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, storageAt S' C n = storageAt S C n

/-- A finite sequence of successful calls to `C` (`call`: any selector but `withdrawEther`;
`withdraw`: `withdrawEther`, under its local assumption on the runner) and of changes that keep
the storage of `C` (`other`). -/
inductive Calls (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → Calls C S' S'' → Calls C S S''
  | withdraw {S S' S'' : State.TransactionState} : GoodWithdraw C S S' → Calls C S' S'' →
      Calls C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Calls C S' S'' →
      Calls C S S''

/-- One successful call keeps `Inv C`. -/
theorem inv_goodCall {C : Address} {S S' : State.TransactionState}
    (h : GoodCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, evm, s, within, hC, hfork, hsize, hnw,
    K, start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_preserved hfork hsize hnw K hI start (Ends.run hrun) hok

/-- One successful call of `withdrawEther` keeps `Inv C` (under its local assumption). -/
theorem inv_goodWithdraw {C : Address} {S S' : State.TransactionState}
    (h : GoodWithdraw C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, evm, s, within, hC, hfork, hglam, hsize,
    hsel, hdel, hkeeps, start, hrun, hok, rfl⟩ := h
  subst hC
  exact Withdraw.supply_withdrawEther hfork hglam hsize hsel hdel hkeeps hI start within hrun hok

/-- A change that keeps the storage of `C` keeps `Inv C`. -/
theorem inv_untouched {C : Address} {S S' : State.TransactionState}
    (h : Untouched C S S') (hI : Inv C S) : Inv C S' :=
  (Supply.inv2_congr h).mpr hI

/-- `Inv C` along every finite sequence of successful calls to `C` and of changes that keep the
storage of `C`. Each call other than `withdrawEther` carries its own hypothesis on keccak
`Sep (callKeys message)`; each call of `withdrawEther` carries its own local assumption on its
runner (`Withdraw.KeepsInv`). -/
theorem inv_calls {C : Address} {S S' : State.TransactionState}
    (h : Calls C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | withdraw hg _ ih => exact ih (inv_goodWithdraw hg hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- A top-level message (any code, any fork) run by EthLib's `processMessage` that ends with an
error is an `Untouched` step for every address `C`: the rollback restores the storage of the
state it was sent from (EthLib's `getStorage_processMessage_of_error`). -/
theorem untouched_process_failed {fork : Fork} {message : Message fork}
    {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (herr : ended.val.error ≠ none) (C : Address) : Untouched C state ended.val.state :=
  fun _ => getStorage_processMessage_of_error hproc (Option.isSome_iff_ne_none.mpr herr) C _

/-- The move of the value of a top-level message to a contract that holds code is an
`Untouched` step: it keeps every storage word of the contract (TokenKit's
`moveEther_keeps_storage`). From Paris, where the state that the message starts from is the
state it is sent from. -/
theorem untouched_move {fork : Fork} (hparis : .paris ≤ fork) {message : Message fork}
    {state moved : State.TransactionState}
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hm : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value = .ok moved) :
    Untouched message.currentTarget state moved := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  rw [hst] at hm
  exact fun n => moveEther_keeps_storage hcode hm n

/-- From Paris, every top-level message to `C` whose code is `CODE` (no precompile, call data
below 2^256 bytes, a selector other than `withdrawEther`), run by EthLib's `processMessage` to
the end, is a sequence of steps of `Calls C`: an `Untouched` step when it ends with an error;
a `GoodCall` when it ends with no error and moves no value; the move of the value then a
`GoodCall` when it ends with no error and moves its value (only the payable fallback does).
`K` is the hypothesis on keccak (not proved). `hcode`: the account of `C` holds code (its code
hash is not the hash of no code), so the move of the value keeps its storage
(`untouched_move`). -/
theorem process_step {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hnw : selector message.data ≠ 0x3bed33ce)
    (K : Sep (callKeys message))
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    Calls message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  by_cases herr : ended.val.error = none
  · have key : ∀ (st : State.TransactionState) (ss : Substate)
        (result : Except EvmError (Evm fork Nat)),
        runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
          (startFrame message st ss (GasMeter.start message.gas message.reservoir))
          (Nat.le_refl _) = result →
        (processMessage fork message state substate).map Subtype.val =
          result.map (rollbackOnError state) →
        GoodCall message.currentTarget st ended.val.state := by
      intro st ss result hres hmap
      rw [hproc] at hmap
      rcases result with e | s
      · cases hmap
      · simp only [Except.map, Except.ok.injEq] at hmap
        have hse : s.error = none := by
          rw [← herr, hmap]
          unfold rollbackOnError
          split <;> rfl
        have hend : ended.val = s := by
          rw [hmap]
          unfold rollbackOnError
          simp [hse]
        exact ⟨fork, message, ss, message.gas, message.gas, processRunner fork message.gas, _,
          s, Nat.le_refl _, rfl, hberlin, hsize, hnw, K, At.startFrame hmc st ss, hres, hse,
          by rw [hend]⟩
    by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · cases hm : (startState fork message state).moveEther fork message.caller
        message.currentTarget message.value with
      | error e =>
        exfalso
        rw [processMessage] at hproc
        simp only [Except.map, ht, ne_eq, not_false_eq_true, and_self, ite_true, bind, pure,
          Except.bind, Except.pure, Except.mapError, hm] at hproc
        cases hproc
      | ok moved =>
        exact .other (untouched_move hparis hcode hm)
          (.call (key moved _ _ rfl (processMessage_map_val_value ht hm noPrecompile rfl))
            (.nil _))
    · have h := key _ _ _ rfl (processMessage_map_val ht noPrecompile rfl)
      rw [hst] at h
      exact .call h (.nil _)
  · exact .other (untouched_process_failed hproc herr _) (.nil _)

/-- `process_step` for a message that moves no value: no hypothesis on the move of the value. -/
theorem process_step_novalue {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hnw : selector message.data ≠ 0x3bed33ce)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  by_cases herr : ended.val.error = none
  · generalize hres : runFrame (step fork) (step_decreases fork) message.gas
      (processRunner (Meter := Nat) fork message.gas)
      (startFrame message (startState fork message state) substate
        (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = result
    have hmap := processMessage_map_val noValue noPrecompile hres
    rw [hproc] at hmap
    rcases result with e | s
    · cases hmap
    · simp only [Except.map, Except.ok.injEq] at hmap
      have hse : s.error = none := by
        rw [← herr, hmap]
        unfold rollbackOnError
        split <;> rfl
      have hend : ended.val = s := by
        rw [hmap]
        unfold rollbackOnError
        simp [hse]
      have start := At.startFrame hmc (startState fork message state) substate
      rw [hst] at start hres
      exact .inl ⟨fork, message, substate, message.gas, message.gas,
        processRunner fork message.gas, _, s, Nat.le_refl _, rfl, hberlin, hsize, hnw, K, start,
        hres, hse, by rw [hend]⟩
  · exact .inr (untouched_process_failed hproc herr _)

/-- From Paris, a top-level message of `CODE` to `C` with a selector other than `withdrawEther`
that `processMessage` ends keeps the invariant: `Inv` at its start gives `Inv` at its end
(hypotheses of `process_step`). -/
theorem process_step_inv {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hnw : selector message.data ≠ 0x3bed33ce)
    (K : Sep (callKeys message))
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state :=
  inv_calls (process_step hparis hmc noPrecompile hsize hnw K hcode hproc) hI

/-- From Paris and before Glamsterdam, a top-level message to `C` whose code is `CODE` (no
precompile, call data below 2^256 bytes) with the selector of `withdrawEther`, run by EthLib's
`processMessage` to the end, is a sequence of steps of `Calls C`: an `Untouched` step when it
ends with an error, a `GoodWithdraw` when it ends with no error. A successful `withdrawEther`
has value 0 (the function is not payable), so no value moves. `hdel`: the code of the owner is
no EIP-7702 delegation. `hkeeps`: the local assumption on `processRunner` for the one message
that the CALL of this call sends. -/
theorem process_step_withdraw {fork : Fork} (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hdel : ∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
      .ok c → .pectra ≤ fork → delegatedAddress c = none)
    (hkeeps : Withdraw.KeepsInv (processRunner (Meter := Nat) fork message.gas) message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    Calls message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  by_cases herr : ended.val.error = none
  · have key : ∀ (st : State.TransactionState) (ss : Substate)
        (result : Except EvmError (Evm fork Nat)),
        runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
          (startFrame message st ss (GasMeter.start message.gas message.reservoir))
          (Nat.le_refl _) = result →
        (processMessage fork message state substate).map Subtype.val =
          result.map (rollbackOnError state) →
        ∃ s, runFrame (step fork) (step_decreases fork) message.gas
            (processRunner fork message.gas)
            (startFrame message st ss (GasMeter.start message.gas message.reservoir))
            (Nat.le_refl _) = .ok s ∧ s.error = none ∧ ended.val = s := by
      intro st ss result hres hmap
      rw [hproc] at hmap
      rcases result with e | s
      · cases hmap
      · simp only [Except.map, Except.ok.injEq] at hmap
        have hse : s.error = none := by
          rw [← herr, hmap]
          unfold rollbackOnError
          split <;> rfl
        have hend : ended.val = s := by
          rw [hmap]
          unfold rollbackOnError
          simp [hse]
        exact ⟨s, hres, hse, hend⟩
    by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exfalso
      cases hm : (startState fork message state).moveEther fork message.caller
        message.currentTarget message.value with
      | error e =>
        rw [processMessage] at hproc
        simp only [Except.map, ht, ne_eq, not_false_eq_true, and_self, ite_true, bind, pure,
          Except.bind, Except.pure, Except.mapError, hm] at hproc
        cases hproc
      | ok moved =>
        obtain ⟨s, hres, hse, -⟩ :=
          key moved _ _ rfl (processMessage_map_val_value ht hm noPrecompile rfl)
        exact ht.2 (Withdraw.withdrawEther_only_owner_run hberlin hsize hsel
          (At.startFrame hmc moved _) (Nat.le_refl _) hres hse).1
    · obtain ⟨s, hres, hse, hend⟩ := key _ _ _ rfl (processMessage_map_val ht noPrecompile rfl)
      rw [hst] at hres
      exact .withdraw ⟨fork, message, substate, message.gas, message.gas,
        processRunner fork message.gas, _, s, Nat.le_refl _, rfl, hberlin, hglam, hsize, hsel,
        hdel, hkeeps, At.startFrame hmc state substate, hres, hse, by rw [hend]⟩ (.nil _)
  · exact .other (untouched_process_failed hproc herr _) (.nil _)

/-- From Paris, EVERY top-level message to `C` whose code is `CODE` (no precompile, call data
below 2^256 bytes, any selector), run by EthLib's `processMessage` to the end, is a sequence of
steps of `Calls C`. The hypotheses of a selector other than `withdrawEther` (`K`, on keccak) and
of `withdrawEther` (`hw`: before Glamsterdam, `hdel`, and the local assumption on
`processRunner`) are each asked only for that kind of selector. -/
theorem process_step_all {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (K : selector message.data ≠ 0x3bed33ce → Sep (callKeys message))
    (hw : selector message.data = 0x3bed33ce → fork < .glamsterdam ∧
      (∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
        .ok c → .pectra ≤ fork → delegatedAddress c = none) ∧
      Withdraw.KeepsInv (processRunner (Meter := Nat) fork message.gas) message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    Calls message.currentTarget state ended.val.state := by
  by_cases hsel : selector message.data = 0x3bed33ce
  · obtain ⟨hglam, hdel, hkeeps⟩ := hw hsel
    exact process_step_withdraw hparis hglam hmc noPrecompile hsize hsel hdel hkeeps hproc
  · exact process_step hparis hmc noPrecompile hsize hsel (K hsel) hcode hproc

/-- From Paris, every top-level message of `CODE` to `C` (any selector) that `processMessage`
ends keeps the invariant: `Inv` at its start gives `Inv` at its end (hypotheses of
`process_step_all`). -/
theorem process_step_inv_all {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (K : selector message.data ≠ 0x3bed33ce → Sep (callKeys message))
    (hw : selector message.data = 0x3bed33ce → fork < .glamsterdam ∧
      (∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
        .ok c → .pectra ≤ fork → delegatedAddress c = none) ∧
      Withdraw.KeepsInv (processRunner (Meter := Nat) fork message.gas) message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state :=
  inv_calls (process_step_all hparis hmc noPrecompile hsize hcode K hw hproc) hI

/-- Two sequences of steps, one after the other, are a sequence of steps. -/
theorem Calls.append {C : Address} {S S' S'' : State.TransactionState}
    (h1 : Calls C S S') (h2 : Calls C S' S'') : Calls C S S'' := by
  induction h1 with
  | nil => exact h2
  | call hg _ ih => exact .call hg (ih h2)
  | withdraw hg _ ih => exact .withdraw hg (ih h2)
  | other hu _ ih => exact .other hu (ih h2)

end BnbVerify

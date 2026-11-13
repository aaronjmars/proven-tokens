import WethVerify.Weth.Reenter
import TokenKit.Evm.Ether

/-!
# Solvency over whole messages and finite sequences of them

`solvent_preserved` is about one frame. Here it is lifted to a whole top-level message as
EthLib's `processMessage` runs it from Paris (the move of the value into the contract, the run
of the code, the rollback of a failed call), and to any finite sequence of steps. The meter is
the one-counter meter (`Nat`); the two-counter meter of EIP-8037 is not covered.

- `Funded C v S Sf`: `Sf` is `S` with `v` wei or more added to the ether of `C` and the storage
  of `C` kept (the state at the start of the frame of a message that carries `v` wei).
- `GoodCall C S S'`: a run of a fresh frame of `CODE` for a message to `C`, from a state funded
  from `S`, that ends with no error in `S'`, with the hypotheses of `solvent_preserved` for that
  run (its own fork from Berlin, call data below 2^256 bytes, `Sep (callKeys message)`, and for
  a call of `withdraw` with no value `WithdrawReady` and `CalleeQuiet`).
- `Other C S S'`: any change that keeps every storage word of `C` and does not lower its ether.
  This is where the model puts what is not a successful run of the code of `C`: a failed call
  rolled back by the message layer (proved: `other_process_failed`), transactions to other
  accounts, fees, ether forced into `C`. For those other changes it is the assumption of the
  step.
- `Calls C S S'`: a finite sequence of such steps. `solvent_calls`: `Solvent C` at its start
  gives `Solvent C` at its end.
- `goodCall_process`: from Paris, a top-level message to `C` (code `CODE`, no precompile) that
  `processMessage` ends with no error is a `GoodCall`. Named hypotheses: `hval` (the message
  moves its value, or has none: no DELEGATECALL-like message with a value it does not move),
  `hne` (the caller is not `C` itself), `hcodeC` (the account of `C` has code, so the move of
  the value does not delete it), `K` (keccak separation, not proved), `hw` (for `withdraw`:
  `WithdrawReady` only; there is no assumption on the callee, `calleeQuiet_process` of
  Weth/Reenter.lean proves `CalleeQuiet` for the runner of the interpreter and every callee).
- `process_step`, `process_step_solvent`, `calls_process`: every top-level message that
  `processMessage` ends is a step, so it keeps `Solvent`.
- `withdrawReady_eoa`: `WithdrawReady` when the caller of `withdraw` has no code (an externally
  owned account) before Glamsterdam. The call depth and the gas are not asked any more.

Retired: `CalleeKeeps` (it restated the conclusion of `solvent_withdraw` and did not fix the gas
of the message), `calleeKeeps_noCode` and `withdrawHyp_eoa` (stated on it).
-/

set_option autoImplicit false

namespace WethVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- `Sf` is `S` with `v` wei or more added to the ether of `C`, and the storage of `C` kept. -/
def Funded (C : Address) (v : U256) (S Sf : State.TransactionState) : Prop :=
  (∀ n, storageAt Sf C n = storageAt S C n) ∧
    (etherOf S C).toNat + v.toNat ≤ (etherOf Sf C).toNat

theorem Funded.backed {C : Address} {v : U256} {S Sf : State.TransactionState}
    (h : Funded C v S Sf) (hs : Solvent C S) : Backed v C Sf := by
  unfold Solvent Supply.Solvent at hs
  unfold Backed Supply.Backed
  rw [Supply.sumBal_congr h.1]
  have := h.2
  omega

/-- One run of `CODE` for a message to `C` that ends with no error, from `S` (funded with the
value of the message) to `S'`, under the hypotheses of `solvent_preserved`. -/
def GoodCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork Nat bound) (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound) (Sf : State.TransactionState),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    Sep (callKeys message) ∧ Funded C message.value S Sf ∧
    (selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message Sf ∧ ∀ calleeCode,
        Sf.getCode (Sf.getAccount message.caller).codeHash = .ok calleeCode →
        CalleeQuiet runChild message Sf substate gas calleeCode) ∧
    At CODE message 0 [] .empty gas Sf substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A change of state that keeps every storage word of `C` and does not lower its ether. -/
def Other (C : Address) (S S' : State.TransactionState) : Prop :=
  (∀ n, storageAt S' C n = storageAt S C n) ∧ (etherOf S C).toNat ≤ (etherOf S' C).toNat

/-- A finite sequence of successful calls to `C` and of changes that keep the storage of `C`
and do not lower its ether. -/
inductive Calls (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → Calls C S' S'' → Calls C S S''
  | other {S S' S'' : State.TransactionState} : Other C S S' → Calls C S' S'' → Calls C S S''

/-- One successful call keeps `Solvent C`. -/
theorem solvent_goodCall {C : Address} {S S' : State.TransactionState}
    (h : GoodCall C S S') (hI : Solvent C S) : Solvent C S' := by
  obtain ⟨fork, message, substate, gas, bound, runChild, evm, s, within, Sf, hC, hfork, hsize, K,
    hf, hw, start, hrun, hok, rfl⟩ := h
  subst hC
  exact solvent_preserved hfork hsize K (hf.backed hI) hw start within hrun hok

/-- A change that keeps the storage of `C` and does not lower its ether keeps `Solvent C`. -/
theorem solvent_other {C : Address} {S S' : State.TransactionState}
    (h : Other C S S') (hI : Solvent C S) : Solvent C S' :=
  Supply.solvent_congr h.1 h.2 hI

/-- `Solvent C` along every finite sequence of steps. Each call carries its own hypotheses. -/
theorem solvent_calls {C : Address} {S S' : State.TransactionState}
    (h : Calls C S S') (hI : Solvent C S) : Solvent C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (solvent_goodCall hg hI)
  | other hu _ ih => exact ih (solvent_other hu hI)

/-- The end of a run of the frame of a top-level message, with no error, is a `GoodCall`. -/
theorem goodCall_of_run {fork : Fork} (hberlin : .berlin ≤ fork)
    {message : Message fork} {state Sf : State.TransactionState} {substate ss : Substate}
    (hmc : message.code = CODE) (hsize : message.data.size < 2 ^ 256)
    (K : Sep (callKeys message)) (hf : Funded message.currentTarget message.value state Sf)
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message Sf ∧ ∀ calleeCode,
        Sf.getCode (Sf.getAccount message.caller).codeHash = .ok calleeCode →
        CalleeQuiet (processRunner fork message.gas) message Sf ss message.gas calleeCode)
    {result : Except EvmError (Evm fork Nat)}
    (hres : runFrame (step fork) (step_decreases fork) message.gas
      (processRunner (Meter := Nat) fork message.gas)
      (startFrame message Sf ss (GasMeter.start message.gas message.reservoir))
      (Nat.le_refl _) = result)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hmap : (processMessage fork message state substate).map Subtype.val =
      result.map (rollbackOnError state))
    (hok : ended.val.error = none) :
    GoodCall message.currentTarget state ended.val.state := by
  rw [hproc] at hmap
  rcases result with e | s
  · cases hmap
  · simp only [Except.map, Except.ok.injEq] at hmap
    have hse : s.error = none := by
      rw [← hok, hmap]
      unfold rollbackOnError
      split <;> rfl
    have hend : ended.val = s := by
      rw [hmap]
      unfold rollbackOnError
      simp [hse]
    exact ⟨fork, message, ss, message.gas, message.gas, processRunner fork message.gas, _,
      s, Nat.le_refl _, Sf, rfl, hberlin, hsize, K, hf, hw, At.startFrame hmc Sf ss, hres, hse,
      by rw [hend]⟩

/-- From Paris, a top-level message to `C` (code `CODE`, no precompile), run by EthLib's
`processMessage`, that ends with no error, is a `GoodCall` from its start state to its end
state. The value of the message, if any, is moved from the caller into `C` first. -/
theorem goodCall_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    (hval : message.shouldTransferValue = true ∨ message.value = 0)
    (hne : message.caller ≠ message.currentTarget)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    GoodCall message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
  · obtain ⟨moved, hm⟩ := moveEther_of_processMessage_eq_ok ht hproc
    have hm' := hm
    rw [hst] at hm'
    obtain ⟨hs, he⟩ := moveEther_into hne hcodeC hm'
    exact goodCall_of_run hberlin hmc hsize K ⟨hs, Nat.le_of_eq he.symm⟩
      (fun _ hv => absurd hv ht.2) rfl hproc
      (processMessage_map_val_value ht hm noPrecompile rfl) hok
  · have hv : message.value = 0 := by
      rcases hval with h | h
      · exact Classical.byContradiction fun hv => ht ⟨h, hv⟩
      · exact h
    generalize hres : runFrame (step fork) (step_decreases fork) message.gas
      (processRunner (Meter := Nat) fork message.gas)
      (startFrame message (startState fork message state) substate
        (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = result
    have hmap := processMessage_map_val ht noPrecompile hres
    rw [hst] at hres
    exact goodCall_of_run hberlin hmc hsize K
      ⟨fun _ => rfl, by rw [hv]; simp⟩
      (fun h hv' => ⟨hw h hv', fun c _ => calleeQuiet_process hberlin c hcodeC⟩)
      hres hproc hmap hok

/-- A top-level message (any code, any fork) run by EthLib's `processMessage` that ends with an
error is an `Other` step for every address `C`: the rollback restores the accounts and the
storage of the state it was sent from. -/
theorem other_process_failed {fork : Fork} {message : Message fork}
    {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (herr : ended.val.error ≠ none) (C : Address) : Other C state ended.val.state := by
  have h := processMessage_sameOutside_of_error hproc (Option.isSome_iff_ne_none.mpr herr) C
    List.not_mem_nil
  refine ⟨fun _ => h.2.1 _, ?_⟩
  unfold etherOf State.TransactionState.getAccount
  rw [h.1]
  exact Nat.le_refl _

/-- From Paris, every top-level message to `C` whose code is `CODE`, run by EthLib's
`processMessage` to the end, is a step of `Calls C`: a `GoodCall` when it ends with no error,
and an `Other` step when it ends with an error. -/
theorem process_step {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    (hval : message.shouldTransferValue = true ∨ message.value = 0)
    (hne : message.caller ≠ message.currentTarget)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      Other message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · exact .inl (goodCall_process hparis hmc noPrecompile hsize K hval hne hcodeC hw hproc herr)
  · exact .inr (other_process_failed hproc herr _)

/-- From Paris, a top-level message of `CODE` to `C` that `processMessage` ends keeps the
contract solvent: `Solvent` in the state it is sent from gives `Solvent` in the state it ends
in, whether it ends with an error or not. -/
theorem process_step_solvent {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    (hval : message.shouldTransferValue = true ∨ message.value = 0)
    (hne : message.caller ≠ message.currentTarget)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Solvent message.currentTarget state) :
    Solvent message.currentTarget ended.val.state := by
  rcases process_step hparis hmc noPrecompile hsize K hval hne hcodeC hw hproc with h | h
  · exact solvent_goodCall h hI
  · exact solvent_other h hI

/-- A top-level message of `CODE` to `C`, then a sequence of steps, is a sequence of steps. -/
theorem calls_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state S' : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    (hval : message.shouldTransferValue = true ∨ message.value = 0)
    (hne : message.caller ≠ message.currentTarget)
    (hcodeC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : Calls message.currentTarget ended.val.state S') :
    Calls message.currentTarget state S' := by
  rcases process_step hparis hmc noPrecompile hsize K hval hne hcodeC hw hproc with h | h
  · exact .call h rest
  · exact .other h rest

/-! ## The caller of `withdraw` with no code -/

/-- `WithdrawReady` when the caller of `withdraw` has no code (an externally owned account),
before Glamsterdam. Nothing else is asked: not the call depth, not the gas. -/
theorem withdrawReady_eoa {fork : Fork} (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState}
    (heoa : (state.getAccount message.caller).codeHash = EMPTY_CODE_HASH) :
    WithdrawReady fork message state := by
  refine ⟨hglam, fun c hc _ => ?_⟩
  have h0 : state.getCode (state.getAccount message.caller).codeHash = .ok ByteArray.empty := by
    simp [State.TransactionState.getCode, heoa]
  rw [h0] at hc
  cases hc
  first | rfl | decide | simp [delegatedAddress]

end WethVerify

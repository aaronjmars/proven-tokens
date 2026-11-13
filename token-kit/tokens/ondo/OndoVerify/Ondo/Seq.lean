import OndoVerify.Ondo.SigSupply
import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# The supply invariant over whole messages and finite sequences of them

`supply_preserved_real` is about one frame: a run of `CODE` from pc 0, under EthLib's real
runner, that ends with no error, for any call data (`delegateBySig` included).
Here it is lifted to a whole top-level message as EthLib's `processMessage` runs it (with the
rollback of a failed call), and to any finite sequence of steps. It follows
`tokens/uni/UniVerify/Uni/Seq.lean`. The meter is the one-counter meter (`Nat`); the
two-counter meter of EIP-8037 is not covered.

- `NoDelegation1 fork S`: the account at address 1 (the precompile ECRECOVER) holds no EIP-7702
  delegation code in `S` (a fact of the state, true on chain).
- `GoodCall C S S'`: a run of a fresh frame of `CODE` for a message to `C`, from the state `S`,
  that ends with no error in the state `S'`, with the hypotheses of `supply_preserved_real` for
  that run: its own fork from Paris and before Glamsterdam, call data below 2^256 bytes,
  `NoDelegation1`, and the hypothesis on keccak `RealSep message S` (assumed, not proved: finite lists of the
  words of that message and that state, see `Sep.lean` and `SigSupply.lean`).
- `Untouched C S S'`: any change that keeps every storage word of `C`. This is where the model
  puts what is not a successful run of the code of `C`: a failed call rolled back by the message
  layer, transactions to other accounts, fees. For a failed top-level message it is proved
  (`untouched_process_failed`); for the other changes it is the assumption of the step.
- `Calls C S S'`: a finite sequence of such steps. `inv_calls`: `Inv C` at its start gives
  `Inv C` at its end.
- `goodCall_process`: a top-level message to `C` (code `CODE`, no value moved, no precompile)
  that `processMessage` ends with no error is a `GoodCall`.
- `process_value_fails`: from Berlin, a top-level message of `CODE` with a nonzero value ends
  with an error.
- `process_step`: every top-level message of `CODE` to `C` that `processMessage` ends is a
  `GoodCall` (no error) or an `Untouched` step (an error: storage as before).
- `process_step_inv`: so `Inv` at the start of the message gives `Inv` at its end.
-/

namespace OndoVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open OndoVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The invariant reads the storage words of `C` only. -/
theorem inv_congr {C : Address} {S S' : State.TransactionState}
    (h : ∀ n, storageAt S' C n = storageAt S C n) : Inv C S' ↔ Inv C S := by
  have hD : SupplyMask.D (79228162514264337593543950335 : U256) 6 4 C S' =
      SupplyMask.D (79228162514264337593543950335 : U256) 6 4 C S := by
    unfold SupplyMask.D SupplyMask.sumBal
    rw [h 4, Supply.sumTo_congr (g := SupplyMask.bal _ 6 C S) _ (fun i _ => by
      show ((bitwiseAnd _ (storageAt S' C _)).toNat : Int) =
        ((bitwiseAnd _ (storageAt S C _)).toNat : Int)
      rw [h])]
  show SupplyMask.Inv _ 6 4 C S' ↔ SupplyMask.Inv _ 6 4 C S
  unfold SupplyMask.Inv
  rw [hD]

/-- The account at address 1 holds no EIP-7702 delegation code in `S`. -/
def NoDelegation1 (fork : Fork) (S : State.TransactionState) : Prop :=
  ∀ c, S.getCode (S.getAccount (toAddressMasked 1)).codeHash = .ok c →
    .pectra ≤ fork → delegatedAddress c = none

/-- One run of `CODE` for a message to `C` that ends with no error, from `S` to `S'`, under the
hypotheses of `supply_preserved_real`. -/
def GoodCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .paris ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ NoDelegation1 fork S ∧ RealSep message S ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within
      = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A change of state that keeps every storage word of `C`. -/
def Untouched (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, storageAt S' C n = storageAt S C n

/-- A finite sequence of successful calls to `C` and of changes that keep the storage of `C`. -/
inductive Calls (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → Calls C S' S'' → Calls C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Calls C S' S'' →
      Calls C S S''

/-- One successful call keeps `Inv C`. -/
theorem inv_goodCall {C : Address} {S S' : State.TransactionState}
    (h : GoodCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hdel, K,
    start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_preserved_real hparis hglam hsize hdel K hI start within hrun hok

/-- A change that keeps the storage of `C` keeps `Inv C`. -/
theorem inv_untouched {C : Address} {S S' : State.TransactionState}
    (h : Untouched C S S') (hI : Inv C S) : Inv C S' :=
  (inv_congr h).mpr hI

/-- `Inv C` along every finite sequence of successful calls to `C` and of changes that keep the
storage of `C`. Each call carries its own hypothesis on keccak `RealSep message S`. -/
theorem inv_calls {C : Address} {S S' : State.TransactionState}
    (h : Calls C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- From Paris and before Glamsterdam, a top-level message to `C` (code `CODE`, no value
moved, no precompile), run by
EthLib's `processMessage`, that ends with no error, is a `GoodCall` from its start state to its
end state. -/
theorem goodCall_process {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hdel : NoDelegation1 fork state)
    (K : RealSep message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    GoodCall message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  generalize hres : runFrame (step fork) (step_decreases fork) message.gas
    (processRunner (Meter := Nat) fork message.gas)
    (startFrame message (startState fork message state) substate
      (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = result
  have hmap := processMessage_map_val noValue noPrecompile hres
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
    have start := At.startFrame hmc (startState fork message state) substate
    rw [hst] at start hres
    exact ⟨fork, message, substate, message.gas, message.gas, _,
      s, Nat.le_refl _, rfl, hparis, hglam, hsize, hdel, K, start, hres, hse, by rw [hend]⟩

/-! ## Failed top-level calls and calls with value -/

/-- A top-level message (any code, any fork) run by EthLib's `processMessage` that ends with an
error is an `Untouched` step for every address `C`: the rollback restores the storage of the
state it was sent from (EthLib's `getStorage_processMessage_of_error`). -/
theorem untouched_process_failed {fork : Fork} {message : Message fork}
    {state : State.TransactionState} {substate : Substate}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (herr : ended.val.error ≠ none) (C : Address) : Untouched C state ended.val.state :=
  fun _ => getStorage_processMessage_of_error hproc (Option.isSome_iff_ne_none.mpr herr) C _

/-- From Berlin, a top-level message whose code is `CODE` (no precompile, call data below 2^256
bytes) with a nonzero value, whether it moves the value or not, never ends without an error
(`runFrame_ok_dispatch`: a run of `CODE` that ends with no error has value 0). -/
theorem process_value_fails {fork : Fork} (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate} (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none) (hsize : message.data.size < 2 ^ 256)
    (hv : message.value ≠ 0)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    ended.val.error ≠ none := by
  have key : ∀ (st : State.TransactionState) (ss : Substate)
      (result : Except EvmError (Evm fork Nat)),
      runFrame (step fork) (step_decreases fork) message.gas (processRunner fork message.gas)
        (startFrame message st ss (GasMeter.start message.gas message.reservoir))
        (Nat.le_refl _) = result →
      (processMessage fork message state substate).map Subtype.val =
        result.map (rollbackOnError state) → ended.val.error ≠ none := by
    intro st ss result hres hmap
    rw [hproc] at hmap
    rcases result with e | s
    · cases hmap
    · simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap]
      have hs : s.error ≠ none := fun hok =>
        hv (runFrame_ok_dispatch hfork hsize (At.startFrame hmc st ss) (Nat.le_refl _) hres
          hok).2.1
      unfold rollbackOnError
      split
      · exact hs
      · exact hs
  by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
  · cases hm : (startState fork message state).moveEther fork message.caller
      message.currentTarget message.value with
    | error e =>
      exfalso
      rw [processMessage] at hproc
      simp only [Except.map, ht, ne_eq, not_false_eq_true, and_self, ite_true, bind, pure,
        Except.bind, Except.pure, Except.mapError, hm] at hproc
      cases hproc
    | ok moved => exact key moved _ _ rfl (processMessage_map_val_value ht hm noPrecompile rfl)
  · exact key _ _ _ rfl (processMessage_map_val ht noPrecompile rfl)

/-- From Paris and before Glamsterdam, every top-level message to `C` whose code is `CODE` (no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` to the end, is a step of `Calls C`: a
`GoodCall` when it ends with no error (then its value is 0 or not moved), and an `Untouched`
step when it ends with an error. With a nonzero value it is always the second. `K` is the
hypothesis on keccak (not proved); the error case does not use it. -/
theorem process_step {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hdel : NoDelegation1 fork state)
    (K : RealSep message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_fails (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (goodCall_process hparis hglam hmc ht noPrecompile hsize hdel K hproc herr)
  · exact .inr (untouched_process_failed hproc herr _)

/-- From Paris and before Glamsterdam, a top-level message of `CODE` to `C` that `processMessage` ends either keeps the
invariant (it ended with no error) or leaves every storage word of `C` unchanged (it ended with
an error); in both cases `Inv` at its start gives `Inv` at its end. -/
theorem process_step_inv {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hdel : NoDelegation1 fork state)
    (K : RealSep message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state := by
  rcases process_step hparis hglam hmc noPrecompile hsize hdel K hproc with h | h
  · exact inv_goodCall h hI
  · exact inv_untouched h hI

/-- A top-level message of `CODE` to `C`, then a sequence of steps, is a sequence of steps. -/
theorem calls_process {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam)
    {message : Message fork} {state S' : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hdel : NoDelegation1 fork state)
    (K : RealSep message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : Calls message.currentTarget ended.val.state S') :
    Calls message.currentTarget state S' := by
  rcases process_step hparis hglam hmc noPrecompile hsize hdel K hproc with h | h
  · exact .call h rest
  · exact .other h rest

end OndoVerify

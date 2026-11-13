import QntVerify.Qnt.Invariant
import TokenKit.Evm.Readable
import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# QNT over whole messages and finite sequences of them: supply and who can mint

Hand-written. `supply_step` (Invariant.lean) is about one frame: a run of `CODE` from pc 0 that
ends with no error. Here it is lifted to a whole top-level message as EthLib's `processMessage`
runs it (with the rollback of a failed call), and to any finite sequence of steps, as SHIB's
Seq.lean does. QNT has no CALL, so no hypothesis on the message runner is needed. The meter is
the one-counter meter (`Nat`); the two-counter meter of EIP-8037 is not covered.

`D C S` below is `Supply.D 0 1 C S`: the sum of the 2^160 balance words minus the word of slot 1
(`totalSupply_`). `crowd C S` is the low 160 bits of slot 3 (`crowdsale`).

What the bytes do, and so what is proved:

- `mint_caller`: a run with the selector of `mint` that ends with no error has the address word
  of its caller equal to `crowd`. No hypothesis on keccak.
- `GoodCall C P S S'`: a run of a fresh frame of `CODE` for a message to `C`, from `S`, that ends
  with no error in `S'`, whose caller word satisfies `P`, with the hypotheses of `supply_step`:
  its own fork from Berlin, call data below 2^256 bytes, and the hypothesis on keccak
  `Sep (callKeys message)` (assumed, not proved).
- `Untouched C S S'`: any change that keeps every storage word of `C` (a failed call rolled back,
  transactions to other accounts, fees). For a failed top-level message it is proved
  (`untouched_process_failed`); for the other changes it is the assumption of the step.
- `Calls C P S S'`: a finite sequence of such steps.
- `calls_fixed`: along any sequence, slot 1 (`totalSupply_`) and slot 3 (`crowdsale`) keep their
  word. So `totalSupply()` never changes after deployment, not even by `mint`.
- `calls_D_mono`: along any sequence, `D` does not go down.
- `inv_calls_no_crowdsale`: if no call of the sequence comes from the address in slot 3, then
  `D` is unchanged; in particular `Inv` (sum of balances = `totalSupply_`) is kept.
- `goodCall_mint_D`: a successful `mint` adds its amount word to `D`. So `mint` with a nonzero
  amount does NOT keep `Inv`: the bytecode adds to a balance and never writes slot 1.
- `goodCall_process`, `process_value_fails`, `process_step`, `calls_process`: from Paris, every
  top-level message of `CODE` to `C` that `processMessage` ends is a `GoodCall` (no error) or an
  `Untouched` step (an error: storage as before).
-/

set_option autoImplicit false

namespace QntVerify

open UsdtVerify
open TokenKit
open QntVerify.Paths QntVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The address in slot 3 (`crowdsale`), as an address word. -/
abbrev crowd (C : Address) (S : State.TransactionState) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (storageAt S C 3)

/-- The address word of the caller of a message. -/
abbrev callerWord {fork : Fork} (message : Message fork) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256

/-- Only the address in slot 3 can mint: a run of `CODE` from pc 0 with the selector of `mint`
that ends with no error has the address word of its caller equal to the low 160 bits of slot 3.
No hypothesis on keccak. -/
theorem mint_caller {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    callerWord message = crowd message.currentTarget state := by
  obtain ⟨-, hc2, -⟩ := ok_mint hfork hsize' hsel start hrun hok
  have e := Readable.eq_of_cond hc2
  rw [Readable.div_one, mask_idem] at e
  exact e

/-- `D` reads the storage words of `C` only. -/
theorem Supply.D_congr {b t : U256} {C : Address} {S S' : State.TransactionState}
    (h : ∀ n, storageAt S' C n = storageAt S C n) :
    Supply.D b t C S' = Supply.D b t C S := by
  unfold Supply.D Supply.sumBal
  rw [h t, Supply.sumTo_congr (g := Supply.bal b C S) _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h])]

/-- One run of `CODE` for a message to `C` that ends with no error, from `S` to `S'`, whose
caller word satisfies `P`, under the hypotheses of `supply_step`. -/
def GoodCall (C : Address) (P : U256 → Prop) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (runChild : MessageRunner fork Nat bound) (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .berlin ≤ fork ∧ message.data.size < 2 ^ 256 ∧
    Sep (callKeys message) ∧ P (callerWord message) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A change of state that keeps every storage word of `C`. -/
def Untouched (C : Address) (S S' : State.TransactionState) : Prop :=
  ∀ n, storageAt S' C n = storageAt S C n

/-- A finite sequence of successful calls to `C` (from callers whose word satisfies `P`) and of
changes that keep the storage of `C`. -/
inductive Calls (C : Address) (P : U256 → Prop) :
    State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls C P S S
  | call {S S' S'' : State.TransactionState} : GoodCall C P S S' → Calls C P S' S'' →
      Calls C P S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Calls C P S' S'' →
      Calls C P S S''

/-- What one successful call does: slots 1 and 3 keep their word; `D` is unchanged, or the
caller is the address in slot 3 and `D` grows by some amount (the call is `mint`). -/
theorem goodCall_step {C : Address} {P : U256 → Prop} {S S' : State.TransactionState}
    (h : GoodCall C P S S') :
    storageAt S' C 1 = storageAt S C 1 ∧ storageAt S' C 3 = storageAt S C 3 ∧
      (Supply.D 0 1 C S' = Supply.D 0 1 C S ∨
        (P (crowd C S) ∧ ∃ v : U256, Supply.D 0 1 C S' = Supply.D 0 1 C S + (v.toNat : Int))) := by
  obtain ⟨fork, message, substate, gas, bound, runChild, evm, s, within, hC, hfork, hsize, K,
    hP, start, hrun, hok, rfl⟩ := h
  subst hC
  obtain ⟨hD, h1, h3⟩ := supply_step hfork hsize K start (Ends.run hrun) hok
  refine ⟨h1, h3, ?_⟩
  rcases hD with hD | ⟨hsel, hD⟩
  · exact .inl hD
  · refine .inr ⟨?_, _, hD⟩
    rw [← mint_caller hfork hsize hsel start (Ends.run hrun) hok]
    exact hP

/-- A successful `mint` adds its amount word to `D`, and its caller is the address in slot 3.
With a nonzero amount `Inv` is not kept: the bytecode never writes slot 1. -/
theorem goodCall_mint_D {fork : Fork} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19) (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    callerWord message = crowd message.currentTarget state ∧
      Supply.D 0 1 message.currentTarget s.state =
        Supply.D 0 1 message.currentTarget state + ((loadWord message.data 36 32).toNat : Int) ∧
      (Inv message.currentTarget state → loadWord message.data 36 32 ≠ 0 →
        ¬ Inv message.currentTarget s.state) := by
  have hd := (delta_mint hfork hsize' hsel hsep start hrun hok).1
  refine ⟨mint_caller hfork hsize' hsel start hrun hok, hd, fun hI hne hI' => hne ?_⟩
  have h0 : (loadWord message.data 36 32).toNat = 0 := by
    have a : Supply.D 0 1 message.currentTarget state = 0 := hI
    have b : Supply.D 0 1 message.currentTarget s.state = 0 := hI'
    rw [a, b] at hd
    omega
  exact BitVec.eq_of_toNat_eq h0

/-- Along every finite sequence of steps, slot 1 (`totalSupply_`) and slot 3 (`crowdsale`) keep
their word, and `D` does not go down. -/
theorem calls_fixed {C : Address} {P : U256 → Prop} {S S' : State.TransactionState}
    (h : Calls C P S S') :
    storageAt S' C 1 = storageAt S C 1 ∧ storageAt S' C 3 = storageAt S C 3 ∧
      Supply.D 0 1 C S ≤ Supply.D 0 1 C S' := by
  induction h with
  | nil => exact ⟨rfl, rfl, Int.le_refl _⟩
  | call hg _ ih =>
    obtain ⟨h1, h3, hD⟩ := goodCall_step hg
    obtain ⟨i1, i3, iD⟩ := ih
    refine ⟨i1.trans h1, i3.trans h3, ?_⟩
    rcases hD with hD | ⟨-, v, hD⟩ <;> omega
  | other hu _ ih =>
    obtain ⟨i1, i3, iD⟩ := ih
    have hD := Supply.D_congr (b := 0) (t := 1) hu
    exact ⟨i1.trans (hu 1), i3.trans (hu 3), by omega⟩

/-- `D` does not go down along a sequence of steps. -/
theorem calls_D_mono {C : Address} {P : U256 → Prop} {S S' : State.TransactionState}
    (h : Calls C P S S') : Supply.D 0 1 C S ≤ Supply.D 0 1 C S' :=
  (calls_fixed h).2.2

/-- If no call of the sequence comes from the address in slot 3, `D` is unchanged. -/
theorem calls_D_no_crowdsale {C : Address} {P : U256 → Prop} {S S' : State.TransactionState}
    (h : Calls C P S S') (hP : ¬ P (crowd C S)) :
    Supply.D 0 1 C S' = Supply.D 0 1 C S := by
  induction h with
  | nil => rfl
  | @call S1 S2 S3 hg _ ih =>
    obtain ⟨-, h3, hD⟩ := goodCall_step hg
    have hc : ¬ P (crowd C S2) := by
      show ¬ P (bitwiseAnd _ (storageAt S2 C 3))
      rw [h3]; exact hP
    rcases hD with hD | ⟨hp, -⟩
    · rw [ih hc, hD]
    · exact absurd hp hP
  | @other S1 S2 S3 hu _ ih =>
    have hc : ¬ P (crowd C S2) := by
      show ¬ P (bitwiseAnd _ (storageAt S2 C 3))
      rw [hu 3]; exact hP
    rw [ih hc, Supply.D_congr hu]

/-- If no call of the sequence comes from the address in slot 3, the invariant "the sum of all
balances is `totalSupply_`" is kept. Each call carries its own hypothesis on keccak
`Sep (callKeys message)`. -/
theorem inv_calls_no_crowdsale {C : Address} {P : U256 → Prop} {S S' : State.TransactionState}
    (h : Calls C P S S') (hP : ¬ P (crowd C S)) (hI : Inv C S) : Inv C S' := by
  show Supply.D 0 1 C S' = 0
  rw [calls_D_no_crowdsale h hP]
  exact hI

/-- From Paris, a top-level message to `C` (code `CODE`, no value moved, no precompile), run by
EthLib's `processMessage`, that ends with no error, is a `GoodCall` from its start state to its
end state. -/
theorem goodCall_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {P : U256 → Prop} (hP : P (callerWord message))
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    GoodCall message.currentTarget P state ended.val.state := by
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
    exact ⟨fork, message, substate, message.gas, message.gas, processRunner fork message.gas, _,
      s, Nat.le_refl _, rfl, hberlin, hsize, K, hP, start, hres, hse, by rw [hend]⟩

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

/-- From Paris, every top-level message to `C` whose code is `CODE` (no precompile, call data
below 2^256 bytes), run by EthLib's `processMessage` to the end, is a step of `Calls C`: a
`GoodCall` when it ends with no error (then its value is 0 or not moved), and an `Untouched`
step when it ends with an error. With a nonzero value it is always the second. `K` is the
hypothesis on keccak (not proved); the error case does not use it. -/
theorem process_step {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {P : U256 → Prop} (hP : P (callerWord message))
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget P state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_fails (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · exact .inl (goodCall_process hparis hP hmc ht noPrecompile hsize K hproc herr)
  · exact .inr (untouched_process_failed hproc herr _)

/-- From Paris, a top-level message of `CODE` to `C` that `processMessage` ends, from a caller
that is not the address in slot 3: `Inv` at its start gives `Inv` at its end; and for any caller
the words of slots 1 and 3 are as before. -/
theorem process_step_inv {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    storageAt ended.val.state message.currentTarget 1 = storageAt state message.currentTarget 1 ∧
      storageAt ended.val.state message.currentTarget 3 =
        storageAt state message.currentTarget 3 ∧
      (callerWord message ≠ crowd message.currentTarget state →
        Inv message.currentTarget state → Inv message.currentTarget ended.val.state) := by
  rcases process_step (P := fun w => w = callerWord message) hparis rfl hmc noPrecompile hsize K
    hproc with h | h
  · obtain ⟨h1, h3, hD⟩ := goodCall_step h
    refine ⟨h1, h3, fun hne hI => ?_⟩
    rcases hD with hD | ⟨hp, -⟩
    · show Supply.D 0 1 _ _ = 0
      rw [hD]; exact hI
    · exact absurd hp.symm hne
  · refine ⟨h 1, h 3, fun _ hI => ?_⟩
    show Supply.D 0 1 _ _ = 0
    rw [Supply.D_congr h]; exact hI

/-- A top-level message of `CODE` to `C`, then a sequence of steps, is a sequence of steps. -/
theorem calls_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state S' : State.TransactionState} {substate : Substate}
    {P : U256 → Prop} (hP : P (callerWord message))
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : Calls message.currentTarget P ended.val.state S') :
    Calls message.currentTarget P state S' := by
  rcases process_step hparis hP hmc noPrecompile hsize K hproc with h | h
  · exact .call h rest
  · exact .other h rest

end QntVerify

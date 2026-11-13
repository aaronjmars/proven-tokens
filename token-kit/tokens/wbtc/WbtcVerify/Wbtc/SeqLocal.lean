import WbtcVerify.Wbtc.AnyLocal
import WbtcVerify.Wbtc.Seq

/-!
# The supply invariant over whole messages and finite sequences, RUN-LOCAL keccak hypotheses

Written by hand (not generated). The results of `Seq.lean` without the global idealizations
`SepAll` and `Reenter.NoCollision CODE`. Each message of a sequence carries its own run-local
condition `CleanW`:

- each message `m` that ENTERS the code of WBTC at `L` during the run of the top-level message
  (the message itself, and every nested call at any depth, reentry included) has
  `Sep (callKeys m)`: upstream's local hypothesis, for the messages that really occur;
- each code that a creation DEPOSITS during the run and that has the keccak hash of the code of
  WBTC is the code of WBTC.

- `process_good_local`: from Berlin and before Glamsterdam, a sane top-level message whose run
  is clean, that `processMessage` ends (with or without an error), leaves a good state good.
- `create_good_local`: the same for a top-level creation at another address than `L`.
- `MsgL`, `CreateL`, `RunL` (with `Other` of `Seq.lean`), `good_runL`, `inv_runL`: finite
  sequences. What a sequence keeps is the EQUATION "sum of balances = totalSupply_"; the supply
  itself changes with mint and burn.
- `cleanW_of_sepList`: the form with ONE finite list `A` of address words chosen by the caller:
  `Sep A`, and every message that enters WBTC during the run takes its mapping keys in `A`.
- `Msg.toLocal`, `Run.toLocal`, `inv_run_of_global`: under the global hypotheses every `Msg` is
  a `MsgL`, so the theorems of `Seq.lean` are corollaries of the ones here.

Hypotheses that stay:
Berlin ≤ fork < Glamsterdam, and the run-local conditions (about keccak on the finitely many
concrete values of each run; NOT proved). No gas cap.
Not covered: the end of a transaction (SELFDESTRUCT deletions, cleanup, fees) and a creation at
`L` itself are `Other` steps or excluded; they are not derived from the model.
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The run of the top-level message is clean for WBTC at `L`: each message that enters `L`
during the run has `Sep (callKeys ·)`, and each deposited code with the hash of the code of WBTC
is that code. -/
abbrev CleanW {fork : Fork} (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) : Prop :=
  Trace.Clean L CODE (fun m : Message fork => SepMsg m) message state substate meter

/-- The same for the run of a top-level creation. -/
abbrev CleanCreateW {fork : Fork} (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) : Prop :=
  Trace.CleanCreate L CODE (fun m : Message fork => SepMsg m) message state substate meter

/-- RUN-LOCAL. From Berlin and before Glamsterdam, every sane top-level message whose run is
clean, that EthLib's `processMessage` ends, to any account, with or without an error, leaves a
good state good. -/
theorem process_good_local {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (sane : Reenter.Sane L CODE message) (g : GoodWbtc L state)
    (clean : CleanW L message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodWbtc L ended.val.state :=
  Trace.processMessage_good_local (storageOnly_inv L) (frameKeepsQ hfork hglam message.gas L)
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- RUN-LOCAL. The same for a top-level creation at another address than `L`. -/
theorem create_good_local {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hne : message.currentTarget ≠ L) (g : GoodWbtc L state)
    (clean : CleanCreateW L message state substate meter)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    GoodWbtc L ended.val.state :=
  Trace.processCreateMessage_good_local (storageOnly_inv L)
    (frameKeepsQ hfork hglam message.gas L) code_not_delegated (Nat.le_refl _) hne g clean h

/-- One top-level message, to any account, run by `processMessage` to its end, with a clean
run. -/
def MsgL (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧
    Reenter.Sane L CODE message ∧ CleanW L message S substate meter ∧
    processMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- One top-level creation at another address than `L`, run by `processCreateMessage` to its
end, with a clean run. -/
def CreateL (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧
    message.currentTarget ≠ L ∧ CleanCreateW L message S substate meter ∧
    processCreateMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- A finite sequence of top-level messages and creations with clean runs, and of changes that
keep the code and the storage of `L`. -/
inductive RunL (L : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : RunL L S S
  | msg {S S' S'' : State.TransactionState} : MsgL L S S' → RunL L S' S'' → RunL L S S''
  | create {S S' S'' : State.TransactionState} : CreateL L S S' → RunL L S' S'' → RunL L S S''
  | other {S S' S'' : State.TransactionState} : Other L S S' → RunL L S' S'' → RunL L S S''

/-- One message with a clean run leaves a good state good. -/
theorem good_msgL {L : Address} {S S' : State.TransactionState} (h : MsgL L S S')
    (g : GoodWbtc L S) : GoodWbtc L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, sane, clean, hproc,
    rfl⟩ := h
  exact process_good_local hfork hglam sane g clean hproc

/-- One creation with a clean run leaves a good state good. -/
theorem good_createL {L : Address} {S S' : State.TransactionState} (h : CreateL L S S')
    (g : GoodWbtc L S) : GoodWbtc L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hne, clean, hproc,
    rfl⟩ := h
  exact create_good_local hfork hglam hne g clean hproc

/-- A good state stays good along every finite sequence of messages with clean runs. No global
hypothesis on keccak. -/
theorem good_runL {L : Address} {S S' : State.TransactionState} (h : RunL L S S')
    (g : GoodWbtc L S) : GoodWbtc L S' := by
  induction h with
  | nil => exact g
  | msg hm _ ih => exact ih (good_msgL hm g)
  | create hc _ ih => exact ih (good_createL hc g)
  | other ho _ ih => exact ih (good_other ho g)

/-- THE SUM OF THE BALANCES STAYS EQUAL TO `totalSupply_`, RUN-LOCAL keccak hypotheses. Along
every finite sequence of top-level messages and creations (to any account, `reclaimToken` with
any token included, reentry included) whose runs are clean: if the sum of all balances of WBTC
is the word of slot 1 before, it is after. The supply itself can change (mint, burn); the
equation is what is kept. -/
theorem inv_runL {L : Address} {S S' : State.TransactionState} (h : RunL L S S')
    (hold : Reenter.HoldsCode L CODE S) (hinv : Inv L S) : Inv L S' :=
  (good_runL h ⟨hold, hinv⟩).2

/-! ## The form with a finite list of address words chosen by the caller -/

/-- The separation of slots for a list gives it for every list of words of that list. -/
theorem Sep.restrict {A B : List U256} (h : Sep A) (hs : ∀ x ∈ B, x ∈ A) : Sep B :=
  ⟨h.total, fun x hx => h.uniq x (hs x hx),
    fun o ho s hs' => h.allow o (hs o ho) s (hs s hs'), h.fixed⟩

/-- ONE finite list `A` of address words with `Sep A`, and the side condition that every message
that enters the code of WBTC at `L` during the run uses only words of `A` as mapping keys (and
that no deposited code collides): the run is clean. -/
theorem cleanW_of_sepList {fork : Fork} {A : List U256} (hA : Sep A) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    (h : Trace.Clean L CODE (fun m : Message fork => ∀ x ∈ callKeys m, x ∈ A) message state
      substate meter) :
    CleanW L message state substate meter :=
  Trace.Clean.mono (fun _ hm => hA.restrict hm) h

/-! ## The global form is a corollary -/

/-- Under the global hypotheses every run is clean. -/
theorem cleanW_of_sepAll_noCollision {fork : Fork} (K : SepAll)
    (hcol : Reenter.NoCollision CODE) (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) :
    CleanW L message state substate meter :=
  Trace.clean_of_global (fun m _ => K.msg m) hcol message state substate meter

theorem Msg.toLocal (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Msg L S S') : MsgL L S S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, sane, hproc, rfl⟩ := h
  exact ⟨fork, message, substate, meter, held, ended, hfork, hglam, sane,
    cleanW_of_sepAll_noCollision K hcol L message S substate meter, hproc, rfl⟩

theorem Run.toLocal (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') : RunL L S S' := by
  induction h with
  | nil => exact .nil _
  | msg hm _ ih => exact .msg (hm.toLocal K hcol) ih
  | other ho _ ih => exact .other ho ih

/-- `inv_run_sepAll_noCollision` (Seq.lean) is a corollary of the run-local theorem. -/
theorem inv_run_of_global (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (hold : Reenter.HoldsCode L CODE S)
    (hinv : Inv L S) : Inv L S' :=
  inv_runL (h.toLocal K hcol) hold hinv

end WbtcVerify

import LinkVerify.Link.AnyLocal
import LinkVerify.Link.Seq

/-!
# The supply invariant over whole messages, creations and finite sequences, RUN-LOCAL keccak

Written by hand (not generated). Fix of audit 4, LINK-1 and LINK-2. The results of `Seq.lean`
without the global idealizations `SepAll` and `Reenter.NoCollision CODE`. Each message of a
sequence carries its own run-local condition `CleanL`:

- each message `m` that ENTERS the code of LINK at `L` during the run of the top-level message
  (the message itself, and every nested call at any depth, reentry included) has
  `Sep (callKeys m)`: upstream's local hypothesis, for the messages that really occur;
- each code that a creation DEPOSITS during the run and that has the keccak hash of the code of
  LINK is the code of LINK.

- `process_good_local`: from Berlin and before Glamsterdam, a sane top-level message whose run
  is clean, that `processMessage` ends (with or without an error), leaves a good state good.
- `create_good_local`: the same for a top-level creation at another address than `L`. A
  transaction that creates a contract runs `processCreateMessage` (not `processMessage`); its
  init code can call LINK. This closes LINK-2 with the run-local form of
  `Reenter.processCreateMessage_good`.
- `MsgL`, `CreateL`, `RunL` (with `Other` of `Seq.lean`), `good_runL`, `inv_runL`: finite
  sequences. THE HEADLINE: the sum of the balances stays `10^27`.
- `cleanL_of_sepList`: the form with ONE finite list `A` of address words chosen by the caller:
  `Sep A`, and every message that enters LINK during the run takes its mapping keys in `A`.
- `Msg.toLocal`, `Create.toLocal`, `Run.toLocal`, `inv_run_of_global`: under the global
  hypotheses every `Msg` is a `MsgL`, so the theorems of `Seq.lean` are corollaries of the ones
  here.

Hypotheses that stay (all in the statements):
- Berlin ≤ fork < Glamsterdam and `message.gas ≤ GAS_CAP` (`2^60 - 1`) for each step;
- `Reenter.Sane L CODE message` for each top-level message: when it goes to `L` it runs the
  code of LINK, is a call, and its data is below 2^256 bytes. It is ASSUMED of the top-level
  message, not derived from the state and from the way a transaction builds its message;
- `CleanL` / `CleanCreateL` for each step (about keccak on the finitely many concrete values of
  that run; NOT proved in general, see `TraceWit.lean` for runs where it is);
- `Other` steps (fees, refunds, the end of a transaction, EIP-7702 authorizations) are ASSUMED
  to keep the code and the storage of `L`; not derived from EthLib's transaction layer;
- a good state at the start: `Reenter.HoldsCode L CODE S` and `Inv L S`. The constructor and the
  history before Berlin are not in the proof; `Base.lean` shows a good state exists.
Not covered: a creation at `L` itself (excluded by `CreateL`).
-/

set_option autoImplicit false

namespace LinkVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The run of the top-level message is clean for LINK at `L`: each message that enters `L`
during the run has `Sep (callKeys ·)`, and each deposited code with the hash of the code of LINK
is that code. -/
abbrev CleanL {fork : Fork} (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) : Prop :=
  Trace.Clean L CODE (fun m : Message fork => SepMsg m) message state substate meter

/-- The same for the run of a top-level creation. -/
abbrev CleanCreateL {fork : Fork} (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) : Prop :=
  Trace.CleanCreate L CODE (fun m : Message fork => SepMsg m) message state substate meter

/-- RUN-LOCAL. From Berlin and before Glamsterdam, every sane top-level message whose run is
clean, that EthLib's `processMessage` ends, to any account, with or without an error, leaves a
good state good. -/
theorem process_good_local {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hG : message.gas ≤ GAS_CAP)
    (sane : Reenter.Sane L CODE message) (g : GoodLink L state)
    (clean : CleanL L message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodLink L ended.val.state :=
  Trace.processMessage_good_local (storageOnly_inv L) (frameKeepsQ hfork hglam L)
    code_not_delegated hG sane g clean h

/-- RUN-LOCAL. The same for a top-level creation at another address than `L`, run by
`processCreateMessage` (what a transaction with no target runs). -/
theorem create_good_local {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hG : message.gas ≤ GAS_CAP)
    (hne : message.currentTarget ≠ L) (g : GoodLink L state)
    (clean : CleanCreateL L message state substate meter)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    GoodLink L ended.val.state :=
  Trace.processCreateMessage_good_local (storageOnly_inv L) (frameKeepsQ hfork hglam L)
    code_not_delegated hG hne g clean h

/-- One top-level message, to any account, run by `processMessage` to its end, with a clean
run. -/
def MsgL (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧ message.gas ≤ GAS_CAP ∧
    Reenter.Sane L CODE message ∧ CleanL L message S substate meter ∧
    processMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- One top-level creation at another address than `L`, run by `processCreateMessage` to its
end, with a clean run. -/
def CreateL (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧ message.gas ≤ GAS_CAP ∧
    message.currentTarget ≠ L ∧ CleanCreateL L message S substate meter ∧
    processCreateMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- A finite sequence of top-level messages and creations with clean runs, and of changes that
keep the code and the storage of `L` (`Other`, an assumption on the steps that are no
message). -/
inductive RunL (L : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : RunL L S S
  | msg {S S' S'' : State.TransactionState} : MsgL L S S' → RunL L S' S'' → RunL L S S''
  | create {S S' S'' : State.TransactionState} : CreateL L S S' → RunL L S' S'' → RunL L S S''
  | other {S S' S'' : State.TransactionState} : Other L S S' → RunL L S' S'' → RunL L S S''

/-- One message with a clean run leaves a good state good. -/
theorem good_msgL {L : Address} {S S' : State.TransactionState} (h : MsgL L S S')
    (g : GoodLink L S) : GoodLink L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, sane, clean, hproc,
    rfl⟩ := h
  exact process_good_local hfork hglam hG sane g clean hproc

/-- One creation with a clean run leaves a good state good. -/
theorem good_createL {L : Address} {S S' : State.TransactionState} (h : CreateL L S S')
    (g : GoodLink L S) : GoodLink L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, hne, clean, hproc,
    rfl⟩ := h
  exact create_good_local hfork hglam hG hne g clean hproc

/-- A good state stays good along every finite sequence of messages and creations with clean
runs. No global hypothesis on keccak. -/
theorem good_runL {L : Address} {S S' : State.TransactionState} (h : RunL L S S')
    (g : GoodLink L S) : GoodLink L S' := by
  induction h with
  | nil => exact g
  | msg hm _ ih => exact ih (good_msgL hm g)
  | create hc _ ih => exact ih (good_createL hc g)
  | other ho _ ih => exact ih (good_other ho g)

/-- THE SUM OF THE BALANCES STAYS `10^27`, RUN-LOCAL keccak hypotheses. Along every finite
sequence of top-level messages and creations (to any account, `transferAndCall` to any receiver
included, reentry included) whose runs are clean, and of `Other` steps: if the account `L` holds
the code of LINK and the sum of all balances is the constant `10^27` that `totalSupply()`
returns before, the sum is `10^27` after. -/
theorem inv_runL {L : Address} {S S' : State.TransactionState} (h : RunL L S S')
    (hold : Reenter.HoldsCode L CODE S) (hinv : Inv L S) : Inv L S' :=
  (good_runL h ⟨hold, hinv⟩).2

/-! ## The form with a finite list of address words chosen by the caller -/

/-- The separation of slots for a list gives it for every list of words of that list. -/
theorem Sep.restrict {A B : List U256} (h : Sep A) (hs : ∀ x ∈ B, x ∈ A) : Sep B :=
  ⟨fun x hx => h.uniq x (hs x hx), fun o ho s hs' => h.allow o (hs o ho) s (hs s hs')⟩

/-- ONE finite list `A` of address words with `Sep A`, and the side condition that every message
that enters the code of LINK at `L` during the run uses only words of `A` as mapping keys (and
that no deposited code collides): the run is clean. -/
theorem cleanL_of_sepList {fork : Fork} {A : List U256} (hA : Sep A) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    (h : Trace.Clean L CODE (fun m : Message fork => ∀ x ∈ callKeys m, x ∈ A) message state
      substate meter) :
    CleanL L message state substate meter :=
  Trace.Clean.mono (fun _ hm => hA.restrict hm) h

/-! ## The global form is a corollary -/

/-- Under the global hypotheses every run is clean. -/
theorem cleanL_of_sepAll_noCollision {fork : Fork} (K : SepAll)
    (hcol : Reenter.NoCollision CODE) (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) :
    CleanL L message state substate meter :=
  Trace.clean_of_global (fun m _ => K.msg m) hcol message state substate meter

/-- Under the global hypotheses every run of a creation is clean. -/
theorem cleanCreateL_of_sepAll_noCollision {fork : Fork} (K : SepAll)
    (hcol : Reenter.NoCollision CODE) (L : Address) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (meter : Nat) :
    CleanCreateL L message state substate meter :=
  Trace.cleanCreate_of_global (fun m _ => K.msg m) hcol message state substate meter

theorem Msg.toLocal (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Msg L S S') : MsgL L S S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, sane, hproc, rfl⟩ := h
  exact ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, sane,
    cleanL_of_sepAll_noCollision K hcol L message S substate meter, hproc, rfl⟩

theorem Create.toLocal (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Create L S S') : CreateL L S S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, hne, hproc, rfl⟩ := h
  exact ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, hne,
    cleanCreateL_of_sepAll_noCollision K hcol L message S substate meter, hproc, rfl⟩

theorem Run.toLocal (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') : RunL L S S' := by
  induction h with
  | nil => exact .nil _
  | msg hm _ ih => exact .msg (hm.toLocal K hcol) ih
  | create hc _ ih => exact .create (hc.toLocal K hcol) ih
  | other ho _ ih => exact .other ho ih

/-- `inv_run_sepAll_noCollision` (Seq.lean) is a corollary of the run-local theorem. -/
theorem inv_run_of_global (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (hold : Reenter.HoldsCode L CODE S)
    (hinv : Inv L S) : Inv L S' :=
  inv_runL (h.toLocal K hcol) hold hinv

end LinkVerify

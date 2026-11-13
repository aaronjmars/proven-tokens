import LinkVerify.Link.Any

/-!
# The supply invariant over whole messages and finite sequences, GLOBAL keccak hypotheses

Written by hand (not generated). This file is the OLD form: it assumes the GLOBAL idealizations
`SepAll` and `Reenter.NoCollision CODE`, and every theorem that does has `sepAll_noCollision` in
its name. Both hypotheses are almost certainly false as mathematics (audit 4, LINK-1), so these
theorems are NOT usable facts. `SeqLocal.lean` has the same results on run-local hypotheses:
those are the headline theorems. This file is kept for the definitions that both forms share
(`GoodLink`, `Other`, `good_other`) and so that the old shape stays stated as a corollary
(`SeqLocal.inv_run_of_global`).

`supply_all_real_sepAll_noCollision` is about one frame of the code of LINK. Here the invariant
is carried over every top-level message that EthLib's `processMessage` runs (with the move of
value, the precompiles, the rollback of a failed call, and every nested call and creation), to
ANY account, over every top-level creation that `processCreateMessage` runs at another address
than `L`, and over finite sequences of them.

A state is good (`GoodLink L S`) when the account `L` holds the code of LINK and the sum of the
balances is `10^27`.

- `process_good_sepAll_noCollision`: from Berlin and before Glamsterdam, a top-level message to
  any account that `processMessage` ends, with or without an error, leaves a good state good.
  `Reenter.Sane`: when the message goes to `L` it runs the code of LINK, is a call, and its data
  is below 2^256 bytes.
- `create_good_sepAll_noCollision`: the same for a top-level creation (a transaction with no
  target runs `processCreateMessage`, not `processMessage`) at another address than `L`.
- `Msg L S S'`: one such message from `S` to `S'`. `Create L S S'`: one such creation.
  `Other L S S'`: any other change that keeps the code and the storage of `L` (fees, the end of
  a transaction); ASSUMED, not derived from EthLib's transaction layer.
- `Run L S S'`: a finite sequence of the three. `good_run_sepAll_noCollision`,
  `inv_run_sepAll_noCollision`: a good state stays good.

Hypotheses that stay: `SepAll` and `Reenter.NoCollision CODE` (keccak, GLOBAL, not proved,
almost certainly false), Berlin ≤ fork < Glamsterdam, the gas of each message at most `GAS_CAP`
(`2^60 - 1`), a good state at the start (no state is shown good here; see `Base.lean`).
Not covered: the end of a transaction (SELFDESTRUCT deletions, cleanup, fees) and a creation at
`L` itself are `Other` steps or excluded; they are not derived from the model.
-/

set_option autoImplicit false

namespace LinkVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The account `L` holds the code of LINK and the sum of its balances is `10^27`. -/
abbrev GoodLink (L : Address) (S : State.TransactionState) : Prop :=
  Reenter.Good L CODE (Inv L) S

/-- GLOBAL keccak hypotheses (NOT a usable fact). From Berlin and before Glamsterdam, every sane
top-level message that EthLib's `processMessage` ends, to any account, with or without an error,
leaves a good state good. -/
theorem process_good_sepAll_noCollision {fork : Fork} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hG : message.gas ≤ GAS_CAP)
    (sane : Reenter.Sane L CODE message) (g : GoodLink L state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodLink L ended.val.state :=
  Reenter.processMessage_good (storageOnly_inv L) (frameKeeps_sepAll hfork hglam K L) hcol
    code_not_delegated hG sane g h

/-- GLOBAL keccak hypotheses (NOT a usable fact). The same for a top-level creation at another
address than `L`, run by `processCreateMessage`. -/
theorem create_good_sepAll_noCollision {fork : Fork} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hG : message.gas ≤ GAS_CAP)
    (hne : message.currentTarget ≠ L) (g : GoodLink L state)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    GoodLink L ended.val.state :=
  Reenter.processCreateMessage_good (storageOnly_inv L) (frameKeeps_sepAll hfork hglam K L) hcol
    code_not_delegated hG hne g h

/-- One top-level message, to any account, run by `processMessage` to its end. -/
def Msg (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧ message.gas ≤ GAS_CAP ∧
    Reenter.Sane L CODE message ∧
    processMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- One top-level creation at another address than `L`, run by `processCreateMessage` to its
end. -/
def Create (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧ message.gas ≤ GAS_CAP ∧
    message.currentTarget ≠ L ∧
    processCreateMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- Any other change of state that keeps the code and every storage word of `L`. This is an
ASSUMPTION about the steps of a transaction that are no message (fees, refunds, the end of a
transaction): it is not derived from EthLib's transaction layer here. -/
def Other (L : Address) (S S' : State.TransactionState) : Prop :=
  (Reenter.HoldsCode L CODE S → Reenter.HoldsCode L CODE S') ∧
    ∀ k, S'.getStorage L k = S.getStorage L k

/-- A finite sequence of top-level messages, of top-level creations at another address than `L`,
and of changes that keep the code and the storage of `L`. -/
inductive Run (L : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Run L S S
  | msg {S S' S'' : State.TransactionState} : Msg L S S' → Run L S' S'' → Run L S S''
  | create {S S' S'' : State.TransactionState} : Create L S S' → Run L S' S'' → Run L S S''
  | other {S S' S'' : State.TransactionState} : Other L S S' → Run L S' S'' → Run L S S''

/-- One message leaves a good state good (GLOBAL keccak hypotheses). -/
theorem good_msg_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Msg L S S') (g : GoodLink L S) : GoodLink L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, sane, hproc, rfl⟩ := h
  exact process_good_sepAll_noCollision hfork hglam K hcol hG sane g hproc

/-- One creation leaves a good state good (GLOBAL keccak hypotheses). -/
theorem good_create_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE)
    {L : Address} {S S' : State.TransactionState} (h : Create L S S') (g : GoodLink L S) :
    GoodLink L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, hG, hne, hproc, rfl⟩ := h
  exact create_good_sepAll_noCollision hfork hglam K hcol hG hne g hproc

/-- A change that keeps the code and the storage of `L` leaves a good state good. -/
theorem good_other {L : Address} {S S' : State.TransactionState} (h : Other L S S')
    (g : GoodLink L S) : GoodLink L S' :=
  ⟨h.1 g.1, storageOnly_inv L S S' h.2 g.2⟩

/-- A good state stays good along every finite sequence of messages and creations (GLOBAL keccak
hypotheses, NOT a usable fact). -/
theorem good_run_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (g : GoodLink L S) : GoodLink L S' := by
  induction h with
  | nil => exact g
  | msg hm _ ih => exact ih (good_msg_sepAll_noCollision K hcol hm g)
  | create hc _ ih => exact ih (good_create_sepAll_noCollision K hcol hc g)
  | other ho _ ih => exact ih (good_other ho g)

/-- The sum of the balances stays `10^27` along every finite sequence of top-level messages and
creations, under the GLOBAL keccak hypotheses (almost certainly false, so NOT a usable fact).
The run-local form is `inv_runL` (SeqLocal.lean). -/
theorem inv_run_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (hold : Reenter.HoldsCode L CODE S)
    (hinv : Inv L S) : Inv L S' :=
  (good_run_sepAll_noCollision K hcol h ⟨hold, hinv⟩).2

end LinkVerify

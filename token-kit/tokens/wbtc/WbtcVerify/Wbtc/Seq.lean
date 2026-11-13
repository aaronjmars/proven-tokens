import WbtcVerify.Wbtc.Any

/-!
# The supply invariant over whole messages and finite sequences, GLOBAL keccak hypotheses

Written by hand (not generated). This file is LINK's form: it assumes the GLOBAL idealizations
`SepAll` and `Reenter.NoCollision CODE`, and every theorem that does has `sepAll_noCollision` in
its name. `SeqLocal.lean` has the same results on run-local hypotheses; prefer those.

`supply_all_real_sepAll_noCollision` is about one frame of the code of WBTC. Here the invariant
is carried over every top-level message that EthLib's `processMessage` runs (the move of value,
the precompiles, the rollback of a failed call, every nested call and creation), to ANY account,
and over finite sequences of such messages.

A state is good (`GoodWbtc L S`) when the account `L` holds the code of WBTC and the sum of the
balances is the word `totalSupply_` (slot 1).

- `process_good_sepAll_noCollision`: from Berlin and before Glamsterdam, a top-level message (to
  any account) that `processMessage` ends, with or without an error, leaves a good state good.
  `Reenter.Sane`: when the message goes to `L` it runs the code of WBTC, is a call, and its data
  is below 2^256 bytes. No gas cap.
- `Msg L S S'`: one such message from `S` to `S'`. `Other L S S'`: any other change that keeps
  the code and the storage of `L` (fees, the end of a transaction); assumed, not derived.
- `Run L S S'`: a finite sequence of both. `good_run_sepAll_noCollision`,
  `inv_run_sepAll_noCollision`: a good state stays good.

What a sequence keeps: the EQUATION "sum of balances = totalSupply_", not a constant. The total
supply of WBTC changes (mint adds, burn subtracts; `Invariant.lean` has the exact change of each
function), so nothing here says that the supply stays the same.

Hypotheses that stay: `SepAll` and `Reenter.NoCollision CODE` (keccak, global, not proved),
Berlin ≤ fork < Glamsterdam.
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

/-- The account `L` holds the code of WBTC and the sum of its balances is `totalSupply_`. -/
abbrev GoodWbtc (L : Address) (S : State.TransactionState) : Prop :=
  Reenter.Good L CODE (Inv L) S

/-- GLOBAL keccak hypotheses. From Berlin and before Glamsterdam, every sane top-level message
that EthLib's `processMessage` ends, to any account, with or without an error, leaves a good
state good. -/
theorem process_good_sepAll_noCollision {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {message : Message fork} {state : State.TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (sane : Reenter.Sane L CODE message) (g : GoodWbtc L state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodWbtc L ended.val.state :=
  Reenter.processMessage_good (storageOnly_inv L)
    (frameKeeps_sepAll hfork hglam K message.gas L) hcol code_not_delegated (Nat.le_refl _)
    sane g h

/-- One top-level message, to any account, run by `processMessage` to its end. -/
def Msg (L : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (meter : Nat)
    (held : GasMeter.gasHeld meter ≤ message.gas)
    (ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }),
    .berlin ≤ fork ∧ fork < .glamsterdam ∧
    Reenter.Sane L CODE message ∧
    processMessage fork message S substate meter held = .ok ended ∧ S' = ended.val.state

/-- Any other change of state that keeps the code and every storage word of `L`. -/
def Other (L : Address) (S S' : State.TransactionState) : Prop :=
  (Reenter.HoldsCode L CODE S → Reenter.HoldsCode L CODE S') ∧
    ∀ k, S'.getStorage L k = S.getStorage L k

/-- A finite sequence of top-level messages and of changes that keep the code and the storage of
`L`. -/
inductive Run (L : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Run L S S
  | msg {S S' S'' : State.TransactionState} : Msg L S S' → Run L S' S'' → Run L S S''
  | other {S S' S'' : State.TransactionState} : Other L S S' → Run L S' S'' → Run L S S''

/-- One message leaves a good state good (GLOBAL keccak hypotheses). -/
theorem good_msg_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Msg L S S') (g : GoodWbtc L S) : GoodWbtc L S' := by
  obtain ⟨fork, message, substate, meter, held, ended, hfork, hglam, sane, hproc, rfl⟩ := h
  exact process_good_sepAll_noCollision hfork hglam K hcol sane g hproc

/-- A change that keeps the code and the storage of `L` leaves a good state good. -/
theorem good_other {L : Address} {S S' : State.TransactionState} (h : Other L S S')
    (g : GoodWbtc L S) : GoodWbtc L S' :=
  ⟨h.1 g.1, storageOnly_inv L S S' h.2 g.2⟩

/-- A good state stays good along every finite sequence of messages (GLOBAL keccak
hypotheses). -/
theorem good_run_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (g : GoodWbtc L S) : GoodWbtc L S' := by
  induction h with
  | nil => exact g
  | msg hm _ ih => exact ih (good_msg_sepAll_noCollision K hcol hm g)
  | other ho _ ih => exact ih (good_other ho g)

/-- THE SUM OF THE BALANCES STAYS EQUAL TO `totalSupply_` (GLOBAL keccak hypotheses). Along every
finite sequence of top-level messages (to any account, `reclaimToken` with any token included):
if the sum of all balances of WBTC is the word of slot 1 before, it is after. The supply itself
can change (mint, burn); the equation is what is kept. -/
theorem inv_run_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE) {L : Address}
    {S S' : State.TransactionState} (h : Run L S S') (hold : Reenter.HoldsCode L CODE S)
    (hinv : Inv L S) : Inv L S' :=
  (good_run_sepAll_noCollision K hcol h ⟨hold, hinv⟩).2

end WbtcVerify

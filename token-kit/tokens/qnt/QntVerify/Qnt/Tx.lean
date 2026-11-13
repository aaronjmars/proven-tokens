import QntVerify.Qnt.Seq
import TokenKit.Seq.Supply

/-!
# QNT over whole transactions, at any depth, and over any finite list of them

`supply_step` (Invariant.lean) is about one frame of the code of QNT. `Seq.lean` lifts it to one
top-level message, and its `Calls` leaves "every other change keeps the storage of `C`" as an
assumption of each step (`Untouched`; fix 2 of audit 4). This file removes that assumption with
the shared library `TokenKit.Seq` (Frame.lean, Run.lean, Tx.lean, Supply.lean): the theorems
here are about EthLib's REAL runner and EthLib's REAL transaction function.

QNT is special: "the sum of all balances is `totalSupply_`" (`Inv`) is NOT an invariant of the
bytecode. `mint`, which only the address in slot 3 (`crowdsale`) can call, adds to a balance and
never writes slot 1 (`goodCall_mint_D` of Seq.lean). So nothing here is named `supply_...` with
no condition. What IS invariant, and what this file states:

1. With no condition on who calls (`Floor`): slot 1 (`totalSupply_`) and slot 3 (`crowdsale`)
   keep their word, and `D` (the sum of all balances minus the word of slot 1) never goes down.
   - `storageOnly_floor`, `frameKeepsQ_floor`: what the library asks for.
   - `floor_message_any_depth`: a call at any depth, with or without an error.
   - `fixed_mono_transaction`: one whole transaction of EthLib's `processTransaction`.
   - `fixed_mono_any_transactions`: THE FIRST HEADLINE. Any finite list of transactions.
2. When no message that enters the code of QNT comes from the address in slot 3 (`NoCrowdMsg`):
   `D` is unchanged, so `Inv` is kept.
   - `frameKeepsQ_noCrowd`, `noCrowd_message_any_depth`, `inv_transaction_no_crowdsale`.
   - `inv_any_transactions_no_crowdsale`: THE SECOND HEADLINE. `Inv` after any finite list of
     transactions in which no message that enters QNT comes from the address in slot 3.
   - `inv_from_zero_no_crowdsale`: the same from the base case (all-zero storage; there slot 3
     holds the address 0).

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction. It is RUN-LOCAL: it speaks of the finitely many events of
   this one run only.
   - `call`, `create`: each message that really enters the code at `C` during the run satisfies
     `Q`, and each code that a creation really deposits during the run, when it has the keccak
     hash of the code of QNT, is that code (no collision of keccak on the codes this run
     deposits, NOT proved). For part 1, `Q` is `SepMsg`: `Sep (callKeys m)`, a hypothesis on
     keccak for three address words, NOT proved. For part 2, `Q` is `NoCrowdMsg`: `Sep (callKeys
     m)` and the address word of the caller of `m` is not the low 160 bits of slot 3 in the
     state that the frame of `m` starts from. The second half is a hypothesis on WHO CALLS, not
     on keccak: it leaves out every call by the crowdsale address (a successful `mint`
     included), at any depth.
   - `auths`: no authorization of the transaction sets a code with the hash of the code of QNT.
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The fork of each transaction is from Dencun and before Glamsterdam. Before Dencun,
   SELFDESTRUCT can delete an account that was not created in the same transaction, and this
   file does not prove that the code of QNT never runs it. From Glamsterdam the gas meter has
   two counters and the proofs are for the one-counter meter.
3. At the start, `C` holds the code of QNT (`Seq.HoldsCode`); for part 2, `Inv` holds too; in
   `inv_from_zero_no_crowdsale`, the storage of `C` is all zero instead.

Not covered: what a block does between transactions (withdrawals, the system calls of
EIP-4788, 2935, 7002, 7251, block rewards), and the constructor run that leaves the real start
state of QNT (the real storage of QNT is not all zero).
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
open EthLib.Execution.State (TransactionState BlockState)
open EthLib.Execution.Transactions

/-- The hypothesis on keccak of one message: `Sep` of its three address words. The state that
the frame starts from is not used. -/
abbrev SepMsg (fork : Fork) (m : Message fork) (_ : TransactionState) : Prop := Sep (callKeys m)

/-- The hypothesis on keccak of one message, and: its caller is not the address in slot 3
(`crowdsale`) of the account it runs at, in the state `s` that its frame starts from. -/
abbrev NoCrowdMsg (fork : Fork) (m : Message fork) (s : TransactionState) : Prop :=
  Sep (callKeys m) ∧ callerWord m ≠ crowd m.currentTarget s

/-- The code of QNT is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of QNT is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of QNT delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- `D` reads the storage words of `C` only (in the form the library uses). -/
theorem D_of_getStorage {C : Address} {S S' : TransactionState}
    (h : ∀ k, S'.getStorage C k = S.getStorage C k) :
    Supply.D 0 1 C S' = Supply.D 0 1 C S := by
  unfold Supply.D
  rw [Seq.sumBal_congr h, Seq.storageAt_of_getStorage h]

/-! ## Part 1: no condition on who calls -/

/-- `D` is at least `d`, slot 1 (`totalSupply_`) holds `w1` and slot 3 (`crowdsale`) holds
`w3`. -/
def Floor (C : Address) (d : Int) (w1 w3 : U256) (S : TransactionState) : Prop :=
  d ≤ Supply.D 0 1 C S ∧ storageAt S C 1 = w1 ∧ storageAt S C 3 = w3

/-- `Floor` reads the storage words of `C` only. -/
theorem storageOnly_floor (C : Address) (d : Int) (w1 w3 : U256) :
    Seq.StorageOnly C (Floor C d w1 w3) := by
  intro S S' h hF
  refine ⟨?_, ?_, ?_⟩
  · rw [D_of_getStorage h]
    exact hF.1
  · rw [Seq.storageAt_of_getStorage h]
    exact hF.2.1
  · rw [Seq.storageAt_of_getStorage h]
    exact hF.2.2

/-- Every state has its own floor. -/
theorem floor_self (C : Address) (S : TransactionState) :
    Floor C (Supply.D 0 1 C S) (storageAt S C 1) (storageAt S C 3) S :=
  ⟨Int.le_refl _, rfl, rfl⟩

/-- The code of QNT at any address `C` keeps `Floor C d w1 w3`: a successful frame keeps the
words of slots 1 and 3, and leaves `D` as it was or (a `mint`) makes it larger (`supply_step`).
Every fork from Berlin, every cap on gas, with the hypothesis on keccak of the message of the
frame only. The runner argument is not used: QNT makes no outside call. -/
theorem frameKeepsQ_floor {fork : Fork} (hfork : .berlin ≤ fork) (G : Nat) (C : Address)
    (d : Int) (w1 w3 : U256) :
    Seq.FrameKeepsQ fork G C CODE (Floor C d w1 w3) (SepMsg fork) := by
  unfold Seq.FrameKeepsQ
  intro bound runChild message state substate gas evm s within _ hC _ hsize hq good _ start
    hrun hok
  subst hC
  obtain ⟨hD, h1, h3⟩ := supply_step hfork hsize hq start (Ends.run hrun) hok
  obtain ⟨gD, g1, g3⟩ := good.2
  refine ⟨?_, h1.trans g1, h3.trans g3⟩
  rcases hD with hD | ⟨-, hD⟩ <;> omega

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into QNT included), keeps "`C` holds the code
of QNT and `Floor C d w1 w3`". With or without an error. -/
theorem floor_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork) {C : Address}
    {d : Int} {w1 w3 : U256}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Floor C d w1 w3) state)
    (clean : Seq.Clean C CODE (SepMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Floor C d w1 w3) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_floor C d w1 w3)
    (Seq.frameKeepsR_of_all (frameKeepsQ_floor hfork message.gas C d w1 w3))
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION keeps `Floor C d w1 w3`. From Dencun, before Glamsterdam. -/
theorem floor_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address} {d : Int} {w1 w3 : U256}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Floor C d w1 w3) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Floor C d w1 w3) (TransactionState.ofBlock out.block) :=
  Seq.processTransaction_good (storageOnly_floor C d w1 w3)
    (fun G => Seq.frameKeepsR_of_all
      (frameKeepsQ_floor (Nat.le_trans (by decide) hden) G C d w1 w3))
    code_size_ne_zero code_not_indicator hden hlt clean h g

/-- Any finite list of transactions keeps `Floor C d w1 w3`. -/
theorem floor_any_transactions {C : Address} {d : Int} {w1 w3 : U256} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (g : Seq.Good C CODE (Floor C d w1 w3) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Floor C d w1 w3) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_floor C d w1 w3)
    (fun _ hden _ G => Seq.frameKeepsR_of_all
      (frameKeepsQ_floor (Nat.le_trans (by decide) hden) G C d w1 w3))
    code_size_ne_zero code_not_indicator chain g

/-- ONE TRANSACTION, whoever sends it and whatever it calls: `C` still holds the code of QNT,
slot 1 (`totalSupply_`) and slot 3 (`crowdsale`) keep their word, and `D` (the sum of all
balances minus the word of slot 1) does not go down. Nothing is assumed about the storage at
the start. This is NOT "the sum of the balances is the total supply": a `mint` makes `D`
larger. -/
theorem fixed_mono_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock block)) :
    Seq.HoldsCode C CODE (TransactionState.ofBlock out.block) ∧
      storageAt (TransactionState.ofBlock out.block) C 1 =
        storageAt (TransactionState.ofBlock block) C 1 ∧
      storageAt (TransactionState.ofBlock out.block) C 3 =
        storageAt (TransactionState.ofBlock block) C 3 ∧
      Supply.D 0 1 C (TransactionState.ofBlock block) ≤
        Supply.D 0 1 C (TransactionState.ofBlock out.block) := by
  have g := floor_transaction hden hlt clean h ⟨hold, floor_self C _⟩
  exact ⟨g.1, g.2.2.1, g.2.2.2, g.2.1⟩

/-- THE FIRST HEADLINE: after any finite list of transactions, whoever calls and however deep,
`C` still holds the code of QNT, slot 1 (`totalSupply_`) and slot 3 (`crowdsale`) hold the word
they held before the first one, and `D` (the sum of all balances minus the word of slot 1) is
at least what it was. Nothing is assumed about the storage at the start. This is NOT "the sum
of the balances is the total supply": a `mint` by the crowdsale address makes `D` larger. -/
theorem fixed_mono_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b)) :
    Seq.HoldsCode C CODE (TransactionState.ofBlock b') ∧
      storageAt (TransactionState.ofBlock b') C 1 = storageAt (TransactionState.ofBlock b) C 1 ∧
      storageAt (TransactionState.ofBlock b') C 3 = storageAt (TransactionState.ofBlock b) C 3 ∧
      Supply.D 0 1 C (TransactionState.ofBlock b) ≤ Supply.D 0 1 C (TransactionState.ofBlock b') := by
  have g := floor_any_transactions chain ⟨hold, floor_self C _⟩
  exact ⟨g.1, g.2.2.1, g.2.2.2, g.2.1⟩

/-! ## Part 2: no message that enters QNT comes from the crowdsale address -/

/-- The invariant of QNT reads the storage words of `C` only. -/
theorem storageOnly_inv (C : Address) : Seq.StorageOnly C (Inv C) :=
  Seq.storageOnly_supply 0 1 C

/-- The base case: a state where every storage word of `C` is zero satisfies `Inv`. -/
theorem inv_zeroBase (C : Address) : Seq.ZeroBase C (Inv C) :=
  Seq.zeroBase_supply 0 1 C

/-- The code of QNT at any address `C` keeps `Inv C` in every frame whose caller is not the
address in slot 3 at the start of the frame (`NoCrowdMsg`): such a frame is no successful
`mint` (`mint_caller`), so it leaves `D` as it was (`supply_step`). Every fork from Berlin,
every cap on gas. -/
theorem frameKeepsQ_noCrowd {fork : Fork} (hfork : .berlin ≤ fork) (G : Nat) (C : Address) :
    Seq.FrameKeepsQ fork G C CODE (Inv C) (NoCrowdMsg fork) := by
  unfold Seq.FrameKeepsQ
  intro bound runChild message state substate gas evm s within _ hC _ hsize hq good _ start
    hrun hok
  subst hC
  obtain ⟨hD, -, -⟩ := supply_step hfork hsize hq.1 start (Ends.run hrun) hok
  rcases hD with hD | ⟨hsel, -⟩
  · show Supply.D 0 1 _ _ = 0
    rw [hD]
    exact good.2
  · exact absurd (mint_caller hfork hsize hsel start (Ends.run hrun) hok) hq.2

/-- ANY DEPTH, no call by the crowdsale address: a call that EthLib's `processMessage` runs, to
any account, whatever code it runs and whatever messages it sends, keeps "`C` holds the code of
QNT and `Inv`", when no message of this run that enters the code at `C` comes from the address
in slot 3 (`Seq.Clean` with `NoCrowdMsg`). With or without an error. -/
theorem noCrowd_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork) {C : Address}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Inv C) state)
    (clean : Seq.Clean C CODE (NoCrowdMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Inv C) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_inv C)
    (Seq.frameKeepsR_of_all (frameKeepsQ_noCrowd hfork message.gas C))
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION, no call by the crowdsale address: a whole transaction as EthLib's
`processTransaction` runs it keeps "`C` holds the code of QNT and `Inv`", when no message of
this transaction that enters the code at `C` comes from the address in slot 3. From Dencun,
before Glamsterdam. -/
theorem inv_transaction_no_crowdsale {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (NoCrowdMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock out.block) :=
  Seq.processTransaction_good (storageOnly_inv C)
    (fun G => Seq.frameKeepsR_of_all (frameKeepsQ_noCrowd (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator hden hlt clean h g

/-- THE SECOND HEADLINE: `Inv` (the sum of all balances is `totalSupply_`) holds after any
finite list of transactions in which no message that enters the code at `C` comes from the
address in slot 3 (`crowdsale`), however deep the calls. With a call by that address it is NOT
claimed: a successful `mint` of a nonzero amount breaks `Inv` (`goodCall_mint_D`). -/
theorem inv_any_transactions_no_crowdsale {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE NoCrowdMsg b b')
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_inv C)
    (fun _ hden _ G => Seq.frameKeepsR_of_all
      (frameKeepsQ_noCrowd (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator chain g

/-- From the base case (`C` holds the code of QNT and its storage is all zero, so slot 3 holds
the address 0), `Inv` holds after any finite list of transactions in which no message that
enters the code at `C` comes from the address in slot 3. -/
theorem inv_from_zero_no_crowdsale {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE NoCrowdMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Inv C (TransactionState.ofBlock b') :=
  Seq.chain_from_zero (storageOnly_inv C)
    (fun _ hden _ G => Seq.frameKeepsR_of_all
      (frameKeepsQ_noCrowd (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator (inv_zeroBase C) chain hold h0

end QntVerify

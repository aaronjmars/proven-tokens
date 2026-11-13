import PepeVerify.Pepe.Seq
import TokenKit.Seq.Supply

/-!
# The supply invariant over whole transactions, at any depth, and over any finite list of them

`supply_preserved` is about one frame of the code of PEPE. `Seq.lean` lifts it to one top-level
message, and its `Calls` leaves "every other change keeps the storage of `C`" as an assumption of
each step (audit 4, PEPE-2). This file removes that assumption with the shared library
`TokenKit.Seq` (Frame.lean, Run.lean, Tx.lean, Supply.lean): the theorems here are about
EthLib's REAL runner and EthLib's REAL transaction function.

- `storageOnly_inv`, `code_size_ne_zero`, `code_not_indicator`, `inv_zeroBase`: the four facts
  about PEPE that the library asks for. All proved, no hypothesis.
- `frameKeepsQ`: the code of PEPE meets the interface `Seq.FrameKeepsQ` of the library, with
  `Q m := Sep (callKeys m)` (the hypothesis on keccak of ONE message) and no cap on gas. PEPE
  makes no outside call, so the runner argument of the interface is not used.
- `supply_message_any_depth`: a call that EthLib's `processMessage` runs, to ANY account, with
  any code, sending any messages at any depth (calls back into PEPE included), ends in a state
  where `C` still holds the code of PEPE and the invariant holds. With or without an error.
  Every fork from Berlin.
- `supply_transaction`: the same for one whole transaction as EthLib's `processTransaction` runs
  it (gas purchase, authorizations of EIP-7702, the message, refunds, the fee, the deletion of
  accounts), from the block state before it to the block state after it.
- `supply_any_transactions`: THE HEADLINE. The same after any finite list of transactions
  (`Seq.Chain`), each at its own fork and in its own block environment.
- `supply_from_zero`: the same from the base case: `C` holds the code with all-zero storage.

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction, with `Q m := Sep (callKeys m)`. It is RUN-LOCAL: it speaks
   of the finitely many events of this one run only.
   - `call`, `create`: each message that really enters the code at `C` during the run satisfies
     `Sep (callKeys m)` (a hypothesis on keccak for three address words, NOT proved), and each
     code that a creation really deposits during the run, when it has the keccak hash of the code
     of PEPE, is that code (no collision of keccak on the codes this run deposits, NOT proved).
   - `auths`: no authorization of the transaction sets a code with the hash of the code of PEPE
     (again no collision of keccak, on finitely many 23 byte codes).
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The fork of each transaction is from Dencun and before Glamsterdam. Before Dencun,
   SELFDESTRUCT can delete an account that was not created in the same transaction, and this
   file does not prove that the code of PEPE never runs it. From Glamsterdam the gas meter has
   two counters and the proofs are for the one-counter meter.
3. At the start, `C` holds the code of PEPE (`Seq.HoldsCode`) and the invariant holds; in
   `supply_from_zero`, the storage of `C` is all zero instead.

Not covered: what a block does between transactions (withdrawals, the system calls of
EIP-4788, 2935, 7002, 7251, block rewards), and the constructor run that leaves the real start
state of PEPE (its storage after deployment is not all zero: the constructor mints the supply).
-/

set_option autoImplicit false

namespace PepeVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open PepeVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState BlockState)
open EthLib.Execution.Transactions

/-- The hypothesis on keccak of one message: `Sep` of its three address words. The state that
the frame starts from is not used (PEPE calls no other account). -/
abbrev SepMsg (fork : Fork) (m : Message fork) (_ : TransactionState) : Prop := Sep (callKeys m)

/-- The invariant of PEPE reads the storage words of `C` only. -/
theorem storageOnly_inv (C : Address) : Seq.StorageOnly C (Inv C) :=
  Seq.storageOnly_supply 1 3 C

/-- The code of PEPE is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of PEPE is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of PEPE delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- The base case: a state where every storage word of `C` is zero satisfies the invariant. -/
theorem inv_zeroBase (C : Address) : Seq.ZeroBase C (Inv C) :=
  Seq.zeroBase_supply 1 3 C

/-- The code of PEPE at any address `C` meets the interface of the library, at every fork from
Berlin, for every cap on gas, with the hypothesis on keccak of the message of the frame only.
The runner argument is not used: PEPE makes no outside call. -/
theorem frameKeepsQ {fork : Fork} (hfork : .berlin ≤ fork) (G : Nat) (C : Address) :
    Seq.FrameKeepsQ fork G C CODE (Inv C) (SepMsg fork) := by
  unfold Seq.FrameKeepsQ
  intro bound runChild message state substate gas evm s within _ hC _ hsize hq good _ start
    hrun hok
  subst hC
  exact supply_preserved hfork hsize hq good.2 start ⟨within, hrun⟩ hok

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into PEPE included), from a state where `C`
holds the code of PEPE and the invariant holds, ends in such a state. With or without an error.
`Seq.Clean` is the run-local hypothesis on the events of this run. -/
theorem supply_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork) {C : Address}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Inv C) state)
    (clean : Seq.Clean C CODE (SepMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Inv C) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_inv C)
    (Seq.frameKeepsR_of_all (frameKeepsQ hfork message.gas C))
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION: a whole transaction as EthLib's `processTransaction` runs it, whoever sends
it and whatever it calls, takes a block state where `C` holds the code of PEPE and the invariant
holds to such a block state. From Dencun, before Glamsterdam. -/
theorem supply_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock out.block) :=
  Seq.processTransaction_good (storageOnly_inv C)
    (fun G => Seq.frameKeepsR_of_all (frameKeepsQ (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator hden hlt clean h g

/-- THE HEADLINE: the supply invariant holds after any finite list of transactions, whoever
calls and however deep. `Seq.Chain` is a list of transactions that EthLib's `processTransaction`
runs one after the other, each from Dencun and before Glamsterdam, each with the run-local
hypotheses `Seq.TxClean`. -/
theorem supply_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_inv C)
    (fun _ hden _ G => Seq.frameKeepsR_of_all (frameKeepsQ (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator chain g

/-- From the base case (`C` holds the code of PEPE and its storage is all zero), the invariant
holds after any finite list of transactions. -/
theorem supply_from_zero {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Inv C (TransactionState.ofBlock b') :=
  Seq.chain_from_zero (storageOnly_inv C)
    (fun _ hden _ G => Seq.frameKeepsR_of_all (frameKeepsQ (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator (inv_zeroBase C) chain hold h0

end PepeVerify

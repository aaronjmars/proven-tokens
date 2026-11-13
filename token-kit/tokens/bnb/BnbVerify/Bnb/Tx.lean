import BnbVerify.Bnb.Stipend
import TokenKit.Seq.Supply

/-!
# The supply invariant over whole transactions, at any depth, and over any finite list of them

`supply_preserved` is about one frame of the code of BNB with a selector other than
`withdrawEther`; `Withdraw.supply_withdrawEther_process` (Bnb/Stipend.lean) is the frame of
`withdrawEther` under EthLib's real runner, with no assumption on the code that the owner runs.
`Seq.lean` lifts both to one top-level message, and its `Calls` leaves "every other change keeps
the storage of `C`" as an assumption of each step (`Untouched`). This file removes that
assumption with the shared library `TokenKit.Seq` (Frame.lean, Run.lean, Tx.lean, Supply.lean):
the theorems here are about EthLib's REAL runner and EthLib's REAL transaction function.
Written by hand (not generated).

How `withdrawEther` is handled. It is the one function of BNB that sends a message (a CALL that
moves ether to the owner). Two things could go wrong and both are proved away:

- The callee (the owner, any code) runs with at most 2300 gas (read from the bytes of the CALL),
  and `TokenKit.Stipend.processMessage_quiet` proves that such a message writes no storage word,
  however deep its own calls go, calls back into BNB included. So the frame of `withdrawEther`
  needs NO fact about the runner: `frameKeepsR` does not use the runner hypothesis of the
  interface, and no cap on gas is needed (the plain `Seq.Chain`, not `Seq.ChainCap`).
- Every OTHER way to reach the code of BNB during a transaction (a contract that calls BNB at
  any depth, re-entry from the owner into another function, a creation, a failed call that is
  rolled back) is covered by the induction of the library over EthLib's interpreter.

- `QMsg`: the run-local hypothesis on one message that enters the code of BNB: keccak separation
  when its selector is not `withdrawEther`; for `withdrawEther`, from Prague, the code of the
  owner (slot 4) is no EIP-7702 delegation in the state that the frame starts from.
- `storageOnly_inv`, `code_size_ne_zero`, `code_not_indicator`, `code_not_delegated`,
  `inv_zeroBase`: the facts about BNB that the library asks for. All proved, no hypothesis.
- `frameKeepsR`: the code of BNB meets the interface `Seq.FrameKeepsR` of the library (the form
  for EthLib's real runner), from Berlin and before Glamsterdam, for every cap on gas.
- `supply_message_any_depth`: a call that EthLib's `processMessage` runs, to ANY account, with
  any code, sending any messages at any depth (calls back into BNB and `withdrawEther`
  included), ends in a state where `C` still holds the code of BNB and the invariant holds. With
  or without an error. From Berlin, before Glamsterdam.
- `supply_transaction`: the same for one whole transaction as EthLib's `processTransaction` runs
  it (gas purchase, authorizations of EIP-7702, the message, refunds, the fee, the deletion of
  accounts). From Dencun, before Glamsterdam.
- `supply_any_transactions`: THE HEADLINE. The same after any finite list of transactions
  (`Seq.Chain`), `withdrawEther` included.
- `supply_from_zero`: the same from the base case: `C` holds the code with all-zero storage.

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction with `Q := QMsg`. It is RUN-LOCAL: it speaks of the
   finitely many events of this one run only.
   - `call`: each message that really enters the code at `C` during the run satisfies `QMsg`:
     `Sep (callKeys m)` when its selector is not `withdrawEther` (a hypothesis on keccak, NOT
     proved); when its selector is `withdrawEther` and the fork is Prague or later, the code of
     the owner is no EIP-7702 delegation (`hdel`: EthLib's rule for the CALL step used by
     `Withdraw.withdrawEther_run` does not cover a delegated target).
   - `create`: each code that a creation really deposits during the run, when it has the keccak
     hash of the code of BNB, is that code (no collision of keccak, NOT proved).
   - `auths`: no authorization of the transaction sets a code with the hash of the code of BNB.
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The fork of each transaction is from Dencun and before Glamsterdam (see the header of
   `TokenKit/Seq/Tx.lean`; `withdrawEther` itself needs "before Glamsterdam" too).
3. At the start, `C` holds the code of BNB (`Seq.HoldsCode`) and the invariant holds; in
   `supply_from_zero`, the storage of `C` is all zero instead.

Not covered: what a block does between transactions (withdrawals, the system calls of EIP-4788,
2935, 7002, 7251, block rewards), and the constructor run that leaves the real start state of
BNB (its storage after deployment is not all zero: the constructor mints the supply).
-/

set_option autoImplicit false

namespace BnbVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState BlockState)
open EthLib.Execution.Transactions

/-- The run-local hypothesis on one message `m` that enters the code of BNB, from the state `s`
that its frame starts from. A selector other than `withdrawEther`: keccak separation of the
address words of the call. The selector of `withdrawEther`: from Prague, the code of the owner
is no EIP-7702 delegation. -/
def QMsg (fork : Fork) (m : Message fork) (s : TransactionState) : Prop :=
  (selector m.data ≠ 0x3bed33ce → Sep (callKeys m)) ∧
    (selector m.data = 0x3bed33ce →
      ∀ c, s.getCode (s.getAccount (Withdraw.ownerOf m s)).codeHash = .ok c →
        .pectra ≤ fork → delegatedAddress c = none)

/-- The invariant of BNB reads the storage words of `C` only. -/
theorem storageOnly_inv (C : Address) : Seq.StorageOnly C (Inv C) :=
  Seq.storageOnly_supply2 5 6 3 C

/-- The code of BNB is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of BNB is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of BNB delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- The base case: a state where every storage word of `C` is zero satisfies the invariant. -/
theorem inv_zeroBase (C : Address) : Seq.ZeroBase C (Inv C) :=
  Seq.zeroBase_supply2 5 6 3 C

/-- The code of BNB at any address `C` meets the interface of the library for EthLib's real
runner, from Berlin and before Glamsterdam, for every cap on gas. The runner hypothesis of the
interface is NOT used: the functions other than `withdrawEther` send no message, and the callee
of `withdrawEther` is covered by the stipend theorem (`Withdraw.supply_withdrawEther_process`),
whatever its code. -/
theorem frameKeepsR {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (G : Nat) (C : Address) : Seq.FrameKeepsR fork G C CODE (Inv C) (QMsg fork) := by
  unfold Seq.FrameKeepsR
  intro bound message state substate gas evm s within _ hC _ hsize hq good _ start hrun hok
  subst hC
  by_cases hsel : selector message.data = 0x3bed33ce
  · exact Withdraw.supply_withdrawEther_process hfork hglam hsize hsel (hq.2 hsel) good.1.2.1
      good.2 start within hrun hok
  · exact supply_preserved hfork hsize hsel (hq.1 hsel) good.2 start (Ends.run hrun) hok

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into BNB and `withdrawEther` included), from a
state where `C` holds the code of BNB and the invariant holds, ends in such a state. With or
without an error. `Seq.Clean` is the run-local hypothesis on the events of this run. -/
theorem supply_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) {C : Address}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Inv C) state)
    (clean : Seq.Clean C CODE (QMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Inv C) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_inv C) (frameKeepsR hfork hglam message.gas C)
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION: a whole transaction as EthLib's `processTransaction` runs it, whoever sends
it and whatever it calls, takes a block state where `C` holds the code of BNB and the invariant
holds to such a block state. From Dencun, before Glamsterdam. -/
theorem supply_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (QMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock out.block) :=
  Seq.processTransaction_good (storageOnly_inv C)
    (fun G => frameKeepsR (Nat.le_trans (by decide) hden) hlt G C)
    code_size_ne_zero code_not_indicator hden hlt clean h g

/-- THE HEADLINE: the supply invariant of BNB (sum of `balanceOf` + sum of `freezeOf` =
`totalSupply`) holds after any finite list of transactions, whoever calls and however deep,
`withdrawEther` included. `Seq.Chain` is a list of transactions that EthLib's
`processTransaction` runs one after the other, each from Dencun and before Glamsterdam, each
with the run-local hypotheses `Seq.TxClean`. -/
theorem supply_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE QMsg b b')
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_inv C)
    (fun _ hden hlt G => frameKeepsR (Nat.le_trans (by decide) hden) hlt G C)
    code_size_ne_zero code_not_indicator chain g

/-- From the base case (`C` holds the code of BNB and its storage is all zero), the invariant
holds after any finite list of transactions. -/
theorem supply_from_zero {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE QMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Inv C (TransactionState.ofBlock b') :=
  Seq.chain_from_zero (storageOnly_inv C)
    (fun _ hden hlt G => frameKeepsR (Nat.le_trans (by decide) hden) hlt G C)
    code_size_ne_zero code_not_indicator (inv_zeroBase C) chain hold h0

end BnbVerify

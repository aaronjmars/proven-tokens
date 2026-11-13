import WethVerify.Weth.Reenter
import WethVerify.Weth.TxChain

/-!
# Solvency of WETH over whole transactions, at any depth, and over any finite list of them

The invariant of WETH is `Solvent C`: the sum of all `balanceOf` is at most the ether of the
contract. It reads the ether of `C`, so it is NOT an invariant of the storage only, and the
shared library `TokenKit.Seq` (which asks for `Seq.StorageOnly`) does not apply as it is.
`TxFrame.lean`, `TxRun.lean` and `TxChain.lean` (generic files, in this folder for now) redo the
induction of the library for an invariant that also reads the ether (`Bal.Mono`: more ether
never breaks it). This file gives the facts about WETH that they ask for, and the headlines.
Written by hand (not generated).

`solvent_preserved_process` (Weth/Reenter.lean) is one frame of the code of WETH under EthLib's
real runner, with no assumption on the callee of `withdraw` (the stipend theorem). `Seq.lean`
lifts it to one top-level message, and its `Calls` leaves "every other change keeps the storage
of `C` and does not lower its ether" as an assumption of each step (`Other`). This file removes
that assumption: the theorems here are about EthLib's REAL runner and REAL transaction function.

Why the ether of `C` cannot go down outside the code of WETH: ether leaves an account only in
the move of value of a message whose caller is the account, in SELFDESTRUCT of a frame at the
account, or when the account pays the gas of a transaction as its sender. A frame at another
address than `C` sends messages whose caller is that other address (DELEGATECALL keeps the
caller but moves no value). So only a frame at `C` can lower the ether of `C`, and a frame at
`C` runs the code of WETH, which `solvent_preserved_process` covers.

- `QMsg`: the run-local hypothesis on one message that enters the code of WETH: keccak
  separation; for `withdraw` with value 0, from Prague, the code of the caller is no EIP-7702
  delegation in the state that the frame starts from.
- `mono_solvent`, `code_size_ne_zero`, `code_not_indicator`, `code_not_delegated`,
  `solvent_zeroBase`: the facts about WETH that the induction asks for. Proved, no hypothesis.
- `backed_startSt`: the move of value of a message into `C`, from a solvent state, leaves the
  contract backed with the value to spare (what `deposit` needs).
- `frameKeepsV`: the code of WETH meets the interface `Bal.FrameKeepsV` (the form for EthLib's
  real runner), from Berlin and before Glamsterdam.
- `solvent_message_any_depth`: a call that EthLib's `processMessage` runs, to ANY account, with
  any code, sending any messages at any depth (calls back into WETH included), ends in a state
  where `C` still holds the code of WETH and is solvent. With or without an error.
- `solvent_transaction`: the same for one whole transaction as EthLib's `processTransaction`
  runs it. From Dencun, before Glamsterdam.
- `solvent_any_transactions`: THE HEADLINE. The same after any finite list of transactions.
- `solvent_from_zero`: the same from the base case: `C` holds the code with all-zero storage.

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction with `Q := QMsg`. RUN-LOCAL: it speaks of the finitely many
   events of this one run only.
   - `call`: each message that really enters the code at `C` during the run satisfies `QMsg`:
     `Sep (callKeys m)` (a hypothesis on keccak, NOT proved); when it is `withdraw` with value
     0 and the fork is Prague or later, the code of its caller is no EIP-7702 delegation.
   - `create`: each code that a creation really deposits during the run, when it has the keccak
     hash of the code of WETH, is that code (no collision of keccak, NOT proved).
   - `auths`: no authorization of the transaction sets a code with the hash of the code of WETH.
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The sender of each transaction is not `C` (`included.sender ≠ C`). On a chain it holds
   because `C` has code (EIP-3607); that check is before `processTransaction` and NOT proved.
3. The fork of each transaction is from Dencun and before Glamsterdam.
4. At the start, `C` holds the code of WETH (`Seq.HoldsCode`) and is solvent; in
   `solvent_from_zero`, the storage of `C` is all zero instead.
5. In `solvent_message_any_depth` only: the message is `Bal.Paid C` (its value does not come
   from `C`, and it moves its value when it runs at `C`). The transaction theorems prove it.

Not covered: what a block does between transactions (withdrawals, the system calls of EIP-4788,
2935, 7002, 7251, block rewards; none of them lowers the ether of a contract, but that is not
proved here), and the constructor run.
-/

set_option autoImplicit false

namespace WethVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState BlockState EMPTY_CODE_HASH)
open EthLib.Execution.Transactions

/-- The run-local hypothesis on one message `m` that enters the code of WETH, from the state `s`
that its frame starts from (after the move of its value): keccak separation of the address
words of the call; for `withdraw` with value 0, from Prague, the code of the caller is no
EIP-7702 delegation. -/
def QMsg (fork : Fork) (m : Message fork) (s : TransactionState) : Prop :=
  Sep (callKeys m) ∧
    (selector m.data = 0x2e1a7d4d → m.value = 0 →
      ∀ c, s.getCode (s.getAccount m.caller).codeHash = .ok c →
        .pectra ≤ fork → delegatedAddress c = none)

/-- Solvency is kept by every change that keeps the storage of `C` and does not lower its
ether. -/
theorem mono_solvent (C : Address) : Bal.Mono C (Solvent C) := by
  intro S S' h hu hs
  exact Supply.solvent_congr (fun _ => h _) hu hs

/-- The code of WETH is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of WETH is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of WETH delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- The base case: a state where every storage word of `C` is zero is solvent. -/
theorem solvent_zeroBase (C : Address) : Seq.ZeroBase C (Solvent C) := by
  intro S h0
  show Supply.sumBal 3 C S ≤ ((etherOf S C).toNat : Int)
  rw [Seq.sumBal_zero h0]
  omega

/-- The start of a message that runs at `C`, from a state where `C` holds code and is solvent:
after the move of its value the contract is backed with that value to spare. The value does not
come from `C` (`Bal.Paid`). -/
theorem backed_startSt {fork : Fork} {message : Message fork}
    {state state1 : TransactionState}
    (paid : Bal.Paid message.currentTarget message)
    (good : Seq.Good message.currentTarget CODE (Solvent message.currentTarget) state)
    (h : Seq.startSt message state = .ok state1) :
    Backed message.value message.currentTarget state1 := by
  have ks := Seq.kept_startState (L := message.currentTarget) message state
  have gs : Solvent message.currentTarget (startState fork message state) :=
    mono_solvent message.currentTarget _ _ (ks.storage good.1.2.1)
      (Bal.up_startState message state) good.2
  have hs : ((startState fork message state).getAccount message.currentTarget).codeHash ≠
      EMPTY_CODE_HASH := (ks.holdsCode good.1).2.1
  unfold Seq.startSt at h
  split at h
  · rename_i hc
    exact Supply.backed_moveEther_into (paid.1 hc.1) hs (EthLib.Base.mapError_ok_iff.mp h) gs
  · rename_i hc
    cases h
    have hv : message.value = 0 := by
      by_cases hv : message.value = 0
      · exact hv
      · exact absurd ⟨paid.2 rfl, hv⟩ hc
    rw [hv]
    exact Supply.Solvent.backed_zero gs

/-- The code of WETH at any address `C` meets the interface `Bal.FrameKeepsV`, for EthLib's real
runner, from Berlin and before Glamsterdam. No fact about the runner is used: the callee of
`withdraw` is covered by the stipend theorem (`solvent_preserved_process`), whatever its
code. -/
theorem frameKeepsV {fork : Fork} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (C : Address) : Bal.FrameKeepsV fork C CODE (Solvent C) (QMsg fork) := by
  unfold Bal.FrameKeepsV
  intro bound message state state1 substate gas evm s within hC _ hsize paid good hst hq start
    hrun hok
  subst hC
  have hold1 := (Bal.kept_startSt (L := message.currentTarget) hst).holdsCode good.1
  exact solvent_preserved_process hfork hsize hq.1 (backed_startSt paid good hst) hold1.2.1
    (fun hsel hv => ⟨hglam, hq.2 hsel hv⟩) start within hrun hok

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into WETH included), from a state where `C`
holds the code of WETH and is solvent, ends in such a state. With or without an error.
`Seq.Clean` is the run-local hypothesis on the events of this run; `Bal.Paid` says that the
value of the message does not come from `C`. -/
theorem solvent_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) {C : Address}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (paid : Bal.Paid C message)
    (g : Seq.Good C CODE (Solvent C) state)
    (clean : Seq.Clean C CODE (QMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Solvent C) ended.val.state :=
  Bal.processMessage_good_bal (mono_solvent C) (frameKeepsV hfork hglam C) code_not_delegated
    sane paid g clean h

/-- ONE TRANSACTION: a whole transaction as EthLib's `processTransaction` runs it, whatever it
calls, takes a block state where `C` holds the code of WETH and is solvent to such a block
state. The sender is not `C`. From Dencun, before Glamsterdam. -/
theorem solvent_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (hsender : included.sender ≠ C)
    (clean : Seq.TxClean C CODE (QMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Solvent C) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Solvent C) (TransactionState.ofBlock out.block) :=
  Bal.processTransaction_good_bal (mono_solvent C) code_size_ne_zero code_not_indicator hden hlt
    (frameKeepsV (Nat.le_trans (by decide) hden) hlt C) hsender clean h g

/-- THE HEADLINE: WETH is solvent (the sum of all `balanceOf` is at most the ether of the
contract) after any finite list of transactions, whoever calls and however deep, `withdraw`
and its callee included. `Bal.ChainV` is a list of transactions that EthLib's
`processTransaction` runs one after the other, each from Dencun and before Glamsterdam, each
with a sender other than `C` and the run-local hypotheses `Seq.TxClean`. -/
theorem solvent_any_transactions {C : Address} {b b' : BlockState}
    (chain : Bal.ChainV C CODE QMsg b b')
    (g : Seq.Good C CODE (Solvent C) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Solvent C) (TransactionState.ofBlock b') :=
  Bal.chain_good_bal (mono_solvent C)
    (fun _ hden hlt => frameKeepsV (Nat.le_trans (by decide) hden) hlt C)
    code_size_ne_zero code_not_indicator chain g

/-- From the base case (`C` holds the code of WETH and its storage is all zero), WETH is solvent
after any finite list of transactions. -/
theorem solvent_from_zero {C : Address} {b b' : BlockState}
    (chain : Bal.ChainV C CODE QMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Solvent C (TransactionState.ofBlock b') :=
  (solvent_any_transactions chain ⟨hold, solvent_zeroBase C _ h0⟩).2

end WethVerify

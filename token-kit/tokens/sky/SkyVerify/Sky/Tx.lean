import SkyVerify.Sky.PermitBytesSeq
import SkyVerify.Sky.FrameRule
import TokenKit.Seq.Supply

/-!
# The supply invariant over whole transactions, at any depth, and over any finite list of them

Audit 4, SKY-3. `supply_preserved` (every selector but the two `permit`, any runner),
`supply_permit` (`permit(v, r, s)`, EthLib's real runner) and `supply_permitBytes`
(`permit(bytes)` with a signature of ANY length, EthLib's real runner) are about one frame of
the code of SKY. `Seq.lean`, `PermitSeq.lean` and `PermitBytesSeq.lean` lift them to one
top-level message, and their `Calls` / `CallsP` / `Calls65` / `CallsAny` leave "every other
change keeps the storage of `C`" (`Untouched`) as an assumption of each step. This file removes
that assumption with the shared library `TokenKit.Seq` (Frame.lean, Run.lean, Tx.lean,
Supply.lean): the theorems here are about EthLib's REAL runner and EthLib's REAL transaction
function, and every selector is included, both `permit` too.

Both `permit` make an outside call to an account with ANY code: a read-only STATICCALL to the
owner (`isValidSignature`, ERC-1271) when the recovered address is not the owner (for
`permit(bytes)`: always when the length word is not 65). `supply_permit` and
`supply_permitBytes` bound that call with the real runner (`TokenKit.staticcall_kept`: a
static run changes no storage word, whatever code it runs), so they need no fact about the
runner. `Sky/FrameRule.lean` (`RealFrameKeeps`, `frameKeepsR_of_real`) is the frame rule that
turns such a frame theorem into the interface `Seq.FrameKeepsR` of the kit. If the owner
contract calls back into SKY during that STATICCALL, the entry is one more event of the run and
the induction of the kit covers it.

- `storageOnly_inv`, `code_size_ne_zero`, `code_not_indicator`, `code_not_delegated`,
  `inv_zeroBase`: the facts about SKY that the library asks for. All proved, no hypothesis.
- `realFrameKeeps`: the code of SKY at any address `C` keeps `Inv C` in one frame under the
  real runner, every selector, from Paris and before Glamsterdam, with
  `Q m s := Sep (callKeys m) ∧ NoDelegation1 fork s`. By cases on the selector.
- `frameKeepsR`: the same as the interface `Seq.FrameKeepsR` (by `frameKeepsR_of_real`).
- `supply_message_any_depth`: a call that EthLib's `processMessage` runs, to ANY account, with
  any code, sending any messages at any depth (calls back into SKY included, from inside the
  STATICCALL of ERC-1271 too), ends in a state where `C` still holds the code of SKY and the
  invariant holds. With or without an error. From Paris, before Glamsterdam.
- `supply_transaction`: the same for one whole transaction as EthLib's `processTransaction`
  runs it (gas purchase, authorizations of EIP-7702, the message, refunds, the fee, the deletion
  of accounts), from the block state before it to the block state after it.
- `supply_any_transactions`: THE HEADLINE. The same after any finite list of transactions
  (`Seq.Chain`), each at its own fork and in its own block environment.
- `supply_from_zero`: the same from the base case: `C` holds the code with all-zero storage.

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction, with `Q := QMsg`. It is RUN-LOCAL: it speaks of the
   finitely many events of this one run only.
   - `call`, `create`: each message `m` that really enters the code at `C` during the run, with
     the state `s` that its frame starts from, satisfies `Sep (callKeys m)` (a hypothesis on
     keccak for the address words of the call, NOT proved) and `NoDelegation1 fork s` (in that
     state the account at address 1, the precompile ECRECOVER, holds no EIP-7702 delegation
     code; NOT proved, it is a fact of the state; used by the two `permit` only, and from
     Pectra only). And each code that a creation really deposits during the run, when it has
     the keccak hash of the code of SKY, is that code (no collision of keccak, NOT proved).
   - `auths`: no authorization of the transaction sets a code with the hash of the code of SKY
     (again no collision of keccak, on finitely many 23 byte codes).
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The fork of each transaction is from Dencun and before Glamsterdam.
3. At the start, `C` holds the code of SKY (`Seq.HoldsCode`) and the invariant holds; in
   `supply_from_zero`, the storage of `C` is all zero instead.

Nothing is assumed about the code of the owner contract that `permit` asks, nor about any other
code that runs in the transaction.

Not covered: what a block does between transactions (withdrawals, the system calls of
EIP-4788, 2935, 7002, 7251, block rewards), and the constructor run that leaves the real start
state of SKY.
-/

set_option autoImplicit false

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState BlockState)
open EthLib.Execution.Transactions

/-- The hypothesis on one message that enters the code at `C`, and on the state that its frame
starts from: `Sep` of its address words (keccak), and no EIP-7702 delegation code at address 1
in that state (used by the two `permit` only). -/
abbrev QMsg (fork : Fork) (m : Message fork) (s : TransactionState) : Prop :=
  Sep (callKeys m) ∧ NoDelegation1 fork s

/-- The invariant of SKY reads the storage words of `C` only. -/
theorem storageOnly_inv (C : Address) : Seq.StorageOnly C (Inv C) :=
  Seq.storageOnly_supply 2 1 C

/-- The code of SKY is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of SKY is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of SKY delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- The base case: a state where every storage word of `C` is zero satisfies the invariant. -/
theorem inv_zeroBase (C : Address) : Seq.ZeroBase C (Inv C) :=
  Seq.zeroBase_supply 2 1 C

/-- One frame of the code of SKY at any address `C`, under EthLib's real runner, from Paris and
before Glamsterdam, for every cap on gas: with `QMsg` on the message and its start state and
`Inv C` at the start, a run that ends with no error keeps `Inv C`. EVERY selector:
`permit(v, r, s)` (`0xd505accf`) by `supply_permit`, `permit(bytes)` (`0x9fd5a6cf`, a signature
of any length) by `supply_permitBytes`, the others by `supply_preserved`. No fact about the
runner and none about the code of the owner that `permit` asks is used. -/
theorem realFrameKeeps {fork : Fork} (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (G : Nat) (C : Address) :
    RealFrameKeeps fork G C CODE (Inv C) (QMsg fork) := by
  intro bound message state substate gas evm s within _ hC _ hsize hq hinv start hrun hok
  subst hC
  by_cases hsel0 : selector message.data = 0x9fd5a6cf
  · exact supply_permitBytes hparis hglam hsize hsel0 hq.2 hq.1 hinv start within hrun hok
  · by_cases hsel : selector message.data = 0xd505accf
    · exact supply_permit hparis hglam hsize hsel hq.2 hq.1 hinv start within hrun hok
    · exact supply_preserved (Nat.le_trans (by decide) hparis) hsize hsel0 hsel hq.1 hinv start
        ⟨within, hrun⟩ hok

/-- The code of SKY at any address `C` meets the interface of the library for EthLib's real
runner, from Paris and before Glamsterdam, for every cap on gas, with the hypothesis `QMsg` on
the message of the frame and its start state. Every selector, both `permit` included. -/
theorem frameKeepsR {fork : Fork} (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (G : Nat) (C : Address) :
    Seq.FrameKeepsR fork G C CODE (Inv C) (QMsg fork) :=
  frameKeepsR_of_real (realFrameKeeps hparis hglam G C)

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into SKY included), from a state where `C`
holds the code of SKY and the invariant holds, ends in such a state. With or without an error.
`Seq.Clean` is the run-local hypothesis on the events of this run. -/
theorem supply_message_any_depth {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam) {C : Address}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Inv C) state)
    (clean : Seq.Clean C CODE (QMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Inv C) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_inv C)
    (frameKeepsR hparis hglam message.gas C)
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION: a whole transaction as EthLib's `processTransaction` runs it, whoever sends
it and whatever it calls, takes a block state where `C` holds the code of SKY and the invariant
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

/-- THE HEADLINE: the supply invariant holds after any finite list of transactions, whoever
calls and however deep, both `permit` included (any signature length, the ERC-1271 way to any
owner code included). `Seq.Chain` is a list of transactions that EthLib's `processTransaction`
runs one after the other, each from Dencun and before Glamsterdam, each with the run-local
hypotheses `Seq.TxClean`. -/
theorem supply_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE QMsg b b')
    (g : Seq.Good C CODE (Inv C) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Inv C) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_inv C)
    (fun _ hden hlt G => frameKeepsR (Nat.le_trans (by decide) hden) hlt G C)
    code_size_ne_zero code_not_indicator chain g

/-- From the base case (`C` holds the code of SKY and its storage is all zero), the invariant
holds after any finite list of transactions. -/
theorem supply_from_zero {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE QMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Inv C (TransactionState.ofBlock b') :=
  Seq.chain_from_zero (storageOnly_inv C)
    (fun _ hden hlt G => frameKeepsR (Nat.le_trans (by decide) hden) hlt G C)
    code_size_ne_zero code_not_indicator (inv_zeroBase C) chain hold h0

end SkyVerify

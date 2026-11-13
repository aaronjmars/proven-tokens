import WbtVerify.Wbt.NoMint
import TokenKit.Seq.Supply

/-!
# The supply invariant over whole transactions, at any depth, and over any finite list of them

`supply_preserved` is about one frame of the code of WBT. `Seq.lean` lifts it to one top-level
message, and its `Calls` leaves "every other change keeps the storage of `C`" as an assumption of
each step (audit 4, WBT-1). This file removes that assumption with the shared library
`TokenKit.Seq` (Frame.lean, Run.lean, Tx.lean, Supply.lean): the theorems here are about
EthLib's REAL runner and EthLib's REAL transaction function.

- `storageOnly_inv`, `code_size_ne_zero`, `code_not_indicator`, `inv_zeroBase`: the four facts
  about WBT that the library asks for. All proved, no hypothesis.
- `frameKeepsQ`: the code of WBT meets the interface `Seq.FrameKeepsQ` of the library, with
  `Q m := Sep (callKeys m)` (the hypothesis on keccak of ONE message) and no cap on gas. WBT
  makes no outside call, so the runner argument of the interface is not used.
- `supply_message_any_depth`: a call that EthLib's `processMessage` runs, to ANY account, with
  any code, sending any messages at any depth (calls back into WBT included), ends in a state
  where `C` still holds the code of WBT and the invariant holds. With or without an error.
  Every fork from Berlin.
- `supply_transaction`: the same for one whole transaction as EthLib's `processTransaction` runs
  it (gas purchase, authorizations of EIP-7702, the message, refunds, the fee, the deletion of
  accounts), from the block state before it to the block state after it.
- `supply_any_transactions`: THE HEADLINE. The same after any finite list of transactions
  (`Seq.Chain`), each at its own fork and in its own block environment.
- `supply_from_zero`: the same from the base case: `C` holds the code with all-zero storage.

WBT has two more facts per frame that assume nothing about the start state (`delta_step` of
Invariant.lean and `total_le` of NoMint.lean). They are lifted the same way, with the state
predicate `Level C d n`: "`D` is `d` and the word of slot 5 (`_totalSupply`) is at most `n`",
for any fixed `d` and `n`.

- `level_message_any_depth`, `level_transaction`: `Level C d n` is kept by a call at any depth
  and by a whole transaction.
- `delta_any_transactions`: THE SECOND HEADLINE. After any finite list of transactions, `D` (the
  sum of all balances minus `_totalSupply`) is what it was before, and `C` still holds the code.
  No invariant is assumed at the start.
- `supply_never_grows_any_transactions`: THE THIRD HEADLINE (audit 4, WBT-1). After any finite
  list of transactions the word of slot 5 (`_totalSupply`) is at most what it was before. No
  invariant is assumed at the start. The older `supply_never_grows` of NoMint.lean is the same
  claim in the weaker per-message model `Calls` (with the assumed `Untouched` step).
- `delta_transaction`, `supply_never_grows_transaction`: the same for one transaction.

Hypotheses that stay (each is named in status.json):
1. `Seq.TxClean` of each transaction, with `Q m := Sep (callKeys m)`. It is RUN-LOCAL: it speaks
   of the finitely many events of this one run only.
   - `call`, `create`: each message that really enters the code at `C` during the run satisfies
     `Sep (callKeys m)` (a hypothesis on keccak for three address words, NOT proved), and each
     code that a creation really deposits during the run, when it has the keccak hash of the code
     of WBT, is that code (no collision of keccak on the codes this run deposits, NOT proved).
   - `auths`: no authorization of the transaction sets a code with the hash of the code of WBT
     (again no collision of keccak, on finitely many 23 byte codes).
   - `data`: the call data of a transaction to `C` is below 2^256 bytes.
2. The fork of each transaction is from Dencun and before Glamsterdam. Before Dencun,
   SELFDESTRUCT can delete an account that was not created in the same transaction, and this
   file does not prove that the code of WBT never runs it. From Glamsterdam the gas meter has
   two counters and the proofs are for the one-counter meter.
3. At the start, `C` holds the code of WBT (`Seq.HoldsCode`) and the invariant holds; in
   `supply_from_zero`, the storage of `C` is all zero instead.

Not covered: what a block does between transactions (withdrawals, the system calls of
EIP-4788, 2935, 7002, 7251, block rewards), and the constructor run that leaves the real start
state of WBT (the real storage of WBT is not all zero: tokens exist).
-/

set_option autoImplicit false

namespace WbtVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open EthLib.Execution.State (TransactionState BlockState)
open EthLib.Execution.Transactions

/-- The hypothesis on keccak of one message: `Sep` of its three address words. The state that
the frame starts from is not used (WBT calls no other account). -/
abbrev SepMsg (fork : Fork) (m : Message fork) (_ : TransactionState) : Prop := Sep (callKeys m)

/-- The invariant of WBT reads the storage words of `C` only. -/
theorem storageOnly_inv (C : Address) : Seq.StorageOnly C (Inv C) :=
  Seq.storageOnly_supply 3 5 C

/-- The code of WBT is not empty. -/
theorem code_size_ne_zero : CODE.size ≠ 0 := by
  rw [size_CODE]
  decide

/-- The code of WBT is no EIP-7702 delegation indicator (an indicator has 23 bytes). -/
theorem code_not_indicator : isValidDelegation CODE = false := by
  simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]

/-- The code of WBT delegates to no address. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  simp [delegatedAddress, code_not_indicator]

/-- The base case: a state where every storage word of `C` is zero satisfies the invariant. -/
theorem inv_zeroBase (C : Address) : Seq.ZeroBase C (Inv C) :=
  Seq.zeroBase_supply 3 5 C

/-- The code of WBT at any address `C` meets the interface of the library, at every fork from
Berlin, for every cap on gas, with the hypothesis on keccak of the message of the frame only.
The runner argument is not used: WBT makes no outside call. -/
theorem frameKeepsQ {fork : Fork} (hfork : .berlin ≤ fork) (G : Nat) (C : Address) :
    Seq.FrameKeepsQ fork G C CODE (Inv C) (SepMsg fork) := by
  unfold Seq.FrameKeepsQ
  intro bound runChild message state substate gas evm s within _ hC _ hsize hq good _ start
    hrun hok
  subst hC
  exact supply_preserved hfork hsize hq good.2 start ⟨within, hrun⟩ hok

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends (calls back into WBT included), from a state where `C`
holds the code of WBT and the invariant holds, ends in such a state. With or without an error.
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
it and whatever it calls, takes a block state where `C` holds the code of WBT and the invariant
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

/-- From the base case (`C` holds the code of WBT and its storage is all zero), the invariant
holds after any finite list of transactions. -/
theorem supply_from_zero {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage C k = 0) :
    Inv C (TransactionState.ofBlock b') :=
  Seq.chain_from_zero (storageOnly_inv C)
    (fun _ hden _ G => Seq.frameKeepsR_of_all (frameKeepsQ (Nat.le_trans (by decide) hden) G C))
    code_size_ne_zero code_not_indicator (inv_zeroBase C) chain hold h0

/-! ## `D` unchanged and the total supply never larger, with no invariant at the start -/

/-- `D` (the sum of all balances minus the word of slot 5) is `d`, and the word of slot 5
(`_totalSupply`) is at most `n`. -/
def Level (C : Address) (d : Int) (n : Nat) (S : TransactionState) : Prop :=
  Supply.D 3 5 C S = d ∧ (storageAt S C 5).toNat ≤ n

/-- `Level` reads the storage words of `C` only. -/
theorem storageOnly_level (C : Address) (d : Int) (n : Nat) :
    Seq.StorageOnly C (Level C d n) := by
  intro S S' h hL
  refine ⟨?_, ?_⟩
  · have e : Supply.D 3 5 C S' = Supply.D 3 5 C S := by
      unfold Supply.D
      rw [Seq.sumBal_congr h, Seq.storageAt_of_getStorage h]
    rw [e]
    exact hL.1
  · rw [Seq.storageAt_of_getStorage h]
    exact hL.2

/-- Every state has its own level. -/
theorem level_self (C : Address) (S : TransactionState) :
    Level C (Supply.D 3 5 C S) (storageAt S C 5).toNat S :=
  ⟨rfl, Nat.le_refl _⟩

/-- The code of WBT at any address `C` keeps `Level C d n`, for every `d` and `n`: a successful
frame leaves `D` as it was (`delta_step`) and does not make the word of slot 5 larger
(`total_le`). Every fork from Berlin, every cap on gas, with the hypothesis on keccak of the
message of the frame only. -/
theorem frameKeepsQ_level {fork : Fork} (hfork : .berlin ≤ fork) (G : Nat) (C : Address)
    (d : Int) (n : Nat) :
    Seq.FrameKeepsQ fork G C CODE (Level C d n) (SepMsg fork) := by
  unfold Seq.FrameKeepsQ
  intro bound runChild message state substate gas evm s within _ hC _ hsize hq good _ start
    hrun hok
  subst hC
  exact ⟨(delta_step hfork hsize hq start ⟨within, hrun⟩ hok).trans good.2.1,
    Nat.le_trans (total_le hfork hsize hq start ⟨within, hrun⟩ hok) good.2.2⟩

/-- ANY DEPTH: a call that EthLib's `processMessage` runs, to any account, whatever code it
runs and whatever messages it sends, keeps "`C` holds the code of WBT, `D` is `d`, the word of
slot 5 is at most `n`". With or without an error. -/
theorem level_message_any_depth {fork : Fork} (hfork : .berlin ≤ fork) {C : Address}
    {d : Int} {n : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Seq.Sane C CODE message) (g : Seq.Good C CODE (Level C d n) state)
    (clean : Seq.Clean C CODE (SepMsg fork) message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Seq.Good C CODE (Level C d n) ended.val.state :=
  Seq.processMessage_good_local (storageOnly_level C d n)
    (Seq.frameKeepsR_of_all (frameKeepsQ_level hfork message.gas C d n))
    code_not_delegated (Nat.le_refl _) sane g clean h

/-- ONE TRANSACTION keeps `Level C d n`. From Dencun, before Glamsterdam. -/
theorem level_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address} {d : Int} {n : Nat}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Seq.Good C CODE (Level C d n) (TransactionState.ofBlock block)) :
    Seq.Good C CODE (Level C d n) (TransactionState.ofBlock out.block) :=
  Seq.processTransaction_good (storageOnly_level C d n)
    (fun G => Seq.frameKeepsR_of_all
      (frameKeepsQ_level (Nat.le_trans (by decide) hden) G C d n))
    code_size_ne_zero code_not_indicator hden hlt clean h g

/-- Any finite list of transactions keeps `Level C d n`. -/
theorem level_any_transactions {C : Address} {d : Int} {n : Nat} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (g : Seq.Good C CODE (Level C d n) (TransactionState.ofBlock b)) :
    Seq.Good C CODE (Level C d n) (TransactionState.ofBlock b') :=
  Seq.chain_good (storageOnly_level C d n)
    (fun _ hden _ G => Seq.frameKeepsR_of_all
      (frameKeepsQ_level (Nat.le_trans (by decide) hden) G C d n))
    code_size_ne_zero code_not_indicator chain g

/-- ONE TRANSACTION, whoever sends it and whatever it calls: `C` still holds the code of WBT and
`D` (the sum of all balances minus `_totalSupply`) is what it was. Nothing is assumed about the
storage at the start. -/
theorem delta_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock block)) :
    Seq.HoldsCode C CODE (TransactionState.ofBlock out.block) ∧
      Supply.D 3 5 C (TransactionState.ofBlock out.block) =
        Supply.D 3 5 C (TransactionState.ofBlock block) := by
  have g := level_transaction hden hlt clean h ⟨hold, level_self C _⟩
  exact ⟨g.1, g.2.1⟩

/-- ONE TRANSACTION, whoever sends it and whatever it calls, does not make the word of slot 5
(`_totalSupply`) larger. Nothing is assumed about the storage at the start. -/
theorem supply_never_grows_transaction {fork : Fork} (hden : Fork.dencun ≤ fork)
    (hlt : fork < .glamsterdam) {C : Address}
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : Seq.TxClean C CODE (SepMsg fork) env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock block)) :
    (storageAt (TransactionState.ofBlock out.block) C 5).toNat ≤
      (storageAt (TransactionState.ofBlock block) C 5).toNat :=
  (level_transaction hden hlt clean h ⟨hold, level_self C _⟩).2.2

/-- THE SECOND HEADLINE: after any finite list of transactions, whoever calls and however deep,
`C` still holds the code of WBT and `D` (the sum of all balances minus `_totalSupply`) is what
it was before the first one. Nothing is assumed about the storage at the start. -/
theorem delta_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b)) :
    Seq.HoldsCode C CODE (TransactionState.ofBlock b') ∧
      Supply.D 3 5 C (TransactionState.ofBlock b') =
        Supply.D 3 5 C (TransactionState.ofBlock b) := by
  have g := level_any_transactions chain ⟨hold, level_self C _⟩
  exact ⟨g.1, g.2.1⟩

/-- THE THIRD HEADLINE (audit 4, WBT-1): after any finite list of transactions, whoever calls
and however deep, the word of slot 5 (`_totalSupply`) is at most what it was before the first
one. Nothing is assumed about the storage at the start. -/
theorem supply_never_grows_any_transactions {C : Address} {b b' : BlockState}
    (chain : Seq.Chain C CODE SepMsg b b')
    (hold : Seq.HoldsCode C CODE (TransactionState.ofBlock b)) :
    (storageAt (TransactionState.ofBlock b') C 5).toNat ≤
      (storageAt (TransactionState.ofBlock b) C 5).toNat :=
  (level_any_transactions chain ⟨hold, level_self C _⟩).2.2

end WbtVerify

import EthLib.Execution.Proofs.Evm.Call.StaticMessage
import EthLib.Execution.Proofs.Evm.Call.Parent
import EthLib.Execution.Proofs.Evm.Logic.Keeps
import EthLib.Execution.Proofs.Evm.Logic.Message
import EthLib.Execution.Proofs.Evm.Logic.Callee
import UsdtVerify.Evm.At
import UsdtVerify.Evm.Write
import UsdtVerify.Evm.Storage

/-!
# One step of any frame keeps the code and the invariant of a contract

GENERIC kit file: nothing here is about one token. It is the step part of the reentrancy
induction of `tokens/wbtc/WbtcVerify/Wbtc/Reenter.lean` (same as the one of LINK), moved into the
kit, without the global hypothesis `NoCollision`, and with one more tracked fact (`Unmarked`).

`L` is the address of a contract, `CODE` its code, `P` an invariant of its storage.

- `HoldsCode L CODE S`: in the state `S` the account of `L` holds `CODE`.
- `Good L CODE P S`: `L` holds `CODE` and `P` holds.
- `Kept L S S'`: the change from `S` to `S'` keeps the code table, the code hash and the storage
  of `L`, and does not record `L` as created in this transaction.
- `Unmarked L evm`: `L` is not recorded as created in this transaction, and is not in the list of
  the accounts to delete at the end of the transaction. From Dencun (EIP-6780) SELFDESTRUCT only
  lists an account that was created in the same transaction, so every step keeps `Unmarked`.
  This is what lets the end of a transaction (`deleteAccounts`) keep the account of `L`.
- `W L CODE P a b`: a step from the frame `a` to the frame `b` keeps the message and the code of
  `L`; in a frame at another address than `L` it keeps a good state good; from Dencun it keeps
  `Unmarked`.
- `res_step`: every successful step of EthLib's `step`, at every fork, static or not, is such a
  step, and a message that it sends is sane.

Hypothesis used: `delegatedAddress CODE = none` (closed fact of a token: its code is not an
EIP-7702 delegation indicator).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TokenKit.Seq

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState EMPTY_CODE_HASH)
open EthLib.Execution.Evm

variable {fork : Fork}

/-! ## The interface -/

/-- The account of `L` holds the code `CODE` in the state `S`.

The code hash of the account reads as `CODE`, is not the empty hash, and is the hash of `CODE`.
-/
def HoldsCode (L : Address) (CODE : ByteArray) (S : State.TransactionState) : Prop :=
  S.getCode (S.getAccount L).codeHash = .ok CODE ∧
    (S.getAccount L).codeHash ≠ EMPTY_CODE_HASH ∧
    (S.getAccount L).codeHash = Cryptography.Hash.Keccak.keccak256 CODE

/-- `L` holds `CODE` and the invariant `P` holds. -/
def Good (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop)
    (S : State.TransactionState) : Prop :=
  HoldsCode L CODE S ∧ P S

/-- A message that runs at `L` is a call that runs `CODE`, with call data below 2^256 bytes. -/
def Sane (L : Address) (CODE : ByteArray) (msg : Message fork) : Prop :=
  msg.currentTarget = L →
    msg.code = CODE ∧ msg.target.isSome = true ∧ msg.data.size < 2 ^ 256

/-- A good state stays good. -/
def GoodKept (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop)
    (tx tx' : State.TransactionState) : Prop :=
  Good L CODE P tx → Good L CODE P tx'

/-- The invariant `P` reads only the storage of `L`. -/
def StorageOnly (L : Address) (P : State.TransactionState → Prop) : Prop :=
  ∀ S S', (∀ k, S'.getStorage L k = S.getStorage L k) → P S → P S'

variable {G : Nat} {L : Address} {CODE : ByteArray} {P : State.TransactionState → Prop}

/-! ## The code of `L` under reads and writes of the state -/

/-- Two states with the same optional account at an address have the same account there. -/
theorem getAccount_congr {S S' : TransactionState} {a : Address}
    (h : S'.getAccountOptional a = S.getAccountOptional a) : S'.getAccount a = S.getAccount a := by
  unfold TransactionState.getAccount
  rw [h]

/-- A state with the account of `L` and the code table of `S` holds `CODE` as `S` does. -/
theorem holdsCode_of_eq {S S' : TransactionState} (ha : S'.getAccount L = S.getAccount L)
    (hc : S'.getCode = S.getCode) (h : HoldsCode L CODE S) : HoldsCode L CODE S' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact And.intro (by rw [ha, hc]; exact h1)
    (And.intro (by rw [ha]; exact h2) (by rw [ha]; exact h3))

/-- An account that holds code exists. -/
theorem HoldsCode.hasAccount {S : TransactionState} (h : HoldsCode L CODE S) :
    UsdtVerify.hasAccount S L := by
  show (S.getAccountOptional L).isSome = true
  cases hopt : S.getAccountOptional L with
  | some a => rfl
  | none =>
    have hh : (S.getAccount L).codeHash = EMPTY_CODE_HASH := by
      unfold TransactionState.getAccount
      rw [hopt]
      rfl
    exact absurd hh h.2.1

/-- A record of an account read keeps the code of `L`. -/
theorem holdsCode_recordAccountRead {S : TransactionState} (address : Address)
    (h : HoldsCode L CODE S) : HoldsCode L CODE (S.recordAccountRead address) :=
  holdsCode_of_eq rfl rfl h

/-- A record of a storage read keeps the code of `L`. -/
theorem holdsCode_recordStorageRead {S : TransactionState} (address : Address) (key : Bytes32)
    (h : HoldsCode L CODE S) : HoldsCode L CODE (S.recordStorageRead address key) :=
  holdsCode_of_eq rfl rfl h

/-- A storage write keeps the code of `L`, at every address, `L` included. -/
theorem holdsCode_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx')
    (hold : HoldsCode L CODE tx) : HoldsCode L CODE tx' :=
  holdsCode_of_eq (getAccount_congr (TransactionState.getAccountOptional_setStorage h))
    (funext (TransactionState.getCode_setStorage h)) hold

/-- The state after SLOAD of a slot keeps the code of `L`. -/
theorem holdsCode_readSlot {S : TransactionState} (target : Address) (n : U256)
    (h : HoldsCode L CODE S) : HoldsCode L CODE (UsdtVerify.readSlot S target n) :=
  holdsCode_of_eq rfl rfl h

/-- The state after SSTORE of a slot keeps the code of `L`, at every address, `L` included. -/
theorem holdsCode_writeSlot {S : TransactionState} (target : Address) (n v : U256)
    (h : HoldsCode L CODE S) : HoldsCode L CODE (UsdtVerify.writeSlot S target n v) := by
  unfold UsdtVerify.writeSlot
  split
  · rename_i s hs
    exact holdsCode_setStorage hs (holdsCode_recordStorageRead _ _ h)
  · exact h

/-- A state that reads as `S` holds the code that `S` holds. -/
theorem HoldsCode.of_readsAs {tx S : TransactionState} (r : Logic.ReadsAs tx S)
    (h : HoldsCode L CODE S) : HoldsCode L CODE tx :=
  holdsCode_of_eq (getAccount_congr (r.1 L (by simp)).1) (funext r.2) h

/-- A state `S` holds the code that a state that reads as `S` holds. -/
theorem HoldsCode.to_readsAs {tx S : TransactionState} (r : Logic.ReadsAs tx S)
    (h : HoldsCode L CODE tx) : HoldsCode L CODE S :=
  holdsCode_of_eq (getAccount_congr (r.1 L (by simp)).1.symm)
    (funext fun c => (r.2 c).symm) h

/-- A state that reads as a good state is good. -/
theorem Good.of_readsAs (so : StorageOnly L P) {tx S : TransactionState}
    (r : Logic.ReadsAs tx S) (g : Good L CODE P S) : Good L CODE P tx :=
  And.intro (HoldsCode.of_readsAs r g.1) (so S tx (fun k => (r.1 L (by simp)).2.1 k) g.2)

/-- A state `S` is good when a state that reads as `S` is good. -/
theorem Good.to_readsAs (so : StorageOnly L P) {tx S : TransactionState}
    (r : Logic.ReadsAs tx S) (g : Good L CODE P tx) : Good L CODE P S :=
  And.intro (HoldsCode.to_readsAs r g.1)
    (so tx S (fun k => ((r.1 L (by simp)).2.1 k).symm) g.2)

/-! ## A change of the state that keeps the code and the storage of `L` -/

/-- The state `S'` has the code table of `S`.

When `L` holds code in `S`, `S'` has the code hash and the storage of `L` in `S`. -/
structure Kept (L : Address) (S S' : TransactionState) : Prop where
  code : S'.getCode = S.getCode
  hash : (S.getAccount L).codeHash ≠ EMPTY_CODE_HASH →
    (S'.getAccount L).codeHash = (S.getAccount L).codeHash
  storage : (S.getAccount L).codeHash ≠ EMPTY_CODE_HASH →
    ∀ key, S'.getStorage L key = S.getStorage L key
  created : L ∈ S'.createdAccounts → L ∈ S.createdAccounts

theorem Kept.refl (L : Address) (S : TransactionState) : Kept L S S :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, id⟩

theorem Kept.trans {a b c : TransactionState} (hab : Kept L a b) (hbc : Kept L b c) :
    Kept L a c :=
  ⟨hbc.code.trans hab.code,
    fun h => (hbc.hash (by rw [hab.hash h]; exact h)).trans (hab.hash h),
    fun h key => (hbc.storage (by rw [hab.hash h]; exact h) key).trans (hab.storage h key),
    fun h => hab.created (hbc.created h)⟩

theorem Kept.holdsCode {S S' : TransactionState} (k : Kept L S S') (h : HoldsCode L CODE S) :
    HoldsCode L CODE S' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e := k.hash h2
  exact And.intro (by rw [e, k.code]; exact h1)
    (And.intro (by rw [e]; exact h2) (by rw [e]; exact h3))

theorem Kept.good (so : StorageOnly L P) {S S' : TransactionState} (k : Kept L S S')
    (g : Good L CODE P S) : Good L CODE P S' :=
  And.intro (k.holdsCode g.1) (so S S' (k.storage g.1.2.1) g.2)

theorem Kept.of_sameOutside {touched : List Address} {S S' : TransactionState}
    (so : TransactionState.SameOutside touched S S') (hL : L ∉ touched)
    (hc : S'.getCode = S.getCode) (hcr : S'.createdAccounts = S.createdAccounts) : Kept L S S' :=
  ⟨hc, fun _ => congrArg _ (getAccount_congr (so L hL).1), fun _ key => (so L hL).2.1 key,
    fun h => (congrArg (fun s => L ∈ s) hcr).mp h⟩

theorem kept_recordAccountRead (tx : TransactionState) (address : Address) :
    Kept L tx (tx.recordAccountRead address) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, id⟩

theorem kept_setTransientStorage (tx : TransactionState) (address : Address) (key : Bytes32)
    (value : U256) : Kept L tx (tx.setTransientStorage address key value) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, id⟩

/-- A change of one account that keeps its code hash keeps the code and the storage of `L`. -/
theorem kept_modifyState {tx tx' : TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account}
    (h : tx.modifyState fork address f = .ok tx')
    (hf : ∀ a b, f a = .ok b → b.codeHash = a.codeHash) : Kept L tx tx' := by
  have hash : (tx'.getAccount L).codeHash = (tx.getAccount L).codeHash := by
    obtain ⟨account, hfa, hget, hother⟩ := TransactionState.modifyState_eq_ok h
    by_cases hL : L = address
    · subst hL
      rw [hget]
      exact hf _ _ hfa
    · rw [hother L hL]
  refine ⟨TransactionState.getCode_modifyState h, fun _ => hash, fun hne key => ?_,
    fun hc => (congrArg (fun s => L ∈ s) (TransactionState.createdAccounts_modifyState h)).mp hc⟩
  rw [TransactionState.getStorage_modifyState h L key]
  split
  · rename_i hc
    obtain ⟨hLa, hnone⟩ := hc
    exfalso
    apply hne
    rw [← hash]
    unfold TransactionState.getAccount
    rw [hLa, hnone]
    rfl
  · rfl

theorem kept_moveEther {tx tx' : TransactionState} {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') : Kept L tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  refine (kept_modifyState h1 ?_).trans (kept_modifyState h2 ?_)
  · intro a b hab
    unfold State.Account.debit at hab
    split at hab <;> cases hab
    rfl
  · intro a b hab
    unfold State.Account.credit at hab
    split at hab <;> cases hab
    rfl

theorem kept_createEther {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.createEther fork address amount = .ok tx') : Kept L tx tx' := by
  unfold TransactionState.createEther at h
  refine kept_modifyState h ?_
  intro a b hab
  unfold State.Account.credit at hab
  split at hab <;> cases hab
  rfl

theorem kept_setAccountBalance {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.setAccountBalance fork address amount = .ok tx') : Kept L tx tx' := by
  unfold TransactionState.setAccountBalance at h
  refine kept_modifyState h ?_
  intro a b hab
  cases hab
  rfl

theorem kept_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : Kept L tx tx' := by
  unfold TransactionState.incrementNonce at h
  refine kept_modifyState h ?_
  intro a b hab
  cases hab
  rfl

theorem kept_selfdestructTransfer {tx tx' : TransactionState} {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') : Kept L tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (kept_moveEther h1).trans (kept_setAccountBalance h)
    · cases h
      exact kept_moveEther h1
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (kept_createEther h1).trans (kept_setAccountBalance h)

/-- A storage write keeps the record of the accounts that the transaction created. -/
theorem createdAccounts_setStorage {tx tx' : TransactionState} {address : Address}
    {key : Bytes32} {value : U256} (h : tx.setStorage address key value = .ok tx') :
    tx'.createdAccounts = tx.createdAccounts := by
  unfold TransactionState.setStorage at h
  split at h
  · cases h
  · cases h
    rfl

/-- A storage write at another address keeps the code and the storage of `L`. -/
theorem kept_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') (hne : L ≠ address) :
    Kept L tx tx' :=
  ⟨funext (TransactionState.getCode_setStorage h),
    fun _ => congrArg _ (getAccount_congr (TransactionState.getAccountOptional_setStorage h)),
    fun _ k => TransactionState.getStorage_setStorage_of_ne h (Or.inl hne),
    fun hc => (congrArg (fun s => L ∈ s) (createdAccounts_setStorage h)).mp hc⟩

theorem kept_touchAccount (tx : TransactionState) (address : Address) :
    Kept L tx (tx.touchAccount address) := by
  refine ⟨funext (TransactionState.getCode_touchAccount tx address), fun _ => ?_,
    fun _ key => ?_, ?_⟩
  · by_cases hL : L = address
    · subst hL
      rw [TransactionState.getAccount_touchAccount_self]
    · rw [TransactionState.getAccount_touchAccount hL]
  · unfold TransactionState.touchAccount
    split
    · rfl
    · rfl
  · unfold TransactionState.touchAccount
    split
    · exact id
    · exact id

theorem kept_startState (message : Message fork) (state : TransactionState) :
    Kept L state (startState fork message state) := by
  unfold startState
  split
  · exact kept_touchAccount _ _
  · exact Kept.refl _ _

/-- The start of a creation at another address keeps the code and the storage of `L`. -/
theorem kept_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') (hne : L ≠ address) : Kept L tx tx' := by
  have k0 : Kept L tx ((tx.destroyStorage address).markAccountCreated address) :=
    ⟨rfl, fun _ => rfl, fun _ key => TransactionState.getStorage_destroyStorage_of_ne tx hne key,
      fun h => by
        have h' : L ∈ tx.createdAccounts.insert address := h
        simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at h'
        rcases h' with e | h'
        · exact absurd e.symm hne
        · exact h'⟩
  unfold prepareCreation at h
  split at h
  · exact k0.trans (kept_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact k0

/-- A rollback to a snapshot of the same block holds the code that the snapshot holds. -/
theorem holdsCode_restore {tx snapshot : TransactionState} (hp : tx.parent = snapshot.parent)
    (hold : HoldsCode L CODE snapshot) : HoldsCode L CODE (tx.restoreTxState snapshot) :=
  holdsCode_of_eq (getAccount_congr (TransactionState.getAccountOptional_restoreTxState hp L))
    (funext (TransactionState.getCode_restoreTxState hp)) hold

/-- A rollback to a good snapshot of the same block is good. -/
theorem good_restore (so : StorageOnly L P) {tx snapshot : TransactionState}
    (hp : tx.parent = snapshot.parent) (g : Good L CODE P snapshot) :
    Good L CODE P (tx.restoreTxState snapshot) :=
  And.intro (holdsCode_restore hp g.1)
    (so _ _ (fun k => TransactionState.getStorage_restoreTxState hp L k) g.2)

/-- An address where a creation may deploy is not `L`, which holds code. -/
theorem ne_of_deployable {S : TransactionState} {address : Address}
    (hold : HoldsCode L CODE S) (hd : S.accountDeployable address = true) : address ≠ L := by
  intro e
  subst e
  unfold TransactionState.accountDeployable at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  exact hold.2.1 hd.2

/-! ## The steps that only read the state

These are the static steps of EthLib (`StaticStep`), with the code table of the state added.
-/

/-- A step that keeps its message, its state up to the records of reads, and the code table. -/
structure QS (before after : Evm fork Nat) : Prop where
  state : StateKept before after
  message : after.message = before.message
  codes : after.state.getCode = before.state.getCode
  created : after.state.createdAccounts = before.state.createdAccounts
  dels : after.substate.accountsToDelete = before.substate.accountsToDelete

theorem QS.refl (evm : Evm fork Nat) : QS evm evm := ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

theorem QS.trans {a b c : Evm fork Nat} (hab : QS a b) (hbc : QS b c) : QS a c :=
  ⟨hab.state.trans hbc.state, hbc.message.trans hab.message, hbc.codes.trans hab.codes,
    hbc.created.trans hab.created, hbc.dels.trans hab.dels⟩

theorem QS.of_sameContext {a b : Evm fork Nat} (h : SameContext a b) : QS a b :=
  ⟨StateKept.of_sameContext h, h.message, by rw [h.state], by rw [h.state], by rw [h.substate]⟩

theorem QS.withMemory (evm : Evm fork Nat) (memory : ByteArray) :
    QS evm { evm with memory } := ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

theorem QS.adv {a b : Evm fork Nat} (h : QS a b) (n : Nat := 1) : QS a (Evm.advance b n) :=
  ⟨h.state, h.message, h.codes, h.created, h.dels⟩

theorem QS.kept {a b : Evm fork Nat} (h : QS a b) : Kept L a.state b.state :=
  Kept.of_sameOutside h.state (by simp) h.codes h.created

theorem qs_recordAccountRead (evm : Evm fork Nat) (address : Address) :
    QS evm (recordAccountRead evm address) :=
  ⟨stateKept_recordAccountRead evm address, rfl, rfl, rfl, rfl⟩

theorem qs_recordStorageRead (evm : Evm fork Nat) (address : Address) (key : Bytes32) :
    QS evm (recordStorageRead evm address key) :=
  ⟨stateKept_recordStorageRead evm address key, rfl, rfl, rfl, rfl⟩

theorem qs_accessAddress (evm : Evm fork Nat) (address : Address) :
    QS evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  exact ⟨stateKept_accessAddress evm address, by rw [h], by rw [h], by rw [h], by rw [h]⟩

theorem qs_accessStorageKey (evm : Evm fork Nat) (address : Address) (key : Bytes32) :
    QS evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  exact ⟨stateKept_accessStorageKey evm address key, by rw [h], by rw [h], by rw [h], by rw [h]⟩

theorem qs_exceptionalHalt (evm : Evm fork Nat) (e : EvmError) :
    QS evm (exceptionalHalt evm e) := ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

theorem qs_balanceStep {evm after : Evm fork Nat} (h : balanceStep evm = .ok after) :
    QS evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : QS e1 e2 := by
    have := qs_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QS.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QS.of_sameContext (chargeGas_sameContext h3))).trans
    (qs_recordAccountRead _ _)).trans
    (QS.of_sameContext (pushWord_sameContext h4)) |>.adv

theorem qs_extcodesizeStep {evm after : Evm fork Nat}
    (h : extcodesizeStep evm = .ok after) : QS evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : QS e1 e2 := by
    have := qs_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QS.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QS.of_sameContext (chargeGas_sameContext h3))).trans
    (qs_recordAccountRead _ _)).trans
    (QS.of_sameContext (pushWord_sameContext h5)) |>.adv

theorem qs_extcodehashStep {evm after : Evm fork Nat}
    (h : extcodehashStep evm = .ok after) : QS evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : QS e1 e2 := by
    have := qs_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((QS.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QS.of_sameContext (chargeGas_sameContext h3))).trans
    (qs_recordAccountRead _ _)).trans
    (QS.of_sameContext (pushWord_sameContext h4)) |>.adv

theorem qs_extcodecopyStep {evm after : Evm fork Nat}
    (h : extcodecopyStep evm = .ok after) : QS evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : QS e4 e5 := by
    have := qs_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((QS.of_sameContext (popWord_sameContext h1)).trans
    (QS.of_sameContext (popWord_sameContext h2))).trans
    (QS.of_sameContext (popWord_sameContext h3))).trans
    (QS.of_sameContext (popWord_sameContext h4))).trans ha).trans
    (QS.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
    (qs_recordAccountRead _ _)).trans (QS.withMemory _ _) |>.adv

theorem qs_accountStep {op : Op} {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Nat}
    (h : step evm = .ok after) : QS evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact qs_balanceStep h
  case extcodesize => subst hstep; exact qs_extcodesizeStep h
  case extcodecopy => subst hstep; exact qs_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (qs_recordAccountRead _ _).trans (QS.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact qs_extcodehashStep h
    · cases hstep

theorem qs_sloadStep {evm after : Evm fork Nat} (h : sloadStep evm = .ok after) :
    QS evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : QS e1 e2 := by
    have := qs_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((QS.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (QS.of_sameContext (chargeGas_sameContext h3))).trans
    (qs_recordStorageRead _ _ _)).trans
    (QS.of_sameContext (pushWord_sameContext h4)) |>.adv

theorem qs_returnOpStep {op : Op} {step : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Nat}
    (h : step evm = .ok after) : QS evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact QS.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep; exact QS.of_sameContext (revertStep_sameContext h)
    · cases hstep

theorem qs_popCallOperands {kind : CallKind} {evm after : Evm fork Nat}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) : QS evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : QS e2 e3 := by
    unfold popCallValue at h3
    split at h3
    · exact QS.of_sameContext (popWord_sameContext h3)
    · cases h3
      exact QS.refl _
  exact (((((((QS.of_sameContext (popWord_sameContext h1)).trans
    (QS.of_sameContext (popWord_sameContext h2))).trans p3).trans
    (QS.of_sameContext (popWord_sameContext h4))).trans
    (QS.of_sameContext (popWord_sameContext h5))).trans
    (QS.of_sameContext (popWord_sameContext h6))).trans
    (QS.of_sameContext (popWord_sameContext h7)))

theorem qs_accessDelegation {evm after : Evm fork Nat} {address : Address}
    {known : Nat} {callee : Callee} (h : accessDelegation evm address known = .ok (callee, after)) :
    QS evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (qs_accessAddress _ _).trans (qs_recordAccountRead _ _)
  · cases h
    exact QS.refl _

theorem qs_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Nat}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    QS evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((QS.of_sameContext (chargeGas_sameContext h1)).trans
      (QS.of_sameContext (chargeStateGas_sameContext h2))).trans
      (QS.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact QS.of_sameContext (chargeGas_sameContext h1)

theorem qs_skipCall {evm after : Evm fork Nat} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : QS evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

theorem qs_runPrecompile {address : Nat} {evm after : Evm fork Nat}
    (h : runPrecompile fork address evm = some after) : QS evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact qs_exceptionalHalt _ _
  · split at h
    · cases h
      exact qs_exceptionalHalt _ _
    · cases h
      exact ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩

/-- A call to `L` runs `CODE`: the call reads the code of `L` from the state.

`CODE` is not a delegation indicator, so the call follows no delegation. -/
theorem code_accessDelegation (hdel : delegatedAddress CODE = none) {evm after : Evm fork Nat}
    {address : Address} {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after))
    (hold : HoldsCode L CODE evm.state) (hL : address = L) : callee.code = CODE := by
  unfold accessDelegation at h
  obtain ⟨code, hc, h⟩ := Base.bind_ok_iff.mp h
  have hcode : code = CODE := by
    unfold accountCode at hc
    have hg := Base.mapError_ok_iff.mp hc
    rw [hL, hold.1] at hg
    cases hg
    rfl
  dsimp only at h
  split at h
  · rename_i d hd
    rw [hcode, hdel] at hd
    simp at hd
  · cases h
    exact hcode

/-! ## One step of a frame -/

/-- `L` is not recorded as created in this transaction, and is not in the list of the accounts
to delete at the end of the transaction. -/
structure Unmarked (L : Address) (evm : Evm fork Nat) : Prop where
  created : L ∉ evm.state.createdAccounts
  dels : L ∉ evm.substate.accountsToDelete

theorem QS.unmarked {L : Address} {a b : Evm fork Nat} (h : QS a b) (u : Unmarked L a) :
    Unmarked L b :=
  ⟨fun hc => u.created ((congrArg (fun s => L ∈ s) h.created).mp hc),
    fun hd => u.dels ((congrArg (fun s => L ∈ s) h.dels).mp hd)⟩

/-- A step from the frame `a` to the frame `b` that keeps the message.

It keeps the code of `L`. In a frame at another address than `L` it keeps a good state good.
From Dencun it keeps `Unmarked`. -/
structure W (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop)
    (a b : Evm fork Nat) : Prop where
  message : b.message = a.message
  holds : HoldsCode L CODE a.state → HoldsCode L CODE b.state
  good : a.message.currentTarget ≠ L → Good L CODE P a.state → Good L CODE P b.state
  safe : Fork.dencun ≤ fork → HoldsCode L CODE a.state → Unmarked L a → Unmarked L b

theorem W.refl (a : Evm fork Nat) : W L CODE P a a := ⟨rfl, id, fun _ => id, fun _ _ => id⟩

theorem W.trans {a b c : Evm fork Nat} (hab : W L CODE P a b) (hbc : W L CODE P b c) :
    W L CODE P a c :=
  ⟨hbc.message.trans hab.message, fun h => hbc.holds (hab.holds h),
    fun t g => hbc.good (by rw [hab.message]; exact t) (hab.good t g),
    fun hf h u => hbc.safe hf (hab.holds h) (hab.safe hf h u)⟩

theorem W.of_kept (so : StorageOnly L P) {a b : Evm fork Nat} (m : b.message = a.message)
    (k : Kept L a.state b.state)
    (d : b.substate.accountsToDelete = a.substate.accountsToDelete) : W L CODE P a b :=
  ⟨m, k.holdsCode, fun _ g => k.good so g, fun _ _ u =>
    ⟨fun hc => u.created (k.created hc),
      fun hd => u.dels ((congrArg (fun s => L ∈ s) d).mp hd)⟩⟩

theorem QS.w (so : StorageOnly L P) {a b : Evm fork Nat} (h : QS a b) : W L CODE P a b :=
  W.of_kept so h.message h.kept h.dels

/-- SSTORE writes the storage of the address of its frame, and no code. -/
theorem w_sstoreStep (so : StorageOnly L P) {evm after : Evm fork Nat}
    (h : sstoreStep evm = .ok after) : W L CODE P evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 : QS evm e2 := (QS.of_sameContext (popWord_sameContext h1)).trans
    (QS.of_sameContext (popWord_sameContext h2))
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
      ⟨cold, e3⟩
    have ha : QS e2 e3 := by
      have := qs_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
      rwa [hpair] at this
    simp only [hpair] at h
    have c3 : QS evm (recordStorageRead e3 e2.message.currentTarget (U256.toBeBytes k)) :=
      (c2.trans ha).trans (qs_recordStorageRead _ _ _)
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.message = evm.message := by
        rw [(chargeStateGas_sameContext h5).message, (chargeGas_sameContext h4).message]
        exact c3.message
      have k5 : Kept L evm.state e5.state := by
        rw [(chargeStateGas_sameContext h5).state, (chargeGas_sameContext h4).state]
        exact c3.kept
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        have hset := Base.mapError_ok_iff.mp hst
        have d5 : e5.substate.accountsToDelete = evm.substate.accountsToDelete := by
          rw [(chargeStateGas_sameContext h5).substate, (chargeGas_sameContext h4).substate]
          exact c3.dels
        refine ⟨m5, fun hold => holdsCode_setStorage hset (k5.holdsCode hold), fun t g => ?_,
          fun _ _ u => ⟨fun hc => u.created (k5.created
              ((congrArg (fun s => L ∈ s) (createdAccounts_setStorage hset)).mp hc)),
            fun hd => u.dels ((congrArg (fun s => L ∈ s) d5).mp hd)⟩⟩
        refine (kept_setStorage hset ?_).good so (k5.good so g)
        rw [c2.message]
        exact fun e => t e.symm
    · exact W.of_kept so c3.message c3.kept c3.dels

/-- TSTORE writes no storage and no code. -/
theorem w_tstoreStep (so : StorageOnly L P) {evm after : Evm fork Nat}
    (h : tstoreStep evm = .ok after) : W L CODE P evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  have c3 : QS evm e3 := ((QS.of_sameContext (popWord_sameContext h1)).trans
    (QS.of_sameContext (popWord_sameContext h2))).trans
    (QS.of_sameContext (chargeGas_sameContext h3))
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact W.of_kept so c3.message (c3.kept.trans (kept_setTransientStorage e3.state _ _ _))
      c3.dels

/-- SELFDESTRUCT moves a balance, and writes no storage and no code in its step. -/
theorem w_selfdestructStep (so : StorageOnly L P) {evm after : Evm fork Nat}
    (h : selfdestructStep fork evm = .ok after) : W L CODE P evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : QS e1 e2 := by
    have := qs_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c : QS evm (recordAccountRead e2 (toAddressMasked w)) :=
    ((QS.of_sameContext (popWord_sameContext h1)).trans ha).trans
      (qs_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeStateGas_sameContext h4).message, (chargeGas_sameContext h3).message]
      exact c.message
    have k4 : Kept L evm.state e4.state := by
      rw [(chargeStateGas_sameContext h4).state, (chargeGas_sameContext h3).state]
      exact c.kept
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have d4 : e4.substate.accountsToDelete = evm.substate.accountsToDelete := by
        rw [(chargeStateGas_sameContext h4).substate, (chargeGas_sameContext h3).substate]
        exact c.dels
      have kall : Kept L evm.state st :=
        k4.trans (kept_selfdestructTransfer (Base.mapError_ok_iff.mp hst))
      refine ⟨m4, kall.holdsCode, fun _ g => kall.good so g, fun hf _ u =>
        ⟨fun hc => u.created (kall.created hc), fun hd => ?_⟩⟩
      have hd' : L ∈ (if fork < Fork.dencun ∨ e4.message.currentTarget ∈ st.createdAccounts then
          e4.substate.accountsToDelete.insert e4.message.currentTarget
        else e4.substate.accountsToDelete) := hd
      split at hd'
      · rename_i hdel
        simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_iff_eq] at hd'
        rcases hd' with e | hd'
        · rcases hdel with hlt | hcr
          · exact absurd hlt (Nat.not_lt.mpr hf)
          · exact u.created (kall.created (e ▸ hcr))
        · exact u.dels ((congrArg (fun s => L ∈ s) d4).mp hd')
      · exact u.dels ((congrArg (fun s => L ∈ s) d4).mp hd')
  · exact W.of_kept so c.message c.kept c.dels

/-- Each instruction that gives the next frame keeps the code of `L`.

In a frame at another address it keeps a good state good. -/
theorem w_instruction (so : StorageOnly L P) {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {evm after : Evm fork Nat}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    W L CODE P evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact (QS.of_sameContext (stackOnlyStep_sameContext hf h)).w so
  rcases orElse_eq_some hrun with hf | hrun
  · exact (QS.of_sameContext (controlFlowStep_sameContext hf h)).w so
  rcases orElse_eq_some hrun with hf | hrun
  · exact (QS.of_sameContext (memoryDataStep_sameContext hf h)).w so
  rcases orElse_eq_some hrun with hf | hrun
  · exact (qs_returnOpStep hf h).w so
  rcases orElse_eq_some hrun with hf | hrun
  · exact (QS.of_sameContext (environmentStep_sameContext hf h)).w so
  rcases orElse_eq_some hrun with hf | hrun
  · exact (qs_accountStep hf h).w so
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact (qs_sloadStep h).w so
    case sstore => subst hf; exact w_sstoreStep so h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact (QS.of_sameContext (tloadStep_sameContext h)).w so
    · exact w_tstoreStep so h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, hm, hs, hsub⟩ := logStep_eq_ok h
    exact W.of_kept so hm (by rw [hs]; exact Kept.refl _ _) (by rw [hsub])
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact w_selfdestructStep so h

/-! ## The calls and the creations -/

/-- A read of memory gives at most the `size` bytes asked for, within memory or not. -/
theorem size_memoryReadBytes_le (memory : ByteArray) (start size : Nat) :
    (memoryReadBytes memory start size).size ≤ size := by
  unfold memoryReadBytes
  split
  · simp
  · simp only [ByteArray.size_extract]
    omega

/-- A creation runs at another address than `L`. -/
def Sane0 (L : Address) (message : Message fork) : Prop :=
  message.target = none → message.currentTarget ≠ L

/-- A result of a step from `evm`, under a fact `H` of the state of `evm`.

The next frame, or the frame that sends a message, is a `W` step from `evm`.

Under `H`, a creation that it sends runs at another address than `L`, and a message that a
frame at another address than `L` sends is sane.

The frame that resumes has the message of the sender and the state that ends the message. Its
accounts to delete are among those of the sender and those of the frame that ends the message. -/
def Res (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop) (H : Prop)
    (evm : Evm fork Nat) : StepResult fork Nat → Prop
  | .next after => W L CODE P evm after
  | .child caller message resume => W L CODE P evm caller ∧
      (H → Sane0 L message ∧ (evm.message.currentTarget ≠ L → Sane L CODE message)) ∧
      ∀ child after, resume child = .ok after →
        after.message = caller.message ∧ after.state = child.state ∧
        (L ∈ after.substate.accountsToDelete →
          L ∈ caller.substate.accountsToDelete ∨ L ∈ child.substate.accountsToDelete)

theorem Res.lift {H : Prop} {evm evm' : Evm fork Nat} {result : StepResult fork Nat}
    (h : W L CODE P evm evm') (r : Res L CODE P H evm' result) : Res L CODE P H evm result := by
  cases result with
  | next after => exact h.trans (r : W L CODE P evm' after)
  | child caller message resume =>
    obtain ⟨c, s, m⟩ := r
    exact ⟨h.trans c, fun hH => ⟨(s hH).1, fun t => (s hH).2 (by rw [h.message]; exact t)⟩, m⟩

theorem Res.mono {H H' : Prop} {evm : Evm fork Nat} {result : StepResult fork Nat}
    (hH : H' → H) (r : Res L CODE P H evm result) : Res L CODE P H' evm result := by
  cases result with
  | next after => exact r
  | child caller message resume =>
    obtain ⟨c, s, m⟩ := r
    exact ⟨c, fun h => s (hH h), m⟩

/-- The caller that resumes after a call keeps its message. -/
theorem message_resumeCall {caller child after : Evm fork Nat} {newAccount : Nat}
    {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after) :
    after.message = caller.message := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  show e.message = caller.message
  rw [(pushWord_sameContext h1).message]
  split <;> simp [message_incorporateChild, refillStateGas]

/-- The creator that resumes after a creation keeps its message. -/
theorem message_resumeCreate {caller child after : Evm fork Nat} {newAccount : Nat}
    {address : Address} (h : resumeCreate fork caller newAccount address child = .ok after) :
    after.message = caller.message := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  show e.message = caller.message
  rw [(pushWord_sameContext h1).message]
  split <;> simp [message_incorporateChild, refillStateGas]

/-- The accounts to delete of a caller that takes back a child are among those of the two. -/
theorem dels_incorporateChild (caller child : Evm fork Nat) (x : Address)
    (h : x ∈ (incorporateChild fork caller child).substate.accountsToDelete) :
    x ∈ caller.substate.accountsToDelete ∨ x ∈ child.substate.accountsToDelete := by
  unfold incorporateChild at h
  dsimp only at h
  split at h
  · rcases Std.ExtTreeSet.mem_insertMany_list.mp h with h' | h'
    · exact .inl h'
    · exact .inr (Std.ExtTreeSet.mem_toList.mp (List.contains_iff_mem.mp h'))
  · exact .inl h

/-- The accounts to delete of the caller that resumes after a call. -/
theorem dels_resumeCall {caller child after : Evm fork Nat} {newAccount : Nat}
    {outputStart outputSize : U256} {x : Address}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (hx : x ∈ after.substate.accountsToDelete) :
    x ∈ caller.substate.accountsToDelete ∨ x ∈ child.substate.accountsToDelete := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hx' : x ∈ e.substate.accountsToDelete := hx
  rw [(pushWord_sameContext h1).substate] at hx'
  dsimp only at hx'
  split at hx'
  · exact dels_incorporateChild caller child x hx'
  · exact dels_incorporateChild caller child x hx'

/-- The accounts to delete of the creator that resumes after a creation. -/
theorem dels_resumeCreate {caller child after : Evm fork Nat} {newAccount : Nat}
    {address : Address} {x : Address}
    (h : resumeCreate fork caller newAccount address child = .ok after)
    (hx : x ∈ after.substate.accountsToDelete) :
    x ∈ caller.substate.accountsToDelete ∨ x ∈ child.substate.accountsToDelete := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hx' : x ∈ e.substate.accountsToDelete := hx
  rw [(pushWord_sameContext h1).substate] at hx'
  dsimp only at hx'
  split at hx'
  · exact dels_incorporateChild caller child x hx'
  · exact dels_incorporateChild caller child x hx'

theorem res_genericCall (so : StorageOnly L P) {H : Prop} {evm : Evm fork Nat}
    {message : Message fork} {newAccount : Nat} {outputStart outputSize : U256}
    {result : StepResult fork Nat}
    (hs : H → Sane0 L message ∧ (evm.message.currentTarget ≠ L → Sane L CODE message))
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    Res L CODE P H evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hsk, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hsk
    exact W.of_kept so q.message q.kept q.dels
  · cases h
    exact ⟨W.of_kept so rfl (Kept.refl _ _) rfl, hs, fun child after hres =>
      ⟨message_resumeCall hres, state_resumeCall hres, dels_resumeCall hres⟩⟩

theorem res_finishCall (so : StorageOnly L P) {H : Prop} {kind : CallKind}
    {call : CallOperands} {callee : Callee} {subCall newAccount expandBy : Nat}
    {evm : Evm fork Nat} {result : StepResult fork Nat}
    (hc : H → call.address = L → callee.code = CODE)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    Res L CODE P H evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hsk, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hsk
    exact W.of_kept so q.message ((kept_recordAccountRead evm.state _).trans q.kept) q.dels
  · refine Res.lift (evm' := recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget)
      (W.of_kept so rfl (kept_recordAccountRead evm.state _) rfl) (res_genericCall so ?_ h)
    intro hH
    refine ⟨fun hn => ?_, fun t hto => ?_⟩
    · simp at hn
    · have hto' : (if kind = .call ∨ kind = .staticcall then call.address
          else evm.message.currentTarget) = L := hto
      refine ⟨?_, rfl, Nat.lt_of_le_of_lt (size_memoryReadBytes_le _ _ _) call.inputSize.isLt⟩
      show callee.code = CODE
      split at hto'
      · exact hc hH hto'
      · exact absurd hto' t

theorem res_callStep (so : StorageOnly L P) (hdel : delegatedAddress CODE = none)
    {kind : CallKind} {evm : Evm fork Nat} {result : StepResult fork Nat}
    (h : callStep kind evm = .ok result) :
    Res L CODE P (HoldsCode L CODE evm.state) evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  have c1 := qs_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : QS e1 e2 := by
    have := qs_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : QS evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (qs_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : QS evm e4 := s3.trans (qs_accessDelegation h4)
    have hc : HoldsCode L CODE evm.state → call.address = L → callee.code = CODE :=
      fun hold hL => code_accessDelegation hdel h4 (s3.kept.holdsCode hold) hL
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact Res.lift ((s4.trans (qs_payCall h5)).w so) (res_finishCall so hc h)
    · exact W.of_kept so s4.message s4.kept s4.dels
  · exact W.of_kept so s3.message s3.kept s3.dels

theorem res_launchCreate (so : StorageOnly L P) {evm : Evm fork Nat} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Nat}
    (h : launchCreate evm value initCode salt = .ok result) :
    Res L CODE P (HoldsCode L CODE evm.state) evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hs
    exact W.of_kept so q.message ((kept_recordAccountRead evm.state _).trans q.kept) q.dels
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 := (qs_accessAddress (recordAccountRead { evm with returnData := .empty }
    evm.message.currentTarget) address).trans (qs_recordAccountRead _ address)
  have k0 := (kept_recordAccountRead (L := L) evm.state evm.message.currentTarget).trans c0.kept
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : e2.message = evm.message := by
      rw [(chargeGas_sameContext h2).message, (chargeStateGas_sameContext h1).message]
      exact c0.message
    have k2 : Kept L evm.state e2.state := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state]
      exact k0
    have d2 : e2.substate.accountsToDelete = evm.substate.accountsToDelete := by
      rw [(chargeGas_sameContext h2).substate, (chargeStateGas_sameContext h1).substate]
      exact c0.dels
    have ks : Kept L evm.state state :=
      k2.trans (kept_incrementNonce (Base.mapError_ok_iff.mp hst))
    split at hr
    · rename_i hdep
      cases hr
      refine ⟨W.of_kept so m2 ks d2, fun hold => ?_, fun child after hres =>
        ⟨message_resumeCreate hres, state_resumeCreate hres, dels_resumeCreate hres⟩⟩
      have hne : address ≠ L := ne_of_deployable (k2.holdsCode hold) hdep
      exact ⟨fun _ => hne, fun _ hto => absurd hto hne⟩
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      refine W.of_kept so ?_ ?_ ?_
      · show e3.message = evm.message
        rw [(pushWord_sameContext h3).message]
        exact m2
      · show Kept L evm.state e3.state
        rw [(pushWord_sameContext h3).state]
        exact ks
      · show e3.substate.accountsToDelete = evm.substate.accountsToDelete
        rw [(pushWord_sameContext h3).substate]
        exact d2
  · exact W.of_kept so c0.message k0 c0.dels

theorem res_createStep (so : StorageOnly L P) {create2 : Bool} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (h : createStep create2 evm = .ok result) :
    Res L CODE P (HoldsCode L CODE evm.state) evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : e4.message = e3.message ∧ e4.state = e3.state ∧ e4.substate = e3.substate := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact ⟨(popWord_sameContext he).message, (popWord_sameContext he).state,
        (popWord_sameContext he).substate⟩
    · cases h4
      exact ⟨rfl, rfl, rfl⟩
  have m5 : e5.message = evm.message := by
    rw [(chargeGasAndMemory_sameContext h5).message, m4.1, (popWord_sameContext h3).message,
      (popWord_sameContext h2).message, (popWord_sameContext h1).message]
  have s5 : e5.state = evm.state := by
    rw [(chargeGasAndMemory_sameContext h5).state, m4.2.1, (popWord_sameContext h3).state,
      (popWord_sameContext h2).state, (popWord_sameContext h1).state]
  have d5 : e5.substate = evm.substate := by
    rw [(chargeGasAndMemory_sameContext h5).substate, m4.2.2, (popWord_sameContext h3).substate,
      (popWord_sameContext h2).substate, (popWord_sameContext h1).substate]
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact Res.lift (W.of_kept so m5 (by rw [s5]; exact Kept.refl _ _) (by rw [d5]))
    (Res.mono (fun hold => by rw [s5]; exact hold) (res_launchCreate so h))

theorem res_messageInstruction (so : StorageOnly L P) (hdel : delegatedAddress CODE = none)
    {op : Op} {run : Evm fork Nat → Except EvmError (StepResult fork Nat)} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : Res L CODE P (HoldsCode L CODE evm.state) evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Nat) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact res_callStep so hdel h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact res_callStep so hdel h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact res_createStep so h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact res_createStep so h
         · cases hrun)

/-- Every successful step of every frame, static or not, at every fork. -/
theorem res_step (so : StorageOnly L P) (hdel : delegatedAddress CODE = none)
    {evm : Evm fork Nat} {result : StepResult fork Nat} (h : step fork evm = .ok result) :
    Res L CODE P (HoldsCode L CODE evm.state) evm result := by
  unfold step at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Nat → Except EvmError (Evm fork Nat)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact w_instruction so hop hr
      · split at h
        · rename_i hcall
          exact res_messageInstruction so hdel hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    show W L CODE P evm _
    exact QS.w so (QS.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl))

end TokenKit.Seq

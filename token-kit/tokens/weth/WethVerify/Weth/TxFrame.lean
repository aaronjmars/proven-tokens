import TokenKit.Seq.Supply

/-!
# The ether of an account under every step of a frame at another address

GENERIC file: nothing here is about WETH. It is in this token folder because the kit library
(`TokenKit/Seq/`) is closed for this round; it is listed in `status.json` under
`to_merge_into_kit` ("invariant that reads the balance").

The kit `TokenKit.Seq` proves its results for an invariant that reads the storage of `L` only
(`StorageOnly`). An invariant such as "the sum of the balances is at most the ether of the
contract" also reads the ether of `L`. This file adds the missing fact, by the same walk over
EthLib's `step` as `TokenKit/Seq/Frame.lean` (the proofs are copies of the proofs there, with the
ether of `L` in place of its code and storage):

- `Up L S S'`: the ether of `L` in `S'` is at least its ether in `S`.
- `U L a b`: a step from the frame `a` to the frame `b` keeps the message; when the frame runs at
  another address than `L`, it does not lower the ether of `L`.
- `Paid L m`: a message whose move of value does not come from `L`, and that moves its value
  when it runs at `L`.
- `resU_step`: every successful step of every frame is a `U` step; a message that a frame at
  another address than `L` sends is `Paid`.

Why it holds: ether leaves an account only in the move of value of a message whose caller is the
account (CALL, CALLCODE, CREATE: the caller is the address of the frame), and in SELFDESTRUCT of
a frame at the account. DELEGATECALL moves no value.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WethVerify.Bal

open TokenKit
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open TokenKit.Seq

variable {fork : Fork} {L : Address}

/-! ## The ether of `L` under the changes of the state -/

/-- The ether of `L` in `S'` is at least its ether in `S`. -/
def Up (L : Address) (S S' : TransactionState) : Prop :=
  (S.getAccount L).balance.toNat ≤ (S'.getAccount L).balance.toNat

theorem Up.refl (L : Address) (S : TransactionState) : Up L S S := Nat.le_refl _

theorem Up.trans {a b c : TransactionState} (hab : Up L a b) (hbc : Up L b c) : Up L a c :=
  Nat.le_trans hab hbc

theorem up_of_eq {S S' : TransactionState} (h : S'.getAccount L = S.getAccount L) :
    Up L S S' := by
  unfold Up
  rw [h]
  exact Nat.le_refl _

theorem up_of_sameOutside {touched : List Address} {S S' : TransactionState}
    (so : TransactionState.SameOutside touched S S') (hL : L ∉ touched) : Up L S S' :=
  up_of_eq (getAccount_congr (so L hL).1)

theorem up_of_qs {a b : Evm fork Nat} (h : QS a b) : Up L a.state b.state :=
  up_of_sameOutside h.state (by simp)

theorem up_recordAccountRead (tx : TransactionState) (address : Address) :
    Up L tx (tx.recordAccountRead address) :=
  up_of_eq rfl

/-- A change of one account that does not lower its balance when the account is `L`. -/
theorem up_modifyState {tx tx' : TransactionState} {address : Address}
    {f : State.Account → Except State.StateError State.Account}
    (h : tx.modifyState fork address f = .ok tx')
    (hf : L = address → ∀ a b, f a = .ok b → a.balance.toNat ≤ b.balance.toNat) :
    Up L tx tx' := by
  obtain ⟨account, hfa, hget, hother⟩ := TransactionState.modifyState_eq_ok h
  by_cases hL : L = address
  · subst hL
    unfold Up
    rw [hget]
    exact hf rfl _ _ hfa
  · exact up_of_eq (hother L hL)

/-- A credit does not lower a balance. -/
theorem credit_up {address : Address} {amount : U256} {a b : State.Account}
    (h : State.Account.credit address amount a = .ok b) :
    a.balance.toNat ≤ b.balance.toNat := by
  unfold State.Account.credit at h
  split at h
  · rename_i hlt
    cases h
    have e : (a.balance + amount).toNat = a.balance.toNat + amount.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_eq_of_lt hlt
    show a.balance.toNat ≤ (a.balance + amount).toNat
    omega
  · cases h

/-- A move of ether from another address than `L`. -/
theorem up_moveEther {tx tx' : TransactionState} {sender recipient : Address} {amount : U256}
    (h : tx.moveEther fork sender recipient amount = .ok tx') (hne : sender ≠ L) :
    Up L tx tx' := by
  unfold TransactionState.moveEther at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (up_modifyState h1 (fun e => absurd e.symm hne)).trans
    (up_modifyState h2 (fun _ a b hab => credit_up hab))

theorem up_createEther {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.createEther fork address amount = .ok tx') : Up L tx tx' := by
  unfold TransactionState.createEther at h
  exact up_modifyState h (fun _ a b hab => credit_up hab)

theorem up_setAccountBalance {tx tx' : TransactionState} {address : Address} {amount : U256}
    (h : tx.setAccountBalance fork address amount = .ok tx') (hne : address ≠ L) :
    Up L tx tx' := by
  unfold TransactionState.setAccountBalance at h
  exact up_modifyState h (fun e => absurd e.symm hne)

theorem up_incrementNonce {tx tx' : TransactionState} {address : Address}
    (h : tx.incrementNonce fork address = .ok tx') : Up L tx tx' := by
  unfold TransactionState.incrementNonce at h
  refine up_modifyState h ?_
  intro _ a b hab
  cases hab
  exact Nat.le_refl _

/-- SELFDESTRUCT of a frame at another address than `L`. -/
theorem up_selfdestructTransfer {tx tx' : TransactionState} {originator beneficiary : Address}
    (h : selfdestructTransfer fork tx originator beneficiary = .ok tx') (hne : originator ≠ L) :
    Up L tx tx' := by
  unfold selfdestructTransfer at h
  split at h
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    split at h
    · exact (up_moveEther h1 hne).trans (up_setAccountBalance h hne)
    · cases h
      exact up_moveEther h1 hne
  · obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
    exact (up_createEther h1).trans (up_setAccountBalance h hne)

/-- A storage write changes no account. -/
theorem up_setStorage {tx tx' : TransactionState} {address : Address} {key : Bytes32}
    {value : U256} (h : tx.setStorage address key value = .ok tx') : Up L tx tx' :=
  up_of_eq (getAccount_congr (TransactionState.getAccountOptional_setStorage h))

theorem up_touchAccount (tx : TransactionState) (address : Address) :
    Up L tx (tx.touchAccount address) := by
  by_cases hL : L = address
  · subst hL
    exact up_of_eq (TransactionState.getAccount_touchAccount_self tx L)
  · exact up_of_eq (TransactionState.getAccount_touchAccount hL)

theorem up_startState (message : Message fork) (state : TransactionState) :
    Up L state (startState fork message state) := by
  unfold startState
  split
  · exact up_touchAccount _ _
  · exact Up.refl _ _

theorem up_prepareCreation {tx tx' : TransactionState} {address : Address}
    (h : prepareCreation fork tx address = .ok tx') : Up L tx tx' := by
  have u0 : Up L tx ((tx.destroyStorage address).markAccountCreated address) := up_of_eq rfl
  unfold prepareCreation at h
  split at h
  · exact u0.trans (up_incrementNonce (Base.mapError_ok_iff.mp h))
  · cases h
    exact u0

/-- A rollback to a snapshot of the same block has the ether of the snapshot. -/
theorem up_restore {tx snapshot : TransactionState} (hp : tx.parent = snapshot.parent) :
    Up L snapshot (tx.restoreTxState snapshot) :=
  up_of_eq (getAccount_congr (TransactionState.getAccountOptional_restoreTxState hp L))

/-- A deposit of code at another address. -/
theorem up_setCode {tx tx' : TransactionState} {address : Address} {code : ByteArray}
    (h : tx.setCode fork address code = .ok tx') (hne : L ≠ address) : Up L tx tx' :=
  up_of_eq (getAccount_congr ((TransactionState.getAccount_setCode h).2 L hne))

/-! ## One step of a frame -/

/-- A step from the frame `a` to the frame `b` that keeps the message. In a frame at another
address than `L` it does not lower the ether of `L`. -/
structure U (L : Address) (a b : Evm fork Nat) : Prop where
  message : b.message = a.message
  up : a.message.currentTarget ≠ L → Up L a.state b.state

theorem U.refl (a : Evm fork Nat) : U L a a := ⟨rfl, fun _ => Up.refl _ _⟩

theorem U.trans {a b c : Evm fork Nat} (hab : U L a b) (hbc : U L b c) : U L a c :=
  ⟨hbc.message.trans hab.message,
    fun t => (hab.up t).trans (hbc.up (by rw [hab.message]; exact t))⟩

theorem U.of_up {a b : Evm fork Nat} (m : b.message = a.message) (u : Up L a.state b.state) :
    U L a b :=
  ⟨m, fun _ => u⟩

theorem u_of_qs {a b : Evm fork Nat} (h : QS a b) : U L a b := U.of_up h.message (up_of_qs h :)

/-- SSTORE changes no account. -/
theorem u_sstoreStep {evm after : Evm fork Nat} (h : sstoreStep evm = .ok after) :
    U L evm after := by
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
      have u5 : Up L evm.state e5.state := by
        rw [(chargeStateGas_sameContext h5).state, (chargeGas_sameContext h4).state]
        exact up_of_qs c3
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
        cases h
        have hset := Base.mapError_ok_iff.mp hst
        exact U.of_up m5 (u5.trans (up_setStorage hset))
    · exact U.of_up c3.message (up_of_qs c3 :)

/-- TSTORE changes no account. -/
theorem u_tstoreStep {evm after : Evm fork Nat} (h : tstoreStep evm = .ok after) :
    U L evm after := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  have c3 : QS evm e3 := ((QS.of_sameContext (popWord_sameContext h1)).trans
    (QS.of_sameContext (popWord_sameContext h2))).trans
    (QS.of_sameContext (chargeGas_sameContext h3))
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    exact U.of_up c3.message ((up_of_qs c3 :).trans (up_of_eq rfl))

/-- SELFDESTRUCT of a frame at another address than `L` does not lower the ether of `L`. -/
theorem u_selfdestructStep {evm after : Evm fork Nat}
    (h : selfdestructStep fork evm = .ok after) : U L evm after := by
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
    have u4 : Up L evm.state e4.state := by
      rw [(chargeStateGas_sameContext h4).state, (chargeGas_sameContext h3).state]
      exact up_of_qs c
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
      cases h
      refine ⟨m4, fun t => u4.trans (up_selfdestructTransfer (Base.mapError_ok_iff.mp hst) ?_)⟩
      rw [m4]
      exact t
  · exact U.of_up c.message (up_of_qs c :)

/-- Each instruction that gives the next frame is a `U` step. -/
theorem u_instruction {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {evm after : Evm fork Nat}
    (hrun : instruction fork op = some run) (h : run evm = .ok after) :
    U L evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (QS.of_sameContext (stackOnlyStep_sameContext hf h))
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (QS.of_sameContext (controlFlowStep_sameContext hf h))
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (QS.of_sameContext (memoryDataStep_sameContext hf h))
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (qs_returnOpStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (QS.of_sameContext (environmentStep_sameContext hf h))
  rcases orElse_eq_some hrun with hf | hrun
  · exact u_of_qs (qs_accountStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact u_of_qs (qs_sloadStep h)
    case sstore => subst hf; exact u_sstoreStep h
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    · exact u_of_qs (QS.of_sameContext (tloadStep_sameContext h))
    · exact u_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, -, -, hm, hs, hsub⟩ := logStep_eq_ok h
    exact U.of_up hm (by rw [hs]; exact Up.refl _ _)
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact u_selfdestructStep h

/-! ## The calls and the creations -/

/-- A message whose move of value does not come from `L`, and that moves its value when it runs
at `L`. Every message that a frame at another address than `L` sends is of this kind. -/
def Paid (L : Address) (m : Message fork) : Prop :=
  (m.shouldTransferValue = true → m.caller ≠ L) ∧
    (m.currentTarget = L → m.shouldTransferValue = true)

/-- A result of a step from `evm`: the next frame, or the frame that sends a message, is a `U`
step from `evm`; a message that a frame at another address than `L` sends is `Paid`. -/
def ResU (L : Address) (evm : Evm fork Nat) : StepResult fork Nat → Prop
  | .next after => U L evm after
  | .child caller message _ => U L evm caller ∧ (evm.message.currentTarget ≠ L → Paid L message)

theorem ResU.lift {evm evm' : Evm fork Nat} {result : StepResult fork Nat}
    (h : U L evm evm') (r : ResU L evm' result) : ResU L evm result := by
  cases result with
  | next after => exact h.trans (r : U L evm' after)
  | child caller message resume =>
    obtain ⟨c, s⟩ := r
    exact ⟨h.trans c, fun t => s (by rw [h.message]; exact t)⟩

theorem resU_genericCall {evm : Evm fork Nat}
    {message : Message fork} {newAccount : Nat} {outputStart outputSize : U256}
    {result : StepResult fork Nat}
    (hs : evm.message.currentTarget ≠ L → Paid L message)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    ResU L evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · obtain ⟨after, hsk, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hsk
    exact U.of_up q.message (up_of_qs q :)
  · cases h
    exact ⟨U.of_up rfl (Up.refl _ _), hs⟩

theorem resU_finishCall {kind : CallKind}
    {call : CallOperands} {callee : Callee} {subCall newAccount expandBy : Nat}
    {evm : Evm fork Nat} {result : StepResult fork Nat}
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    ResU L evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  split at h
  · obtain ⟨after, hsk, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hsk
    exact U.of_up q.message ((up_recordAccountRead evm.state _).trans (up_of_qs q :))
  · refine ResU.lift (evm' := recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget)
      (U.of_up rfl (up_recordAccountRead evm.state _)) (resU_genericCall ?_ h)
    intro t
    have t' : evm.message.currentTarget ≠ L := t
    constructor
    · intro hstv
      have hstv' : (kind != CallKind.delegatecall) = true := hstv
      have hk : ¬ kind = CallKind.delegatecall := by
        intro e
        subst e
        exact absurd hstv' (by decide)
      show (if kind = CallKind.delegatecall then evm.message.caller
        else evm.message.currentTarget) ≠ L
      rw [if_neg hk]
      exact t'
    · intro hto
      have hto' : (if kind = .call ∨ kind = .staticcall then call.address
          else evm.message.currentTarget) = L := hto
      show (kind != CallKind.delegatecall) = true
      cases kind <;> first
        | decide
        | (rw [if_neg (by decide)] at hto'; exact absurd hto' t')

theorem resU_callStep {kind : CallKind} {evm : Evm fork Nat} {result : StepResult fork Nat}
    (h : callStep kind evm = .ok result) : ResU L evm result := by
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
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      exact ResU.lift (u_of_qs (s4.trans (qs_payCall h5))) (resU_finishCall h)
    · exact U.of_up s4.message (up_of_qs s4 :)
  · exact U.of_up s3.message (up_of_qs s3 :)

theorem resU_launchCreate {evm : Evm fork Nat} {value : U256}
    {initCode : ByteArray} {salt : Option U256} {result : StepResult fork Nat}
    (h : launchCreate evm value initCode salt = .ok result) : ResU L evm result := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · obtain ⟨after, hs, rfl⟩ := Base.map_ok_iff.mp h
    have q := qs_skipCall hs
    exact U.of_up q.message ((up_recordAccountRead evm.state _).trans (up_of_qs q :))
  obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
  have c0 := (qs_accessAddress (recordAccountRead { evm with returnData := .empty }
    evm.message.currentTarget) address).trans (qs_recordAccountRead _ address)
  have u0 := (up_recordAccountRead (L := L) evm.state evm.message.currentTarget).trans
    (up_of_qs c0 :)
  rcases keepReads_eq_ok h with hr | ⟨e, rfl⟩
  · obtain ⟨e1, h1, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨e2, h2, hr⟩ := Base.bind_ok_iff.mp hr
    obtain ⟨state, hst, hr⟩ := Base.bind_ok_iff.mp hr
    have m2 : e2.message = evm.message := by
      rw [(chargeGas_sameContext h2).message, (chargeStateGas_sameContext h1).message]
      exact c0.message
    have u2 : Up L evm.state e2.state := by
      rw [(chargeGas_sameContext h2).state, (chargeStateGas_sameContext h1).state]
      exact u0
    have us : Up L evm.state state :=
      u2.trans (up_incrementNonce (Base.mapError_ok_iff.mp hst))
    split at hr
    · cases hr
      refine ⟨U.of_up m2 us, fun t => ⟨fun _ => ?_, fun _ => rfl⟩⟩
      exact t
    · obtain ⟨e3, h3, hr⟩ := Base.bind_ok_iff.mp hr
      cases hr
      refine U.of_up ?_ ?_
      · show e3.message = evm.message
        rw [(pushWord_sameContext h3).message]
        exact m2
      · show Up L evm.state e3.state
        rw [(pushWord_sameContext h3).state]
        exact us
  · exact U.of_up c0.message u0

theorem resU_createStep {create2 : Bool} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (h : createStep create2 evm = .ok result) :
    ResU L evm result := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨salt, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have m4 : e4.message = e3.message ∧ e4.state = e3.state := by
    unfold popSalt at h4
    split at h4
    · obtain ⟨⟨_, e⟩, he, h4⟩ := Base.bind_ok_iff.mp h4
      cases h4
      exact ⟨(popWord_sameContext he).message, (popWord_sameContext he).state⟩
    · cases h4
      exact ⟨rfl, rfl⟩
  have m5 : e5.message = evm.message := by
    rw [(chargeGasAndMemory_sameContext h5).message, m4.1, (popWord_sameContext h3).message,
      (popWord_sameContext h2).message, (popWord_sameContext h1).message]
  have s5 : e5.state = evm.state := by
    rw [(chargeGasAndMemory_sameContext h5).state, m4.2, (popWord_sameContext h3).state,
      (popWord_sameContext h2).state, (popWord_sameContext h1).state]
  unfold genericCreate at h
  split at h
  · cases h
  split at h
  · cases h
  exact ResU.lift (U.of_up m5 (by rw [s5]; exact Up.refl _ _)) (resU_launchCreate h)

theorem resU_messageInstruction
    {op : Op} {run : Evm fork Nat → Except EvmError (StepResult fork Nat)} {evm : Evm fork Nat}
    {result : StepResult fork Nat} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) : ResU L evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Nat) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact resU_callStep h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact resU_callStep h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact resU_createStep h)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact resU_createStep h
         · cases hrun)

/-- Every successful step of every frame, static or not, at every fork: in a frame at another
address than `L` it does not lower the ether of `L`, and the message that it sends, if any, does
not move value out of `L`. -/
theorem resU_step {evm : Evm fork Nat} {result : StepResult fork Nat}
    (h : step fork evm = .ok result) : ResU L evm result := by
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
          exact u_instruction hop hr
      · split at h
        · rename_i hcall
          exact resU_messageInstruction hcall h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    show U L evm _
    exact u_of_qs (QS.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl))

end WethVerify.Bal

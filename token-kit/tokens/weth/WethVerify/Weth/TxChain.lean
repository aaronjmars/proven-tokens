import WethVerify.Weth.TxRun

/-!
# Whole transactions, for an invariant that reads the storage and the ether of `L`

GENERIC file: nothing here is about WETH (see the note at the top of `TxFrame.lean`; listed in
`status.json` under `to_merge_into_kit`).

`TokenKit/Seq/Tx.lean` lifts `processMessage_good_local` to EthLib's `processTransaction` and to
any finite list of transactions, for an invariant with `StorageOnly`. This file does the same
for an invariant with `Mono` (it may read the ether of `L`; more ether does not break it), on
top of `TxRun.lean`. The proofs follow the proofs of the kit step by step; the facts on the code
of `L` are taken from the kit (used with the invariant `True`).

One more hypothesis than the kit, per transaction: the sender is not `L` (`sender ≠ L`). The
sender pays the gas and the value, so its ether goes down. On a chain it always holds: `L` has
code, and a transaction whose sender has code is rejected (EIP-3607). That rule is checked
before `processTransaction` and is NOT proved here, so it stays a named hypothesis.

- `runTransaction_good_bal`, `processTransaction_good_bal`: one whole transaction keeps `L`
  good. From Dencun, before Glamsterdam.
- `ChainV`, `chain_good_bal`: any finite list of transactions.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WethVerify.Bal

open TokenKit
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState BlockState EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Transactions
open TokenKit.Seq

variable {fork : Fork} {L : Address} {CODE : ByteArray} {P : State.TransactionState → Prop}
  {Q : Message fork → TransactionState → Prop}

/-! ## Deletions at the end of a transaction -/

theorem up_destroyAccount (tx : TransactionState) {address : Address} (hne : L ≠ address) :
    Up L tx (tx.destroyAccount address) :=
  up_of_sameOutside (TransactionState.sameOutside_destroyAccount tx address) (by simpa using hne)

theorem up_destroyTouched {tx : TransactionState} (touched : List Address)
    (hold : HoldsCode L CODE tx) :
    Up L tx (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact Up.refl _ _
  · suffices hs : ∀ (l : List Address) (acc : TransactionState), HoldsCode L CODE acc →
        Up L acc (l.foldl (fun tx address =>
          if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) acc) from
      hs touched tx hold
    intro l
    induction l with
    | nil => intro acc _; exact Up.refl _ _
    | cons a l ih =>
      intro acc hacc
      rw [List.foldl_cons]
      have k1 : Kept L acc
            (if acc.accountExistsAndIsEmpty a then acc.destroyAccount a else acc) ∧
          Up L acc (if acc.accountExistsAndIsEmpty a then acc.destroyAccount a else acc) := by
        split
        · rename_i he
          by_cases hL : L = a
          · subst hL
            exact absurd he (fun he => not_empty_of_holds hacc he)
          · exact ⟨kept_destroyAccount acc hL, up_destroyAccount acc hL⟩
        · exact ⟨Kept.refl _ _, Up.refl _ _⟩
      exact k1.2.trans (ih _ (k1.1.holdsCode hacc))

theorem up_foldlM_destroy (hlt : fork < .glamsterdam) :
    ∀ (l : List Address) (S S' : TransactionState), (∀ a ∈ l, a ≠ L) →
      l.foldlM (fun (state : TransactionState) address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else (pure (state.destroyAccount address) : Except State.StateError TransactionState))
        S = .ok S' → Up L S S' := by
  have hge : ¬ fork ≥ .glamsterdam := Nat.not_le.mpr hlt
  intro l
  induction l with
  | nil =>
    intro S S' _ h
    cases h
    exact Up.refl _ _
  | cons a l ih =>
    intro S S' hall h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
    rw [if_neg hge] at h1
    cases h1
    exact (up_destroyAccount S (fun e => hall a List.mem_cons_self e.symm)).trans
      (ih _ _ (fun b hb => hall b (List.mem_cons_of_mem _ hb)) h2)

theorem up_deleteAccounts (hlt : fork < .glamsterdam) {state state' : TransactionState}
    {output : CallOutput} (hold : HoldsCode L CODE state) (hd : L ∉ output.accountsToDelete)
    (h : deleteAccounts fork state output = .ok state') : Up L state state' := by
  unfold deleteAccounts at h
  obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h1
  have k1 : Kept L state mid := kept_foldlM_destroy hlt _ _ _
    (fun a ha e => hd (e ▸ Std.ExtTreeSet.mem_toList.mp ha)) h1
  have u1 : Up L state mid := up_foldlM_destroy hlt _ _ _
    (fun a ha e => hd (e ▸ Std.ExtTreeSet.mem_toList.mp ha)) h1
  exact u1.trans (up_destroyTouched _ (k1.holdsCode hold))

/-! ## The gas of a transaction -/

/-- The sender buys the gas: when the sender is not `L`, the ether of `L` is not lowered. -/
theorem up_buyGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} (h : buyGas env state sender tx = .ok state')
    (hne : sender ≠ L) : Up L state state' := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  exact (up_incrementNonce h1).trans (up_modifyState h2 (fun e => absurd e.symm hne))

theorem up_creditEther {state state' : TransactionState} {address : Address} {amount : Nat}
    (h : creditEther fork state address amount = .ok state') : Up L state state' := by
  unfold creditEther at h
  split at h
  · exact up_createEther h
  · cases h

theorem up_payBeneficiary {state state' : TransactionState} {coinbase : Address} {fee : Nat}
    (hold : HoldsCode L CODE state) (h : payBeneficiary fork state coinbase fee = .ok state') :
    Up L state state' := by
  unfold payBeneficiary at h
  split at h
  · cases h
    split
    · rename_i he
      by_cases hL : L = coinbase
      · subst hL
        exact absurd he (fun he => not_empty_of_holds hold he)
      · exact up_destroyAccount state hL
    · exact Up.refl _ _
  · exact up_creditEther h

theorem up_settleGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refund used : Nat}
    (hold : HoldsCode L CODE state)
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) :
    Up L state state' := by
  unfold settleGas at h
  obtain ⟨s1, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have k1 : Kept L state s1 := kept_creditEther h1
  exact (up_creditEther h1).trans (up_payBeneficiary (k1.holdsCode hold) h2)

/-! ## The authorizations of EIP-7702 and the first frame -/

/-- The authorizations of a transaction keep the account of `L`, which holds real code. -/
theorem auths_account (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {chainId : Nat} {state : TransactionState} {accessed paid : Std.ExtTreeSet Address}
    {meter : Nat} {auths : List Authorization} {done : Delegations Nat}
    (hold : HoldsCode L CODE state)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
    (h : applyAuthorizations fork chainId state accessed meter paid auths = .ok done) :
    done.state.getAccount L = state.getAccount L := by
  unfold applyAuthorizations at h
  have hne : ∀ auth ∈ auths, Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ≠
      (state.getAccount L).codeHash := by
    intro auth ha e
    rw [hold.2.2] at e
    exact delegationCode_ne hsize hind auth (hh auth ha e)
  obtain ⟨ha, -, -, -⟩ := foldlM_applyAuthorization_keeps hsize hind h hold.1 hne
  exact getAccount_congr ha

/-- The preparation of the first frame does not lower the ether of `L`, and keeps the caller of
the message and whether it moves its value. -/
theorem prepareFirstFrame_up (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Nat}
    (hold : HoldsCode L CODE state)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
    (h : prepareFirstFrame (Meter := Nat) chainId message state substate auths paid =
      .ok first) :
    Up L state first.state ∧ first.message.caller = message.caller ∧
      first.message.shouldTransferValue = message.shouldTransferValue := by
  unfold prepareFirstFrame at h
  dsimp only at h
  split at h
  · rename_i htgt
    split at h
    · rename_i hd
      split at h
      all_goals
        obtain ⟨m, hm, h⟩ := Base.bind_ok_iff.mp h
        cases h
        exact ⟨up_recordAccountRead _ _, rfl, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := Base.bind_ok_iff.mp h
    have u0 : Up L state done.state := up_of_eq (auths_account hsize hind hold hh hdone)
    have key : ∀ (S' : TransactionState) (code : ByteArray),
        (S'.recordAccountRead target).getCode
          ((S'.recordAccountRead target).getAccount target).codeHash = .ok code →
        (S' = done.state.recordAccountRead target ∨ S' = done.state) →
        Up L done.state (S'.recordAccountRead target) := by
      rintro S' code - (rfl | rfl)
      · exact (up_recordAccountRead _ _).trans (up_recordAccountRead _ _)
      · exact up_recordAccountRead _ _
    split at h
    all_goals split at h
    all_goals
      obtain ⟨m, hm, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨code, hcode, h⟩ := Base.bind_ok_iff.mp h
      have hg := Base.mapError_ok_iff.mp hcode
      have K := key _ _ hg (by first | exact Or.inl rfl | exact Or.inr rfl)
      cases heq : (if fork ≥ Fork.pectra then delegatedAddress code else none) with
      | some delegate =>
        simp only [heq] at h
        have K2 := K.trans (up_recordAccountRead _ delegate)
        split at h
        all_goals
          obtain ⟨m2, hm2, h⟩ := Base.bind_ok_iff.mp h
          obtain ⟨code2, hcode2, h⟩ := Base.bind_ok_iff.mp h
          cases h
          exact ⟨u0.trans K2, rfl, rfl⟩
      | none =>
        simp only [heq] at h
        cases h
        exact ⟨u0.trans K, rfl, rfl⟩

/-! ## The message of a transaction -/

/-- The message of a transaction keeps a good state good and leaves `L` out of the accounts to
delete, when it moves its value from another address than `L`. From Dencun. -/
theorem processMessageCall_good_bal (mono : Mono L P)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false) (hden : Fork.dencun ≤ fork)
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (fk : FrameKeepsV fork L CODE P Q)
    (g : Good L CODE P state) (hc : L ∉ state.createdAccounts)
    (hd : L ∉ substate.accountsToDelete)
    (hcur : ∀ t, message.target = some t → message.currentTarget = t)
    (hdata : message.target = some L → message.data.size < 2 ^ 256)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
    (hpaid : message.shouldTransferValue = true ∧ message.caller ≠ L)
    (clean : ∀ first,
      prepareFirstFrame (Meter := Nat) chainId message state substate auths paid = .ok first →
      (first.message.target.isSome = true →
        Clean L CODE Q first.message first.state first.substate first.meter) ∧
      (first.message.target = none →
        CleanCreate L CODE Q first.message first.state first.substate first.meter))
    (h : processMessageCall (Meter := Nat) chainId message state substate auths paid =
      .ok output) :
    Good L CODE P output.state ∧ L ∉ output.accountsToDelete := by
  have hdel : delegatedAddress CODE = none := by simp [delegatedAddress, hind]
  have kit := processMessageCall_good (P := fun _ => True) (Q := Q) storageOnly_true hsize hind
    hden (fun first _ => frameKeepsR_true first.message.gas) ⟨g.1, trivial⟩ hc hd hcur hdata hh
    clean h
  refine ⟨⟨kit.1.1, ?_⟩, kit.2⟩
  unfold processMessageCall at h
  split at h
  · rename_i e read hprep
    split at h
    · cases h
    · cases h
      exact mono _ _
        (fun k => (TransactionState.sameOutside_withReadsOf state read L (by simp)).2.1 k)
        (up_of_sameOutside (TransactionState.sameOutside_withReadsOf state read) (by simp)) g.2
  · rename_i first hprep
    obtain ⟨hold1, hst1, hcr1, hdl1, htg1, hct1, hda1, hne1, hcode1⟩ :=
      prepareFirstFrame_facts hsize hind g.1 hh hprep
    obtain ⟨hu1, hca1, hsv1⟩ := prepareFirstFrame_up hsize hind g.1 hh hprep
    have g1 : Good L CODE P first.state := ⟨hold1, mono state first.state hst1 hu1 g.2⟩
    have hstv : first.message.shouldTransferValue = true := by rw [hsv1]; exact hpaid.1
    have hcal : first.message.caller ≠ L := by rw [hca1]; exact hpaid.2
    split at h
    · rename_i htgt
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have hne : first.message.currentTarget ≠ L := by rw [hct1]; exact hne1 htgt
      have cl := (clean first hprep).2 (by rw [htg1]; exact htgt)
      have gE := processCreateMessage_good_bal mono fk hdel hne (fun _ => hcal) g1 cl hrun
      rw [ofFrame_state]
      exact gE.2
    · rename_i target htgt
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have sane : Sane L CODE first.message := by
        intro ht
        have ht' : message.currentTarget = L := by rw [← hct1]; exact ht
        have htl : message.target = some L := by rw [htgt, ← hcur _ htgt, ht']
        exact ⟨hcode1 htl, by rw [htg1, htgt]; rfl, by rw [hda1]; exact hdata htl⟩
      have cl := (clean first hprep).1 (by rw [htg1, htgt]; rfl)
      have gE := processMessage_good_bal mono fk hdel sane ⟨fun _ => hcal, fun _ => hstv⟩ g1 cl
        hrun
      rw [ofFrame_state]
      exact gE.2

/-! ## A whole transaction -/

/-- The message of a transaction: the sender is its caller, and it moves its value. -/
theorem transactionMessage_paid {env : BlockEnvironment fork}
    {txEnv : TransactionEnvironment fork} {state : TransactionState} {sender target : Address}
    {gas : Nat} {tx : Transaction} {message : Message fork}
    (h : transactionMessage env txEnv state sender target gas tx = .ok message) :
    message.caller = sender ∧ message.shouldTransferValue = true := by
  unfold transactionMessage at h
  dsimp only at h
  split at h
  · obtain ⟨code, -, rfl⟩ := Base.map_ok_iff.mp h
    exact ⟨rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl⟩

/-- The block state after a transaction is good when the state of the transaction is. -/
theorem good_incorporate_bal (mono : Mono L P) {S : TransactionState}
    (g : Good L CODE P S) :
    Good L CODE P (TransactionState.ofBlock S.incorporateTxIntoBlock.parent) := by
  have e : TransactionState.ofBlock S.incorporateTxIntoBlock.parent =
      S.incorporateTxIntoBlock := rfl
  rw [e]
  exact ⟨holdsCode_of_eq
      (getAccount_congr (TransactionState.getAccountOptional_incorporateTxIntoBlock S L))
      (funext (TransactionState.getCode_incorporateTxIntoBlock S)) g.1,
    mono _ _ (fun k => TransactionState.getStorage_incorporateTxIntoBlock S L k)
      (up_of_eq
        (getAccount_congr (TransactionState.getAccountOptional_incorporateTxIntoBlock S L)))
      g.2⟩

/-- A whole transaction, as EthLib's `runTransaction Nat` runs it, keeps `L` good: from the
block state before it to the block state after it. With or without an error of its message,
whatever it calls, at any depth. The sender is not `L`. From Dencun, before Glamsterdam. -/
theorem runTransaction_good_bal (mono : Mono L P)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (fk : FrameKeepsV fork L CODE P Q)
    (hsender : included.sender ≠ L)
    (clean : TxClean L CODE Q env block included tx)
    (h : runTransaction Nat env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) := by
  unfold runTransaction at h
  obtain ⟨target, hTarget, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bought, hBought, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨message, hMessage, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨output, hOutput, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨settled, used⟩, hSettle, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨deleted, hDeleted, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hBought' := Base.mapError_ok_iff.mp hBought
  have hSettle' := Base.mapError_ok_iff.mp hSettle
  have hDeleted' := Base.mapError_ok_iff.mp hDeleted
  have kb : Kept L (TransactionState.ofBlock block) bought := kept_buyGas hBought'
  have gb : Good L CODE P bought :=
    ⟨kb.holdsCode g.1, mono _ _ (kb.storage g.1.2.1) (up_buyGas hBought' hsender) g.2⟩
  have hcb : L ∉ bought.createdAccounts := fun x =>
    absurd (kb.created x) Std.ExtTreeSet.not_mem_empty
  obtain ⟨mt, mc, md⟩ := transactionMessage_facts hTarget hMessage
  obtain ⟨mcal, mstv⟩ := transactionMessage_paid hMessage
  obtain ⟨gO, hdO⟩ := processMessageCall_good_bal
    (message := { message with
      reservoir := (allocateGas fork tx included.intrinsicGas).reservoir })
    mono hsize hind hden fk gb hcb
    (Std.ExtTreeSet.not_mem_empty)
    (fun t e => by
      have e' : message.target = some t := e
      rw [mt] at e'
      exact mc.trans (md t e').1)
    (fun e => by
      have e' : message.target = some L := e
      rw [mt] at e'
      have hd : message.data = tx.data := (md L e').2
      show message.data.size < 2 ^ 256
      rw [hd]
      exact clean.data e')
    clean.auths
    ⟨mstv, fun e => hsender (mcal.symm.trans e)⟩
    (fun first hp =>
      ⟨clean.call first ⟨target, bought, message, hTarget, hBought', hMessage, hp⟩,
        clean.create first ⟨target, bought, message, hTarget, hBought', hMessage, hp⟩⟩)
    hOutput
  have ks : Kept L output.state settled := kept_settleGas gO.1 hSettle'
  have us : Up L output.state settled := up_settleGas gO.1 hSettle'
  have hs : HoldsCode L CODE settled := ks.holdsCode gO.1
  have kd : Kept L settled deleted := kept_deleteAccounts hlt hs hdO hDeleted'
  have ud : Up L settled deleted := up_deleteAccounts hlt hs hdO hDeleted'
  have gD : Good L CODE P deleted :=
    ⟨kd.holdsCode hs, mono _ _ (kd.storage hs.2.1) ud
      (mono _ _ (ks.storage gO.1.2.1) us gO.2)⟩
  exact good_incorporate_bal mono gD

/-- The same for EthLib's `processTransaction`. From Dencun, before Glamsterdam (where
`processTransaction` is `runTransaction Nat`). -/
theorem processTransaction_good_bal (mono : Mono L P)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (fk : FrameKeepsV fork L CODE P Q)
    (hsender : included.sender ≠ L)
    (clean : TxClean L CODE Q env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) := by
  rw [processTransaction_of_lt_glamsterdam hlt] at h
  exact runTransaction_good_bal mono hsize hind hden hlt fk hsender clean h g

/-! ## Any finite list of transactions -/

/-- A finite list of transactions that takes the block state `b` to the block state `b'`.

As `TokenKit.Seq.Chain`, with one more hypothesis per transaction: its sender is not `L`. Each
one is run by EthLib's `processTransaction`, at its own fork (from Dencun, before Glamsterdam),
in its own block environment, on the block state that the one before left, and satisfies the
run-local hypotheses `TxClean`. `Qf fork` is the hypothesis `Q` at that fork. -/
inductive ChainV (L : Address) (CODE : ByteArray)
    (Qf : (fork : Fork) → Message fork → TransactionState → Prop) :
    BlockState → BlockState → Prop
  /-- No transaction. -/
  | nil (b : BlockState) : ChainV L CODE Qf b b
  /-- One transaction, then the rest of the list. -/
  | cons {fork : Fork} {env : BlockEnvironment fork} {b b' : BlockState} {included : Included}
      {tx : Transaction} {out : TransactionOutput} :
      Fork.dencun ≤ fork → fork < .glamsterdam →
      processTransaction env b included tx = .ok out →
      included.sender ≠ L →
      TxClean L CODE (Qf fork) env b included tx →
      ChainV L CODE Qf out.block b' → ChainV L CODE Qf b b'

/-- Any finite list of transactions keeps `L` good: it holds `CODE` and `P` holds, after the
last one as before the first one. -/
theorem chain_good_bal {Qf : (fork : Fork) → Message fork → TransactionState → Prop}
    (mono : Mono L P)
    (fk : ∀ fork, Fork.dencun ≤ fork → fork < .glamsterdam →
      FrameKeepsV fork L CODE P (Qf fork))
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {b b' : BlockState} (chain : ChainV L CODE Qf b b')
    (g : Good L CODE P (TransactionState.ofBlock b)) :
    Good L CODE P (TransactionState.ofBlock b') := by
  induction chain with
  | nil => exact g
  | cons hden hlt hrun hsender clean _ ih =>
    exact ih (processTransaction_good_bal mono hsize hind hden hlt (fk _ hden hlt) hsender clean
      hrun g)

end WethVerify.Bal

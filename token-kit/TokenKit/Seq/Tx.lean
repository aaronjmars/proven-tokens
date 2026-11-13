import TokenKit.Seq.Run
import EthLib.Execution.Proofs.Transactions.Process
import EthLib.Execution.Proofs.Transactions.Authorization

/-!
# A contract stays good through a whole transaction, and through any finite list of them

GENERIC kit file: nothing here is about one token. It links the message-level results of
`TokenKit/Seq/Run.lean` to the transaction that EthLib really runs.

`L` is the address of a contract, `CODE` its code, `P` an invariant of its storage,
`Good L CODE P S`: in the state `S`, `L` holds `CODE` and `P` holds.

## Results

- `processMessageCall_good`: the message of a transaction (`processMessageCall`: EIP-7702
  authorizations, the first frame, then `processMessage` or `processCreateMessage`) keeps a good
  state good, and leaves `L` out of the accounts to delete.
- `runTransaction_good`: EthLib's `runTransaction Nat` (buy the gas, the message, settle the gas,
  delete the accounts) takes a block state where `L` is good to a block state where `L` is good.
- `processTransaction_good`: the same for `processTransaction`, which is `runTransaction Nat`
  before Glamsterdam.
- `Chain`, `chain_good`: any finite list of transactions, each run by `processTransaction` at
  its own fork on the block state that the one before left, keeps `L` good. Whoever sends them,
  whatever they call, at any depth, with or without an error.
- `runTransaction_good_at`: the core form (the interface of the token at the gas of the first
  frame of the transaction). `GasCap`, `runTransaction_good_cap`, `processTransaction_good_cap`,
  `ChainCap`, `chainCap_good`: the same results for a token whose interface holds under a cap `G`
  on gas only (a token that makes a real outside call), with the run-local hypothesis `GasCap`:
  the first frame of each transaction has at most `G` gas.
- `good_of_zero`: the base case shape. A token proves `ZeroBase L P` (all-zero storage satisfies
  `P`).

## Fork range, stated honestly

`Fork.dencun ≤ fork` and `fork < Fork.glamsterdam`.

- From Dencun: by EIP-6780 SELFDESTRUCT only deletes an account created in the same transaction,
  so the end of the transaction cannot delete `L`. Before Dencun a token would also have to show
  that `CODE` never runs SELFDESTRUCT at `L` (not done here; the message-level theorems of
  `Run.lean` hold at every fork).
- Before Glamsterdam: `processTransaction` runs with the one-counter gas meter `Nat`, the meter
  of these proofs.

## Hypotheses

Of the token (closed facts and its bytecode proof): `StorageOnly L P`,
`FrameKeepsR fork G L CODE P Q` for every `G` (or for one cap `G`, with `GasCap`),
`CODE.size ≠ 0`, `isValidDelegation CODE = false`.

Of the run of ONE transaction, `TxClean` (nothing global about Keccak):
- `auths`: no EIP-7702 authorization of the transaction sets a code with the hash of `CODE`
  (such a code is 0 or 23 bytes long, so only a Keccak collision breaks this);
- `data`: the call data of a transaction to `L` is below 2^256 bytes;
- `call`, `create`: the run of its first frame is `Clean`: each message that enters `L`, with
  the state that its frame starts from, satisfies `Q`, and a deposited code with the hash of
  `CODE` is `CODE`.

## Not covered

Block-level steps between transactions (withdrawals, the system calls of EIP-4788, EIP-2935,
EIP-7002 and EIP-7251) are not linked: `Chain` strings transactions only. The constructor run
that deploys `CODE` at `L` is not linked either (`good_of_zero` is only the shape of a base
case).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TokenKit.Seq

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState BlockState EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Transactions

variable {fork : Fork} {L : Address} {CODE : ByteArray} {P : State.TransactionState → Prop}
  {Q : Message fork → TransactionState → Prop}

/-! ## Deletions at the end of a transaction -/

/-- An account that holds code is not an empty account. -/
theorem not_empty_of_holds {S : TransactionState} (hold : HoldsCode L CODE S)
    (he : S.accountExistsAndIsEmpty L = true) : False := by
  unfold TransactionState.accountExistsAndIsEmpty at he
  split at he
  · rename_i account hopt
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    have hh : (S.getAccount L).codeHash = EMPTY_CODE_HASH := by
      unfold TransactionState.getAccount
      rw [hopt]
      exact he.1.2
    exact hold.2.1 hh
  · cases he

/-- The deletion of another account keeps the code and the storage of `L`. -/
theorem kept_destroyAccount (tx : TransactionState) {address : Address} (hne : L ≠ address) :
    Kept L tx (tx.destroyAccount address) :=
  Kept.of_sameOutside (TransactionState.sameOutside_destroyAccount tx address)
    (by simpa using hne) rfl rfl

/-- The deletion of the touched empty accounts keeps `L`, which holds code and so is not empty. -/
theorem kept_destroyTouched {tx : TransactionState} (touched : List Address)
    (hold : HoldsCode L CODE tx) :
    Kept L tx (tx.destroyTouchedEmptyAccounts fork touched) := by
  unfold TransactionState.destroyTouchedEmptyAccounts
  split
  · exact Kept.refl _ _
  · suffices hs : ∀ (l : List Address) (acc : TransactionState), HoldsCode L CODE acc →
        Kept L acc (l.foldl (fun tx address =>
          if tx.accountExistsAndIsEmpty address then tx.destroyAccount address else tx) acc) from
      hs touched tx hold
    intro l
    induction l with
    | nil => intro acc _; exact Kept.refl _ _
    | cons a l ih =>
      intro acc hacc
      rw [List.foldl_cons]
      have k1 : Kept L acc
          (if acc.accountExistsAndIsEmpty a then acc.destroyAccount a else acc) := by
        split
        · rename_i he
          by_cases hL : L = a
          · subst hL
            exact absurd he (fun he => not_empty_of_holds hacc he)
          · exact kept_destroyAccount acc hL
        · exact Kept.refl _ _
      exact k1.trans (ih _ (k1.holdsCode hacc))

/-- The deletion of a list of accounts without `L` keeps `L`, before Glamsterdam. -/
theorem kept_foldlM_destroy (hlt : fork < .glamsterdam) :
    ∀ (l : List Address) (S S' : TransactionState), (∀ a ∈ l, a ≠ L) →
      l.foldlM (fun (state : TransactionState) address =>
        if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
        else (pure (state.destroyAccount address) : Except State.StateError TransactionState))
        S = .ok S' → Kept L S S' := by
  have hge : ¬ fork ≥ .glamsterdam := Nat.not_le.mpr hlt
  intro l
  induction l with
  | nil =>
    intro S S' _ h
    cases h
    exact Kept.refl _ _
  | cons a l ih =>
    intro S S' hall h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
    rw [if_neg hge] at h1
    cases h1
    exact (kept_destroyAccount S (fun e => hall a List.mem_cons_self e.symm)).trans
      (ih _ _ (fun b hb => hall b (List.mem_cons_of_mem _ hb)) h2)

/-- The end of a transaction keeps `L`, when `L` holds code and is not an account to delete. -/
theorem kept_deleteAccounts (hlt : fork < .glamsterdam) {state state' : TransactionState}
    {output : CallOutput} (hold : HoldsCode L CODE state) (hd : L ∉ output.accountsToDelete)
    (h : deleteAccounts fork state output = .ok state') : Kept L state state' := by
  unfold deleteAccounts at h
  obtain ⟨mid, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  rw [Std.ExtTreeSet.foldlM_eq_foldlM_toList] at h1
  have k1 : Kept L state mid := kept_foldlM_destroy hlt _ _ _
    (fun a ha e => hd (e ▸ Std.ExtTreeSet.mem_toList.mp ha)) h1
  exact k1.trans (kept_destroyTouched _ (k1.holdsCode hold))

/-! ## The gas of a transaction -/

theorem kept_buyGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} (h : buyGas env state sender tx = .ok state') :
    Kept L state state' := by
  unfold buyGas at h
  obtain ⟨mid, h1, h2⟩ := Base.bind_ok_iff.mp h
  refine (kept_incrementNonce h1).trans (kept_modifyState h2 ?_)
  intro a b hab
  split at hab
  · cases hab
    rfl
  · cases hab

theorem kept_creditEther {state state' : TransactionState} {address : Address} {amount : Nat}
    (h : creditEther fork state address amount = .ok state') : Kept L state state' := by
  unfold creditEther at h
  split at h
  · exact kept_createEther h
  · cases h

theorem kept_payBeneficiary {state state' : TransactionState} {coinbase : Address} {fee : Nat}
    (hold : HoldsCode L CODE state) (h : payBeneficiary fork state coinbase fee = .ok state') :
    Kept L state state' := by
  unfold payBeneficiary at h
  split at h
  · cases h
    split
    · rename_i he
      by_cases hL : L = coinbase
      · subst hL
        exact absurd he (fun he => not_empty_of_holds hold he)
      · exact kept_destroyAccount state hL
    · exact Kept.refl _ _
  · exact kept_creditEther h

theorem kept_settleGas {env : BlockEnvironment fork} {state state' : TransactionState}
    {sender : Address} {tx : Transaction} {gasLeft refund used : Nat}
    (hold : HoldsCode L CODE state)
    (h : settleGas env state sender tx gasLeft refund = .ok (state', used)) :
    Kept L state state' := by
  unfold settleGas at h
  obtain ⟨s1, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨s2, h2, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have k1 : Kept L state s1 := kept_creditEther h1
  exact k1.trans (kept_payBeneficiary (k1.holdsCode hold) h2)

/-! ## The authorizations of EIP-7702 -/

/-- The code that an authorization sets is not `CODE`: it is empty or a delegation indicator. -/
theorem delegationCode_ne (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (auth : Authorization) : delegationCode auth ≠ CODE := by
  intro e
  unfold delegationCode at e
  split at e
  · apply hsize
    rw [← e]
    rfl
  · rw [← e, isValidDelegation_delegationIndicator] at hind
    cases hind

theorem createdAccounts_delegate {state state' : TransactionState} {authority : Address}
    {auth : Authorization} {refund : Nat}
    (h : delegate fork state authority auth = .ok (state', refund)) :
    state'.createdAccounts = state.createdAccounts := by
  obtain ⟨coded, hcode, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨bumped, hnonce, h⟩ := Base.bind_ok_iff.mp h
  cases h
  unfold TransactionState.incrementNonce at hnonce
  rw [TransactionState.createdAccounts_modifyState hnonce, createdAccounts_setCode hcode]

theorem createdAccounts_applyAuthorization {chainId : Nat} {done done' : Delegations Nat}
    {auth : Authorization} (h : applyAuthorization fork chainId done auth = .ok done') :
    done'.state.createdAccounts = done.state.createdAccounts := by
  rcases applyAuthorization_cases h with rfl | ⟨authority, -, -, ⟨-, rfl⟩ |
    ⟨-, paid, state, refund, hpay, hdelegate, rfl⟩⟩
  · rfl
  · rfl
  · obtain ⟨hstate, -, -⟩ := state_payAuthorization hpay
    show state.createdAccounts = done.state.createdAccounts
    rw [createdAccounts_delegate hdelegate, hstate]
    rfl

theorem createdAccounts_foldlM_applyAuthorization {chainId : Nat} :
    ∀ {auths : List Authorization} {start done : Delegations Nat},
      auths.foldlM (applyAuthorization fork chainId) start = .ok done →
      done.state.createdAccounts = start.state.createdAccounts
  | [], _, _, h => by
    cases h
    rfl
  | auth :: rest, start, done, h => by
    obtain ⟨next, hnext, h⟩ := Base.bind_ok_iff.mp h
    rw [createdAccounts_foldlM_applyAuthorization h, createdAccounts_applyAuthorization hnext]

/-- The authorizations of a transaction keep `L`, which holds real code.

No authorization may set a code with the hash of `CODE` (run-local: these authorizations). -/
theorem auths_keep (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {chainId : Nat} {state : TransactionState} {accessed paid : Std.ExtTreeSet Address}
    {meter : Nat} {auths : List Authorization} {done : Delegations Nat}
    (hold : HoldsCode L CODE state)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
    (h : applyAuthorizations fork chainId state accessed meter paid auths = .ok done) :
    HoldsCode L CODE done.state ∧ (∀ k, done.state.getStorage L k = state.getStorage L k) ∧
      done.state.createdAccounts = state.createdAccounts := by
  unfold applyAuthorizations at h
  have hne : ∀ auth ∈ auths, Cryptography.Hash.Keccak.keccak256 (delegationCode auth) ≠
      (state.getAccount L).codeHash := by
    intro auth ha e
    rw [hold.2.2] at e
    exact delegationCode_ne hsize hind auth (hh auth ha e)
  obtain ⟨ha, hs, -, hc⟩ := foldlM_applyAuthorization_keeps hsize hind h hold.1 hne
  have hacc : done.state.getAccount L = state.getAccount L := getAccount_congr ha
  exact ⟨⟨by rw [hacc]; exact hc, by rw [hacc]; exact hold.2.1, by rw [hacc]; exact hold.2.2⟩,
    hs, createdAccounts_foldlM_applyAuthorization h⟩

/-! ## The first frame of a transaction -/

theorem kept_ite_read (c : Prop) [Decidable c] (S : TransactionState) (t : Address) :
    Kept L S (if c then S.recordAccountRead t else S) := by
  split
  · exact kept_recordAccountRead _ _
  · exact Kept.refl _ _

/-- What the preparation of the first frame keeps, from a state where `L` holds `CODE`.

A creation is at another address than `L`, and a call to `L` runs `CODE`. -/
theorem prepareFirstFrame_facts (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Nat}
    (hold : HoldsCode L CODE state)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
    (h : prepareFirstFrame (Meter := Nat) chainId message state substate auths paid =
      .ok first) :
    HoldsCode L CODE first.state ∧ (∀ k, first.state.getStorage L k = state.getStorage L k) ∧
      (L ∈ first.state.createdAccounts → L ∈ state.createdAccounts) ∧
      first.substate.accountsToDelete = substate.accountsToDelete ∧
      first.message.target = message.target ∧
      first.message.currentTarget = message.currentTarget ∧
      first.message.data = message.data ∧
      (message.target = none → message.currentTarget ≠ L) ∧
      (message.target = some L → first.message.code = CODE) := by
  have hdel : delegatedAddress CODE = none := by simp [delegatedAddress, hind]
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
        exact ⟨holdsCode_recordAccountRead _ hold, fun _ => rfl, id, rfl, rfl, rfl, rfl,
          fun _ => ne_of_deployable (holdsCode_recordAccountRead _ hold) hd,
          fun e => by rw [htgt] at e; cases e⟩
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i target htgt
    obtain ⟨done, hdone, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨ha1, ha2, ha3⟩ := auths_keep hsize hind hold hh hdone
    have key : ∀ (S' : TransactionState) (code : ByteArray),
        (S'.recordAccountRead target).getCode
          ((S'.recordAccountRead target).getAccount target).codeHash = .ok code →
        (S' = done.state.recordAccountRead target ∨ S' = done.state) →
        Kept L done.state (S'.recordAccountRead target) := by
      rintro S' code - (rfl | rfl)
      · exact (kept_recordAccountRead _ _).trans (kept_recordAccountRead _ _)
      · exact kept_recordAccountRead _ _
    have hL : message.target = some L → target = L := by
      intro e
      rw [htgt] at e
      cases e
      rfl
    split at h
    all_goals split at h
    all_goals
      obtain ⟨m, hm, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨code, hcode, h⟩ := Base.bind_ok_iff.mp h
      have hg := Base.mapError_ok_iff.mp hcode
      have K := key _ _ hg (by first | exact Or.inl rfl | exact Or.inr rfl)
      have hcd : target = L → code = CODE := by
        intro e
        subst e
        rw [(K.holdsCode ha1).1] at hg
        cases hg
        rfl
      cases heq : (if fork ≥ Fork.pectra then delegatedAddress code else none) with
      | some delegate =>
        simp only [heq] at h
        have K2 := K.trans (kept_recordAccountRead _ delegate)
        have hno : message.target = some L → False := by
          intro e
          rw [hcd (hL e)] at heq
          split at heq
          · rw [hdel] at heq
            cases heq
          · cases heq
        split at h
        all_goals
          obtain ⟨m2, hm2, h⟩ := Base.bind_ok_iff.mp h
          obtain ⟨code2, hcode2, h⟩ := Base.bind_ok_iff.mp h
          cases h
          exact ⟨K2.holdsCode ha1, fun k => (K2.storage ha1.2.1 k).trans (ha2 k),
            fun hc => (congrArg (fun s => L ∈ s) ha3).mp (K2.created hc), rfl, rfl, rfl, rfl,
            fun e => (by rw [htgt] at e; cases e), fun e => (hno e).elim⟩
      | none =>
        simp only [heq] at h
        cases h
        exact ⟨K.holdsCode ha1, fun k => (K.storage ha1.2.1 k).trans (ha2 k),
          fun hc => (congrArg (fun s => L ∈ s) ha3).mp (K.created hc), rfl, rfl, rfl, rfl,
          fun e => (by rw [htgt] at e; cases e), fun e => hcd (hL e)⟩

/-! ## The message of a transaction -/

theorem ofFrame_state (evm : Evm fork Nat) (refund : Nat) (touched : Std.ExtTreeSet Address) :
    (CallOutput.ofFrame evm refund touched).state = evm.state := by
  unfold CallOutput.ofFrame
  dsimp only
  split <;> rfl

theorem ofFrame_dels {evm : Evm fork Nat} {refund : Nat} {touched : Std.ExtTreeSet Address}
    {x : Address} (h : x ∈ (CallOutput.ofFrame evm refund touched).accountsToDelete) :
    x ∈ evm.substate.accountsToDelete := by
  unfold CallOutput.ofFrame at h
  dsimp only at h
  split at h
  · exact absurd h Std.ExtTreeSet.not_mem_empty
  · exact h

/-- The message of a transaction keeps a good state good and leaves `L` out of the accounts to
delete. From Dencun. The hypotheses on the run are local: these authorizations, this first
frame. -/
theorem processMessageCall_good (so : StorageOnly L P)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false) (hden : Fork.dencun ≤ fork)
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {output : CallOutput}
    (fk : ∀ first,
      prepareFirstFrame (Meter := Nat) chainId message state substate auths paid = .ok first →
      FrameKeepsR fork first.message.gas L CODE P Q)
    (g : Good L CODE P state) (hc : L ∉ state.createdAccounts)
    (hd : L ∉ substate.accountsToDelete)
    (hcur : ∀ t, message.target = some t → message.currentTarget = t)
    (hdata : message.target = some L → message.data.size < 2 ^ 256)
    (hh : ∀ auth ∈ auths,
      Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
        Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE)
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
  unfold processMessageCall at h
  split at h
  · rename_i e read hprep
    split at h
    · cases h
    · cases h
      exact ⟨(Kept.of_sameOutside (TransactionState.sameOutside_withReadsOf state read)
        (by simp) rfl rfl).good so g, Std.ExtTreeSet.not_mem_empty⟩
  · rename_i first hprep
    obtain ⟨hold1, hst1, hcr1, hdl1, htg1, hct1, hda1, hne1, hcode1⟩ :=
      prepareFirstFrame_facts hsize hind g.1 hh hprep
    have g1 : Good L CODE P first.state := ⟨hold1, so state first.state hst1 g.2⟩
    have hc1 : L ∉ first.state.createdAccounts := fun x => hc (hcr1 x)
    have hd1 : L ∉ first.substate.accountsToDelete := by rw [hdl1]; exact hd
    split at h
    · rename_i htgt
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have hne : first.message.currentTarget ≠ L := by rw [hct1]; exact hne1 htgt
      have cl := (clean first hprep).2 (by rw [htg1]; exact htgt)
      have gE := processCreateMessage_good_local so (fk first hprep) hdel (Nat.le_refl _) hne g1
        cl hrun
      have uE := processCreateMessage_unmarked_local so (fk first hprep) hdel (Nat.le_refl _) hne
        hden hold1 hc1 hd1 cl hrun
      exact ⟨by rw [ofFrame_state]; exact gE, fun hx => uE.dels (ofFrame_dels hx)⟩
    · rename_i target htgt
      obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
      cases h
      have sane : Sane L CODE first.message := by
        intro ht
        have ht' : message.currentTarget = L := by rw [← hct1]; exact ht
        have htl : message.target = some L := by rw [htgt, ← hcur _ htgt, ht']
        exact ⟨hcode1 htl, by rw [htg1, htgt]; rfl, by rw [hda1]; exact hdata htl⟩
      have cl := (clean first hprep).1 (by rw [htg1, htgt]; rfl)
      have gE := processMessage_good_local so (fk first hprep) hdel (Nat.le_refl _) sane g1 cl hrun
      have uE := processMessage_unmarked_local so (fk first hprep) hdel (Nat.le_refl _) hden hold1
        hc1 hd1 cl hrun
      exact ⟨by rw [ofFrame_state]; exact gE, fun hx => uE.dels (ofFrame_dels hx)⟩

/-! ## A whole transaction -/

/-- The message of a transaction: it has the recipient of the transaction, it runs at `target`,
and a call carries the data of the transaction. -/
theorem transactionMessage_facts {env : BlockEnvironment fork}
    {txEnv : TransactionEnvironment fork} {state : TransactionState} {sender target : Address}
    {gas nonce : Nat} {tx : Transaction} {message : Message fork}
    (ht : messageTarget sender nonce tx = .ok target)
    (h : transactionMessage env txEnv state sender target gas tx = .ok message) :
    message.target = tx.to ∧ message.currentTarget = target ∧
      (∀ t, tx.to = some t → target = t ∧ message.data = tx.data) := by
  unfold transactionMessage at h
  unfold messageTarget at ht
  dsimp only at h
  split at h
  · rename_i to hto
    obtain ⟨code, -, rfl⟩ := Base.map_ok_iff.mp h
    rw [hto] at ht
    cases ht
    refine ⟨rfl, rfl, fun t e => ?_⟩
    rw [hto] at e
    cases e
    exact ⟨rfl, rfl⟩
  · rename_i hto
    cases h
    refine ⟨rfl, rfl, fun t e => ?_⟩
    rw [hto] at e
    cases e

/-- `first` is the first frame of the transaction `tx`, as `runTransaction Nat` prepares it on
the block state `block`: after the sender buys the gas, and after the authorizations. -/
def FirstOf (env : BlockEnvironment fork) (block : BlockState) (included : Included)
    (tx : Transaction) (first : FirstFrame fork Nat) : Prop :=
  ∃ target bought message,
    messageTarget included.sender
        ((TransactionState.ofBlock block).getAccount included.sender).nonce tx = .ok target ∧
    buyGas env (TransactionState.ofBlock block) included.sender tx = .ok bought ∧
    transactionMessage env ⟨included.sender, included.gasPrice, fun _ => tx.blobHashes⟩ bought
        included.sender target (allocateGas fork tx included.intrinsicGas).execution tx =
      .ok message ∧
    prepareFirstFrame (Meter := Nat) env.chainId.toNat
        { message with reservoir := (allocateGas fork tx included.intrinsicGas).reservoir }
        bought (startSubstate fork env.coinbase included.sender target tx) tx.authorizations
        (paidWrites included.sender target tx) = .ok first

/-- The run-local hypotheses on ONE transaction. Nothing here is about another run. -/
structure TxClean (L : Address) (CODE : ByteArray) (Q : Message fork → TransactionState → Prop)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included)
    (tx : Transaction) : Prop where
  /-- No authorization of the transaction sets a code with the hash of `CODE`. -/
  auths : ∀ auth ∈ tx.authorizations,
    Cryptography.Hash.Keccak.keccak256 (delegationCode auth) =
      Cryptography.Hash.Keccak.keccak256 CODE → delegationCode auth = CODE
  /-- The call data of a transaction to `L` is below 2^256 bytes. -/
  data : tx.to = some L → tx.data.size < 2 ^ 256
  /-- The run of the first frame of a call is clean. -/
  call : ∀ first, FirstOf env block included tx first → first.message.target.isSome = true →
    Clean L CODE Q first.message first.state first.substate first.meter
  /-- The run of the first frame of a creation is clean. -/
  create : ∀ first, FirstOf env block included tx first → first.message.target = none →
    CleanCreate L CODE Q first.message first.state first.substate first.meter

/-- The block state after a transaction is good when the state of the transaction is. -/
theorem good_incorporate (so : StorageOnly L P) {S : TransactionState}
    (g : Good L CODE P S) :
    Good L CODE P (TransactionState.ofBlock S.incorporateTxIntoBlock.parent) := by
  have e : TransactionState.ofBlock S.incorporateTxIntoBlock.parent =
      S.incorporateTxIntoBlock := rfl
  rw [e]
  exact ⟨holdsCode_of_eq
      (getAccount_congr (TransactionState.getAccountOptional_incorporateTxIntoBlock S L))
      (funext (TransactionState.getCode_incorporateTxIntoBlock S)) g.1,
    so _ _ (fun k => TransactionState.getStorage_incorporateTxIntoBlock S L k) g.2⟩

/-- The core form: the interface of the token is asked at the gas of the first frame of this
transaction only. A whole transaction, as EthLib's `runTransaction Nat` runs it, keeps `L` good:
from the block state before it to the block state after it. With or without an error of its message,
whoever sends it, whatever it calls, at any depth. From Dencun, before Glamsterdam. -/
theorem runTransaction_good_at (so : StorageOnly L P)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (fk : ∀ first, FirstOf env block included tx first →
      FrameKeepsR fork first.message.gas L CODE P Q)
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
  have hcb : L ∉ bought.createdAccounts := fun x =>
    absurd (kb.created x) Std.ExtTreeSet.not_mem_empty
  obtain ⟨mt, mc, md⟩ := transactionMessage_facts hTarget hMessage
  obtain ⟨gO, hdO⟩ := processMessageCall_good so hsize hind hden
    (fun first hp => fk first ⟨target, bought, message, hTarget, hBought', hMessage, hp⟩)
    (kb.good so g) hcb
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
    (fun first hp =>
      ⟨clean.call first ⟨target, bought, message, hTarget, hBought', hMessage, hp⟩,
        clean.create first ⟨target, bought, message, hTarget, hBought', hMessage, hp⟩⟩)
    hOutput
  have ks : Kept L output.state settled := kept_settleGas gO.1 hSettle'
  have kd : Kept L settled deleted := kept_deleteAccounts hlt (ks.holdsCode gO.1) hdO hDeleted'
  exact good_incorporate so (kd.good so (ks.good so gO))

/-- A whole transaction, as EthLib's `runTransaction Nat` runs it, keeps `L` good: from the
block state before it to the block state after it. With or without an error of its message,
whoever sends it, whatever it calls, at any depth. From Dencun, before Glamsterdam. For a token
whose interface holds for every cap on gas. -/
theorem runTransaction_good (so : StorageOnly L P) (fk : ∀ G, FrameKeepsR fork G L CODE P Q)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : TxClean L CODE Q env block included tx)
    (h : runTransaction Nat env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) :=
  runTransaction_good_at so hsize hind hden hlt (fun _ _ => fk _) clean h g

/-- The gas of the first frame of the transaction is at most `G`. RUN-LOCAL: it speaks of this
transaction only. (The gas of the first frame is the gas limit of the transaction minus its
intrinsic gas, so it holds when the gas limit is at most `G`; that step is not proved here.) -/
def GasCap (G : Nat) (env : BlockEnvironment fork) (block : BlockState) (included : Included)
    (tx : Transaction) : Prop :=
  ∀ first, FirstOf env block included tx first → first.message.gas ≤ G

/-- The interface with the cap `G` gives the interface with every smaller cap. -/
theorem FrameKeepsR.mono {G G' : Nat} (fk : FrameKeepsR fork G L CODE P Q) (hle : G' ≤ G) :
    FrameKeepsR fork G' L CODE P Q := by
  intro bound message state substate gas evm s within hG
  exact fk within (Nat.le_trans hG hle)

/-- A whole transaction keeps `L` good, for a token whose interface holds under the cap `G` on
gas only (a token that makes a real outside call): the first frame has at most `G` gas. -/
theorem runTransaction_good_cap {G : Nat} (so : StorageOnly L P)
    (fk : FrameKeepsR fork G L CODE P Q)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (cap : GasCap G env block included tx)
    (clean : TxClean L CODE Q env block included tx)
    (h : runTransaction Nat env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) :=
  runTransaction_good_at so hsize hind hden hlt (fun first hf => fk.mono (cap first hf)) clean h g

/-- The same for EthLib's `processTransaction`. -/
theorem processTransaction_good_cap {G : Nat} (so : StorageOnly L P)
    (fk : FrameKeepsR fork G L CODE P Q)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (cap : GasCap G env block included tx)
    (clean : TxClean L CODE Q env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) := by
  rw [processTransaction_of_lt_glamsterdam hlt] at h
  exact runTransaction_good_cap so fk hsize hind hden hlt cap clean h g

/-- A whole transaction, as EthLib's `processTransaction` runs it, keeps `L` good. From Dencun,
before Glamsterdam (where `processTransaction` is `runTransaction Nat`). -/
theorem processTransaction_good (so : StorageOnly L P)
    (fk : ∀ G, FrameKeepsR fork G L CODE P Q)
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    (hden : Fork.dencun ≤ fork) (hlt : fork < .glamsterdam)
    {env : BlockEnvironment fork} {block : BlockState} {included : Included}
    {tx : Transaction} {out : TransactionOutput}
    (clean : TxClean L CODE Q env block included tx)
    (h : processTransaction env block included tx = .ok out)
    (g : Good L CODE P (TransactionState.ofBlock block)) :
    Good L CODE P (TransactionState.ofBlock out.block) := by
  rw [processTransaction_of_lt_glamsterdam hlt] at h
  exact runTransaction_good so fk hsize hind hden hlt clean h g

/-! ## Any finite list of transactions -/

/-- A finite list of transactions that takes the block state `b` to the block state `b'`.

Each one is run by EthLib's `processTransaction`, at its own fork (from Dencun, before
Glamsterdam), in its own block environment, on the block state that the one before left, and
satisfies the run-local hypotheses `TxClean`. `Qf fork` is the hypothesis `Q` at that fork. -/
inductive Chain (L : Address) (CODE : ByteArray)
    (Qf : (fork : Fork) → Message fork → TransactionState → Prop) :
    BlockState → BlockState → Prop
  /-- No transaction. -/
  | nil (b : BlockState) : Chain L CODE Qf b b
  /-- One transaction, then the rest of the list. -/
  | cons {fork : Fork} {env : BlockEnvironment fork} {b b' : BlockState} {included : Included}
      {tx : Transaction} {out : TransactionOutput} :
      Fork.dencun ≤ fork → fork < .glamsterdam →
      processTransaction env b included tx = .ok out →
      TxClean L CODE (Qf fork) env b included tx →
      Chain L CODE Qf out.block b' → Chain L CODE Qf b b'

/-- Any finite list of transactions keeps `L` good: it holds `CODE` and `P` holds, after the
last one as before the first one. -/
theorem chain_good {Qf : (fork : Fork) → Message fork → TransactionState → Prop}
    (so : StorageOnly L P)
    (fk : ∀ fork, Fork.dencun ≤ fork → fork < .glamsterdam →
      ∀ G, FrameKeepsR fork G L CODE P (Qf fork))
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {b b' : BlockState} (chain : Chain L CODE Qf b b')
    (g : Good L CODE P (TransactionState.ofBlock b)) :
    Good L CODE P (TransactionState.ofBlock b') := by
  induction chain with
  | nil => exact g
  | cons hden hlt hrun clean _ ih =>
    exact ih (processTransaction_good so (fk _ hden hlt) hsize hind hden hlt clean hrun g)

/-- A finite list of transactions as in `Chain`, each with at most `G` gas in its first frame
(`GasCap`). For a token whose interface holds under a cap on gas only. -/
inductive ChainCap (L : Address) (CODE : ByteArray)
    (Qf : (fork : Fork) → Message fork → TransactionState → Prop) (G : Nat) :
    BlockState → BlockState → Prop
  /-- No transaction. -/
  | nil (b : BlockState) : ChainCap L CODE Qf G b b
  /-- One transaction, then the rest of the list. -/
  | cons {fork : Fork} {env : BlockEnvironment fork} {b b' : BlockState} {included : Included}
      {tx : Transaction} {out : TransactionOutput} :
      Fork.dencun ≤ fork → fork < .glamsterdam →
      processTransaction env b included tx = .ok out →
      GasCap G env b included tx →
      TxClean L CODE (Qf fork) env b included tx →
      ChainCap L CODE Qf G out.block b' → ChainCap L CODE Qf G b b'

/-- Any finite list of transactions with at most `G` gas each keeps `L` good, for a token whose
interface holds under the cap `G`. -/
theorem chainCap_good {Qf : (fork : Fork) → Message fork → TransactionState → Prop} {G : Nat}
    (so : StorageOnly L P)
    (fk : ∀ fork, Fork.dencun ≤ fork → fork < .glamsterdam →
      FrameKeepsR fork G L CODE P (Qf fork))
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false)
    {b b' : BlockState} (chain : ChainCap L CODE Qf G b b')
    (g : Good L CODE P (TransactionState.ofBlock b)) :
    Good L CODE P (TransactionState.ofBlock b') := by
  induction chain with
  | nil => exact g
  | cons hden hlt hrun cap clean _ ih =>
    exact ih (processTransaction_good_cap so (fk _ hden hlt) hsize hind hden hlt cap clean hrun g)

/-! ## The base case -/

/-- The shape of the base case of a token: a state where every word of the storage of `L` is
zero satisfies the invariant. -/
def ZeroBase (L : Address) (P : State.TransactionState → Prop) : Prop :=
  ∀ S : TransactionState, (∀ k, S.getStorage L k = 0) → P S

/-- A state where `L` holds `CODE` and its storage is all zero is good. -/
theorem good_of_zero (hz : ZeroBase L P) {S : TransactionState} (hold : HoldsCode L CODE S)
    (h0 : ∀ k, S.getStorage L k = 0) : Good L CODE P S :=
  ⟨hold, hz S h0⟩

/-- From a block state where `L` holds `CODE` with all-zero storage, the invariant holds after
any finite list of transactions. -/
theorem chain_from_zero {Qf : (fork : Fork) → Message fork → TransactionState → Prop}
    (so : StorageOnly L P)
    (fk : ∀ fork, Fork.dencun ≤ fork → fork < .glamsterdam →
      ∀ G, FrameKeepsR fork G L CODE P (Qf fork))
    (hsize : CODE.size ≠ 0) (hind : isValidDelegation CODE = false) (hz : ZeroBase L P)
    {b b' : BlockState} (chain : Chain L CODE Qf b b')
    (hold : HoldsCode L CODE (TransactionState.ofBlock b))
    (h0 : ∀ k, (TransactionState.ofBlock b).getStorage L k = 0) :
    P (TransactionState.ofBlock b') :=
  (chain_good so fk hsize hind chain (good_of_zero hz hold h0)).2

end TokenKit.Seq

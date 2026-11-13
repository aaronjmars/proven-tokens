import SkyVerify.Sky.Permit1271
import SkyVerify.Sky.Seq
import TokenKit.Evm.Readable

/-!
# SKY: `permit(v, r, s)` in the invariant, in sequences of calls, and in plain terms

Hand-written, after tokens/usdd PermitSeq.lean.

- `supply_permit`: a `permit` that ends with no error keeps `Inv` (the sum of the balances is
  `totalSupply`), by the signature path and by the ERC-1271 path (the STATICCALL to the owner
  keeps every storage word, with no assumption on the code of the owner).
- `PermitCall`, `CallsP`, `inv_callsP`: sequences of calls with `permit(v, r, s)`.
- `permitCall_process`, `process_step_all`, `process_step_all_inv`, `callsP_process`: over
  EthLib's `processMessage`. The other `permit` (selector `0x9fd5a6cf`, a signature as bytes)
  is not covered: `process_step_all` keeps the hypothesis that the selector is not that one.
  Sky/PermitBytesSeq.lean covers it for a signature of 65 bytes (`process_step_sig65`).
- `permit_readable`: the effects of `permit(v, r, s)` over the start state.

Scope: from Paris and before Glamsterdam. `Sep (callKeys message)` is the hypothesis on keccak
(not proved). `NoDelegation1`: the account at address 1 holds no EIP-7702 delegation code.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The account at address 1 (ECRECOVER) holds no EIP-7702 delegation code in the state `S`.
Used from Pectra only. -/
def NoDelegation1 (fork : Fork) (S : State.TransactionState) : Prop :=
  ∀ c, S.getCode (S.getAccount (toAddressMasked 1)).codeHash = .ok c →
    .pectra ≤ fork → delegatedAddress c = none

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- What every way `PermitEndKept` holds gives: a state `st'` with the storage of the token as in
`st` and a substate `ss'` with the logs of `ss` (they are `st` and `ss` on the signature path,
and the state and the substate after the STATICCALL to the owner on the ERC-1271 path); the
token account exists in `st'`; nothing is returned; the end state is `st'` with the allowance
slot written; the logs are those of `ss'` and then `Approval(owner, spender, value)`. -/
theorem permitEnd_facts {st : State.TransactionState} {ss : Substate} {g : Nat}
    {s : Evm fork Nat} {owner spender value rec : U256}
    (h : PermitEndKept fork message st ss g s owner spender value rec) :
    ∃ (st' : State.TransactionState) (ss' : Substate),
      hasAccount st' message.currentTarget ∧
      (∀ n, storageAt st' message.currentTarget n = storageAt st message.currentTarget n) ∧
      ss'.logs = ss.logs ∧ s.output = ByteArray.empty ∧
      s.state = writeSlot st' message.currentTarget (permitAllowKey owner spender) value ∧
      s.substate.logs = ss'.logs.push (Readable.log3 message.currentTarget APPROVAL_TOPIC
        (bitwiseAnd ADDR_MASK owner) (bitwiseAnd spender ADDR_MASK) (wordBytes value)) := by
  unfold PermitEndKept PermitKept PermitWrites at h
  rcases h with ⟨-, -, hacc, -, hout, -, hst, hsub⟩ |
    ⟨-, -, c, out, st', ss', g', -, -, -, -, hso, -, hlogs, -, -, -, -, hacc, -, hout, -, hst,
      hsub⟩
  · exact ⟨st, ss, hacc, fun _ => rfl, rfl, hout, hst,
      by rw [hsub, Readable.logs_logSub, Readable.logs_storeSub]⟩
  · exact ⟨st', ss', hacc, fun n => (hso message.currentTarget (by simp)).2.1 _, hlogs, hout,
      hst, by rw [hsub, Readable.logs_logSub, Readable.logs_storeSub]⟩

/-- The `PermitEndKept` of a `permit` that ends with no error, for either layout of the memory
(from `PermitEnd`, which also names the call to the owner; see `ok_permit_full`). -/
theorem permit_end (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitChecks message ∧ message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    ∃ (g : Nat) (rec : U256),
      PermitEndKept fork message (ecState message (permitState1 message state))
        (ecSub (permitSub1 fork message state substate)) g s (loadWord message.data 4 32)
        (loadWord message.data 36 32) (loadWord message.data 68 32) rec := by
  obtain ⟨hchecks, hstatic, hacc, hlay⟩ :=
    ok_permit_full hparis hglam hsize' hsel hdel start within hrun hok
  refine ⟨hchecks, hstatic, hacc, ?_⟩
  rcases hlay with ⟨-, hA⟩ | ⟨-, hA⟩
  · unfold PermitAfterEc at hA
    obtain ⟨-, -, M, -, hend⟩ := hA
    exact ⟨_, _, PermitEnd.kept hend⟩
  · unfold PermitAfterEc at hA
    obtain ⟨-, -, M, -, hend⟩ := hA
    exact ⟨_, _, PermitEnd.kept hend⟩

/-- From Paris and before Glamsterdam, under the real runner: a successful `permit(v, r, s)`
keeps the invariant, by the signature path and by the ERC-1271 path. `hsep` is the hypothesis
on keccak (not proved). -/
theorem supply_permit (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  obtain ⟨-, -, hacc, g, rec, hend⟩ :=
    permit_end hparis hglam hsize' hsel hdel hsep start within hrun hok
  obtain ⟨st', ss', hacc', hsame, -, -, hst, -⟩ := permitEnd_facts hend
  rw [hst]
  clear hst hend start hrun hok
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  have hS1 : Inv message.currentTarget (permitState1 message state) := by
    unfold Inv Supply.Inv at hinv ⊢
    simp only [permitState1, permitNonceKey, permitOwner, ADDR_MASK, and_mask_comm]
    simp (disch := slot_side) only [Supply.D_read, D_nonce hsep hm2]
    exact hinv
  have hS2 : Inv message.currentTarget st' := (Supply.inv_congr hsame).mpr hS1
  unfold Inv Supply.Inv at hS2 ⊢
  simp only [permitAllowKey, ADDR_MASK, and_mask_comm]
  simp (disch := slot_side) only [D_allow hsep hm2 hm3]
  exact hS2

/-- One run of `permit(v, r, s)` on `CODE` for a message to `C` that ends with no error, from
`S` to `S'`, under the hypotheses of `supply_permit`. -/
def PermitCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .paris ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ selector message.data = 0xd505accf ∧ NoDelegation1 fork S ∧
    Sep (callKeys message) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within
      = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One successful `permit(v, r, s)` keeps `Inv C`. -/
theorem inv_permitCall {C : Address} {S S' : State.TransactionState}
    (h : PermitCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    hdel, K, start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_permit hparis hglam hsize hsel hdel K hI start within hrun hok

/-- A finite sequence of successful calls to `C` (`permit(v, r, s)` or a function of `GoodCall`)
and of changes that keep the storage of `C`. -/
inductive CallsP (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : CallsP C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → CallsP C S' S'' →
      CallsP C S S''
  | permit {S S' S'' : State.TransactionState} : PermitCall C S S' → CallsP C S' S'' →
      CallsP C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → CallsP C S' S'' →
      CallsP C S S''

/-- A sequence without `permit` is a sequence. -/
theorem callsP_of_calls {C : Address} {S S' : State.TransactionState} (h : Calls C S S') :
    CallsP C S S' := by
  induction h with
  | nil => exact .nil _
  | call hg _ ih => exact .call hg ih
  | other hu _ ih => exact .other hu ih

/-- `Inv C` along every finite sequence of successful calls to `C`, `permit(v, r, s)` included,
and of changes that keep the storage of `C`. Each call carries its own hypothesis on keccak. -/
theorem inv_callsP {C : Address} {S S' : State.TransactionState}
    (h : CallsP C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | permit hp _ ih => exact ih (inv_permitCall hp hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- From Paris and before Glamsterdam, a top-level `permit(v, r, s)` message to `C` (code
`CODE`, no value moved, no precompile), run by EthLib's `processMessage`, that ends with no
error, is a `PermitCall` from its start state to its end state. -/
theorem permitCall_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    PermitCall message.currentTarget state ended.val.state := by
  have hst : startState fork message state = state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  generalize hres : runFrame (step fork) (step_decreases fork) message.gas
    (processRunner (Meter := Nat) fork message.gas)
    (startFrame message (startState fork message state) substate
      (GasMeter.start message.gas message.reservoir)) (Nat.le_refl _) = result
  have hmap := processMessage_map_val noValue noPrecompile hres
  rw [hproc] at hmap
  rcases result with e | s
  · cases hmap
  · simp only [Except.map, Except.ok.injEq] at hmap
    have hse : s.error = none := by
      rw [← hok, hmap]
      unfold rollbackOnError
      split <;> rfl
    have hend : ended.val = s := by
      rw [hmap]
      unfold rollbackOnError
      simp [hse]
    have start := At.startFrame hmc (startState fork message state) substate
    rw [hst] at start hres
    exact ⟨fork, message, substate, message.gas, message.gas, _,
      s, Nat.le_refl _, rfl, hparis, hglam, hsize, hsel, hdel, K, start, hres, hse,
      by rw [hend]⟩

/-- From Paris and before Glamsterdam, every top-level message to `C` whose code is `CODE` (no
precompile, call data below 2^256 bytes, any selector but `0x9fd5a6cf`, the `permit` with a
signature as bytes, which is not covered), run by EthLib's `processMessage` to the end, is a
step of `CallsP C`: a `GoodCall` or a `PermitCall` when it ends with no error, and an
`Untouched` step when it ends with an error. `K` is the hypothesis on keccak (not proved);
`hdel` is used by `permit` only. -/
theorem process_step_all (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hsel0 : selector message.data ≠ 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      PermitCall message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_fails (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · by_cases hsel : selector message.data = 0xd505accf
      · exact .inr (.inl (permitCall_process hparis hglam hmc ht noPrecompile hsize hsel hdel K
          hproc herr))
      · exact .inl (goodCall_process hparis hglam hmc ht noPrecompile hsize hsel0 hsel K hproc herr)
  · exact .inr (.inr (untouched_process_failed hproc herr _))

/-- From Paris and before Glamsterdam, a top-level message of `CODE` to `C` that
`processMessage` ends, with any selector but `0x9fd5a6cf`: `Inv` at its start gives `Inv` at
its end. -/
theorem process_step_all_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hsel0 : selector message.data ≠ 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state := by
  rcases process_step_all hparis hglam hmc noPrecompile hsize hsel0 hdel K hproc with h | h | h
  · exact inv_goodCall h hI
  · exact inv_permitCall h hI
  · exact inv_untouched h hI

/-- A top-level message of `CODE` to `C` with any selector but `0x9fd5a6cf`, then a sequence of
steps, is a sequence of steps. -/
theorem callsP_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {S' : State.TransactionState}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hsel0 : selector message.data ≠ 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : CallsP message.currentTarget ended.val.state S') :
    CallsP message.currentTarget state S' := by
  rcases process_step_all hparis hglam hmc noPrecompile hsize hsel0 hdel K hproc with h | h | h
  · exact .call h rest
  · exact .permit h rest
  · exact .other h rest

/-! ## `permit(v, r, s)` in plain terms over the start state -/

/-- permit(owner, spender, value, deadline, v, r, s), under the real runner, from Paris and
before Glamsterdam. A run that ends with no error passed the checks of `PermitChecks` and was
not static. Then: nothing is returned; `nonces[owner]` is the old word plus 1;
`allowance[owner][spender]` is `value`; every other slot keeps its word; the logs are the logs
at the start and then exactly one log, Approval(owner, spender, value). This holds on the
signature path and on the ERC-1271 path (which of the two, and what each needs, is in
`ok_permit_full`). `hsep` is the hypothesis on keccak (not proved); it is used for one fact,
that the allowance slot is not the nonce slot. -/
theorem permit_readable (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitChecks message ∧ message.isStatic = false ∧ s.output = ByteArray.empty ∧
    storageAt s.state message.currentTarget (permitNonceKey message) =
      add (storageAt state message.currentTarget (permitNonceKey message)) (1 : U256) ∧
    storageAt s.state message.currentTarget
      (permitAllowKey (loadWord message.data 4 32) (loadWord message.data 36 32)) =
      loadWord message.data 68 32 ∧
    (∀ k, k ≠ permitNonceKey message →
      k ≠ permitAllowKey (loadWord message.data 4 32) (loadWord message.data 36 32) →
      storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
    s.substate.logs = substate.logs.push (Readable.log3 message.currentTarget APPROVAL_TOPIC
      (bitwiseAnd ADDR_MASK (loadWord message.data 4 32))
      (bitwiseAnd (loadWord message.data 36 32) ADDR_MASK)
      (wordBytes (loadWord message.data 68 32))) := by
  obtain ⟨hchecks, hstatic, hacc, g, rec, hend⟩ :=
    permit_end hparis hglam hsize' hsel hdel hsep start within hrun hok
  obtain ⟨st', ss', hacc', hsame, hlogs', hout, hst, hlogs⟩ := permitEnd_facts hend
  clear hend start hrun hok
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  have hne : permitNonceKey message ≠
      permitAllowKey (loadWord message.data 4 32) (loadWord message.data 36 32) := by
    simp only [permitAllowKey, permitNonceKey, permitOwner, ADDR_MASK, and_mask_comm]
    exact fun e => (hsep.nonce _ hm2).2.2 _ hm2 _ hm3 e.symm
  have hacc1 := hasAccount_readSlot (other := message.currentTarget)
    (n := permitNonceKey message) hacc
  have hsame' : ∀ n, storageAt st' message.currentTarget n =
      storageAt (permitState1 message state) message.currentTarget n := hsame
  refine ⟨hchecks, hstatic, hout, ?_, ?_, ?_, ?_⟩
  · rw [hst, storageAt_writeSlot_of_ne hacc' hne, hsame', storageAt_writeSlot_self hacc1]
  · rw [hst, storageAt_writeSlot_self hacc']
  · intro k hk1 hk2
    rw [hst, storageAt_writeSlot_of_ne hacc' hk2, hsame', storageAt_writeSlot_of_ne hacc1 hk1,
      storageAt_readSlot]
  · rw [hlogs, hlogs']

end SkyVerify

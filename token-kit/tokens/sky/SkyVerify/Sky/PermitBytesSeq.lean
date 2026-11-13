import SkyVerify.Sky.PermitBytesAny
import SkyVerify.Sky.PermitSeq

/-!
# SKY: `permit` with a signature given as bytes: the invariant, sequences of calls, plain terms

Hand-written, after Sky/PermitSeq.lean, for `permit(owner, spender, value, deadline, bytes
signature)` (selector `0x9fd5a6cf`).

EVERY SIGNATURE LENGTH (audit 4, SKY-2). The code takes the ECRECOVER path only when the length
word of the signature is 65; for every other length it asks the owner contract (ERC-1271) with
the bytes as given. Both routes are proved: `ok_permitBytes65_full` (Sky/PermitBytes.lean) for
65 and `ok_permitBytes_other` (Sky/PermitBytesAny.lean) for every other length, joined in
`ok_permitBytes_full`. This file has two layers:

- with no hypothesis on the length: `permitBytes_end`, `supply_permitBytes`,
  `permitBytes_readable`, `PermitBytesCall`, `CallsAny`, `inv_callsAny`,
  `permitBytesCall_process`, `process_step_any`, `process_step_any_inv`, `callsAny_process`.
  `process_step_any` is for every message to the code: no hypothesis on the selector and none
  on the call data but its size below 2^256.
- the special case of a length word of 65, kept under the names that carry `65`
  (`permitBytes65_end`, `supply_permitBytes65`, `permitBytes65_readable`, `PermitBytes65Call`,
  `Calls65`, `inv_calls65`, `permitBytes65Call_process`, `process_step_sig65`,
  `process_step_sig65_inv`, `calls65_process`): each has the hypothesis `hlen` that the length
  word is 65. `calls65_any` turns a `Calls65` into a `CallsAny`.

Scope: from Paris and before Glamsterdam. `Sep (callKeys message)` is the hypothesis on keccak
(not proved). `NoDelegation1`: the account at address 1 holds no EIP-7702 delegation code (used
by the ECRECOVER path only, so by a length word of 65 only; the statements with no hypothesis
on the length carry it because the length is not known).
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

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The `PermitEndKept` of a `permit` with a signature of 65 bytes that ends with no error, for
either layout of the memory (from `PermitEnd`, which also names the call to the owner; see
`ok_permitBytes65_full`). -/
theorem permitBytes65_end (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytes65Checks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ∃ (g : Nat) (rec : U256),
      PermitEndKept fork message (ecState message (permitState1 message state))
        (ecSub (permitSub1 fork message state substate)) g s (loadWord message.data 4 32)
        (loadWord message.data 36 32) (loadWord message.data 68 32) rec := by
  obtain ⟨hchecks, hstatic, hacc, hlay⟩ :=
    ok_permitBytes65_full hparis hglam hsize' hsel hlen hdel start within hrun hok
  refine ⟨hchecks, hstatic, hacc, ?_⟩
  rcases hlay with ⟨-, hA⟩ | ⟨-, hA⟩
  · unfold PermitBytes65AfterEc at hA
    obtain ⟨-, -, -, hend⟩ := hA
    exact ⟨_, _, hend.kept⟩
  · unfold PermitBytes65AfterEc at hA
    obtain ⟨-, -, -, hend⟩ := hA
    exact ⟨_, _, hend.kept⟩

/-- From Paris and before Glamsterdam, under the real runner: a successful `permit` with a
signature of 65 bytes keeps the invariant, by the signature path and by the ERC-1271 path.
`hsep` is the hypothesis on keccak (not proved). -/
theorem supply_permitBytes65 (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
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
    permitBytes65_end hparis hglam hsize' hsel hlen hdel start within hrun hok
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

/-- One run of `permit` with a signature of 65 bytes on `CODE` for a message to `C` that ends
with no error, from `S` to `S'`, under the hypotheses of `supply_permitBytes65`. -/
def PermitBytes65Call (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .paris ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ selector message.data = 0x9fd5a6cf ∧
    loadWord message.data (sigPtr message).toNat 32 = (65 : U256) ∧ NoDelegation1 fork S ∧
    Sep (callKeys message) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within
      = .ok s ∧
    s.error = none ∧ S' = s.state

/-- One successful `permit` with a signature of 65 bytes keeps `Inv C`. -/
theorem inv_permitBytes65Call {C : Address} {S S' : State.TransactionState}
    (h : PermitBytes65Call C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    hlen, hdel, K, start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_permitBytes65 hparis hglam hsize hsel hlen hdel K hI start within hrun hok

/-- A finite sequence of successful calls to `C` (a function of `GoodCall`, `permit(v, r, s)`,
or `permit` with a signature of 65 bytes) and of changes that keep the storage of `C`. -/
inductive Calls65 (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : Calls65 C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → Calls65 C S' S'' →
      Calls65 C S S''
  | permit {S S' S'' : State.TransactionState} : PermitCall C S S' → Calls65 C S' S'' →
      Calls65 C S S''
  | permitBytes65 {S S' S'' : State.TransactionState} : PermitBytes65Call C S S' →
      Calls65 C S' S'' → Calls65 C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → Calls65 C S' S'' →
      Calls65 C S S''

/-- A sequence of `CallsP` is a sequence of `Calls65`. -/
theorem calls65_of_callsP {C : Address} {S S' : State.TransactionState} (h : CallsP C S S') :
    Calls65 C S S' := by
  induction h with
  | nil => exact .nil _
  | call hg _ ih => exact .call hg ih
  | permit hp _ ih => exact .permit hp ih
  | other hu _ ih => exact .other hu ih

/-- `Inv C` along every finite sequence of successful calls to `C`, both `permit` included, the
one with a signature as bytes for 65-byte signatures only, and of changes that keep the storage
of `C`. A successful `permit(bytes)` call with another signature length is not a step of
`Calls65`; it is a step of `CallsAny` (`inv_callsAny`). Each call carries its own hypothesis on
keccak. -/
theorem inv_calls65 {C : Address} {S S' : State.TransactionState}
    (h : Calls65 C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | permit hp _ ih => exact ih (inv_permitCall hp hI)
  | permitBytes65 hp _ ih => exact ih (inv_permitBytes65Call hp hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- From Paris and before Glamsterdam, a top-level `permit` message with a signature of 65 bytes
to `C` (code `CODE`, no value moved, no precompile), run by EthLib's `processMessage`, that ends
with no error, is a `PermitBytes65Call` from its start state to its end state. -/
theorem permitBytes65Call_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    PermitBytes65Call message.currentTarget state ended.val.state := by
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
      s, Nat.le_refl _, rfl, hparis, hglam, hsize, hsel, hlen, hdel, K, start, hres, hse,
      by rw [hend]⟩

/-- From Paris and before Glamsterdam, every top-level message to `C` whose code is `CODE` (no
precompile, call data below 2^256 bytes), run by EthLib's `processMessage` to the end, is a step
of `Calls65 C`: a `GoodCall`, a `PermitCall` or a `PermitBytes65Call` when it ends with no error,
and an `Untouched` step when it ends with an error. Every selector is handled, but not every
message: `hlen` asks that a message with the selector `0x9fd5a6cf` has a signature length word
of 65 (65-byte signatures only; `process_step_any` has no such hypothesis). `K` is the
hypothesis on keccak (not proved); `hdel` is used by the two `permit` only. -/
theorem process_step_sig65 (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hlen : selector message.data = 0x9fd5a6cf →
      loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      PermitCall message.currentTarget state ended.val.state ∨
      PermitBytes65Call message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_fails (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · by_cases hsel0 : selector message.data = 0x9fd5a6cf
      · exact .inr (.inr (.inl (permitBytes65Call_process hparis hglam hmc ht noPrecompile hsize
          hsel0 (hlen hsel0) hdel K hproc herr)))
      · by_cases hsel : selector message.data = 0xd505accf
        · exact .inr (.inl (permitCall_process hparis hglam hmc ht noPrecompile hsize hsel hdel
            K hproc herr))
        · exact .inl (goodCall_process hparis hglam hmc ht noPrecompile hsize hsel0 hsel K hproc herr)
  · exact .inr (.inr (.inr (untouched_process_failed hproc herr _)))

/-- From Paris and before Glamsterdam, a top-level message of `CODE` to `C` that
`processMessage` ends, with any selector (`hlen`: a signature of 65 bytes when the selector is
`0x9fd5a6cf`): `Inv` at its start gives `Inv` at its end. -/
theorem process_step_sig65_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hlen : selector message.data = 0x9fd5a6cf →
      loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state := by
  rcases process_step_sig65 hparis hglam hmc noPrecompile hsize hlen hdel K hproc with
    h | h | h | h
  · exact inv_goodCall h hI
  · exact inv_permitCall h hI
  · exact inv_permitBytes65Call h hI
  · exact inv_untouched h hI

/-- A top-level message of `CODE` to `C` with any selector (`hlen`), then a sequence of steps,
is a sequence of steps. -/
theorem calls65_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {S' : State.TransactionState}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hlen : selector message.data = 0x9fd5a6cf →
      loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : Calls65 message.currentTarget ended.val.state S') :
    Calls65 message.currentTarget state S' := by
  rcases process_step_sig65 hparis hglam hmc noPrecompile hsize hlen hdel K hproc with
    h | h | h | h
  · exact .call h rest
  · exact .permit h rest
  · exact .permitBytes65 h rest
  · exact .other h rest

/-! ## `permit` with a signature of 65 bytes in plain terms over the start state -/

/-- permit(owner, spender, value, deadline, signature) with a signature of 65 bytes, under the
real runner, from Paris and before Glamsterdam. A run that ends with no error passed the checks
of `PermitBytes65Checks` and was not static. Then: nothing is returned; `nonces[owner]` is the old
word plus 1; `allowance[owner][spender]` is `value`; every other slot keeps its word; the logs
are the logs at the start and then exactly one log, Approval(owner, spender, value). This holds
on the signature path and on the ERC-1271 path (which of the two, and what each needs, is in
`ok_permitBytes65_full`). `hsep` is the hypothesis on keccak (not proved); it is used for one
fact, that the allowance slot is not the nonce slot. -/
theorem permitBytes65_readable (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hlen : loadWord message.data (sigPtr message).toNat 32 = (65 : U256))
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytes65Checks message ∧ message.isStatic = false ∧ s.output = ByteArray.empty ∧
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
    permitBytes65_end hparis hglam hsize' hsel hlen hdel start within hrun hok
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

/-! ## Every signature length -/

/-- What the end of the ERC-1271 path of `permit(bytes)` for a length that is not 65 gives, in
the terms of `permitEnd_facts`. -/
theorem permitByContractAny_facts {bound : Nat} {st0 : State.TransactionState} {ss0 : Substate}
    {g0 k : Nat} {s : Evm fork Nat} {dg owner spender value : U256} {sig : ByteArray}
    (h : PermitByContractAny fork bound message st0 ss0 g0 s k dg sig owner spender value) :
    ∃ (st' : State.TransactionState) (ss' : Substate),
      hasAccount st' message.currentTarget ∧
      (∀ n, storageAt st' message.currentTarget n = storageAt st0 message.currentTarget n) ∧
      ss'.logs = ss0.logs ∧ s.output = ByteArray.empty ∧
      s.state = writeSlot st' message.currentTarget (permitAllowKey owner spender) value ∧
      s.substate.logs = ss'.logs.push (Readable.log3 message.currentTarget APPROVAL_TOPIC
        (bitwiseAnd ADDR_MASK owner) (bitwiseAnd spender ADDR_MASK) (wordBytes value)) := by
  obtain ⟨g1, h⟩ := h.kept
  unfold PermitKept PermitWrites at h
  obtain ⟨c, out, st', ss', g', -, -, -, -, hso, -, hlogs, -, -, -, -, hacc, -, hout, -, hst,
    hsub⟩ := h
  exact ⟨st', ss', hacc, fun n => (hso message.currentTarget (by simp)).2.1 _, hlogs, hout,
    hst, by rw [hsub, Readable.logs_logSub, Readable.logs_storeSub]⟩

/-- The end of a `permit` with a signature as bytes of any length that ends with no error, by
any of its paths (ECRECOVER, or ERC-1271 after ECRECOVER, for a length word of 65; ERC-1271
with the bytes as given for another length): the checks, and a state `st'` and a substate `ss'`
(those before the write of the allowance) with the storage of the token as after the write of
the nonce and the logs of the start; the end state is `st'` with the allowance slot written and
the logs are those of `ss'` and then `Approval(owner, spender, value)`. -/
theorem permitBytes_end (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytesChecks message ∧ message.isStatic = false ∧
    hasAccount state message.currentTarget ∧
    ∃ (st' : State.TransactionState) (ss' : Substate),
      hasAccount st' message.currentTarget ∧
      (∀ n, storageAt st' message.currentTarget n =
        storageAt (permitState1 message state) message.currentTarget n) ∧
      ss'.logs = substate.logs ∧ s.output = ByteArray.empty ∧
      s.state = writeSlot st' message.currentTarget
        (permitAllowKey (loadWord message.data 4 32) (loadWord message.data 36 32))
        (loadWord message.data 68 32) ∧
      s.substate.logs = ss'.logs.push (Readable.log3 message.currentTarget APPROVAL_TOPIC
        (bitwiseAnd ADDR_MASK (loadWord message.data 4 32))
        (bitwiseAnd (loadWord message.data 36 32) ADDR_MASK)
        (wordBytes (loadWord message.data 68 32))) := by
  by_cases hlen : sigLen message = (65 : U256)
  · obtain ⟨hchecks, hstatic, hacc, g, rec, hend⟩ :=
      permitBytes65_end hparis hglam hsize' hsel hlen hdel start within hrun hok
    obtain ⟨st', ss', hacc', hsame, hlogs', hout, hst, hlogs⟩ := permitEnd_facts hend
    exact ⟨hchecks.any hlen, hstatic, hacc, st', ss', hacc', hsame, hlogs', hout, hst, hlogs⟩
  · obtain ⟨hchecks, hstatic, hacc, hlay⟩ :=
      ok_permitBytes_other hparis hglam hsize' hsel hlen start within hrun hok
    have key : ∀ {b F : Nat} {domain : U256},
        PermitBytesByContract fork bound message state substate gas s b F domain →
        ∃ (st' : State.TransactionState) (ss' : Substate),
          hasAccount st' message.currentTarget ∧
          (∀ n, storageAt st' message.currentTarget n =
            storageAt (permitState1 message state) message.currentTarget n) ∧
          ss'.logs = substate.logs ∧ s.output = ByteArray.empty ∧
          s.state = writeSlot st' message.currentTarget
            (permitAllowKey (loadWord message.data 4 32) (loadWord message.data 36 32))
            (loadWord message.data 68 32) ∧
          s.substate.logs = ss'.logs.push (Readable.log3 message.currentTarget APPROVAL_TOPIC
            (bitwiseAnd ADDR_MASK (loadWord message.data 4 32))
            (bitwiseAnd (loadWord message.data 36 32) ADDR_MASK)
            (wordBytes (loadWord message.data 68 32))) := by
      intro b F domain h
      obtain ⟨-, -, h⟩ := h
      obtain ⟨st', ss', hacc', hsame, hlogs', hout, hst, hlogs⟩ := permitByContractAny_facts h
      exact ⟨st', ss', hacc', hsame, by rw [hlogs', Readable.logs_storeSub], hout, hst,
        hlogs⟩
    refine ⟨hchecks, hstatic, hacc, ?_⟩
    rcases hlay with ⟨-, h⟩ | ⟨-, h⟩
    · exact key h
    · exact key h

/-- From Paris and before Glamsterdam, under the real runner: a successful `permit` with a
signature as bytes of any length keeps the invariant, by every path. `hsep` is the hypothesis on
keccak (not proved). -/
theorem supply_permitBytes (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
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
  obtain ⟨-, -, hacc, st', ss', hacc', hsame, -, -, hst, -⟩ :=
    permitBytes_end hparis hglam hsize' hsel hdel start within hrun hok
  rw [hst]
  clear hst start hrun hok
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

/-- One run of `permit` with a signature as bytes (of any length) on `CODE` for a message to `C`
that ends with no error, from `S` to `S'`, under the hypotheses of `supply_permitBytes`. -/
def PermitBytesCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .paris ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ selector message.data = 0x9fd5a6cf ∧
    NoDelegation1 fork S ∧
    Sep (callKeys message) ∧
    At CODE message 0 [] .empty gas S substate evm ∧
    Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm within
      = .ok s ∧
    s.error = none ∧ S' = s.state

/-- A `PermitBytes65Call` is a `PermitBytesCall`. -/
theorem PermitBytes65Call.any {C : Address} {S S' : State.TransactionState}
    (h : PermitBytes65Call C S S') : PermitBytesCall C S S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    -, hdel, K, start, hrun, hok, hS⟩ := h
  exact ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    hdel, K, start, hrun, hok, hS⟩

/-- One successful `permit` with a signature as bytes of any length keeps `Inv C`. -/
theorem inv_permitBytesCall {C : Address} {S S' : State.TransactionState}
    (h : PermitBytesCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    hdel, K, start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_permitBytes hparis hglam hsize hsel hdel K hI start within hrun hok

/-- A finite sequence of successful calls to `C` (a function of `GoodCall`, `permit(v, r, s)`,
or `permit` with a signature as bytes of any length) and of changes that keep the storage of
`C`. -/
inductive CallsAny (C : Address) : State.TransactionState → State.TransactionState → Prop
  | nil (S : State.TransactionState) : CallsAny C S S
  | call {S S' S'' : State.TransactionState} : GoodCall C S S' → CallsAny C S' S'' →
      CallsAny C S S''
  | permit {S S' S'' : State.TransactionState} : PermitCall C S S' → CallsAny C S' S'' →
      CallsAny C S S''
  | permitBytes {S S' S'' : State.TransactionState} : PermitBytesCall C S S' →
      CallsAny C S' S'' → CallsAny C S S''
  | other {S S' S'' : State.TransactionState} : Untouched C S S' → CallsAny C S' S'' →
      CallsAny C S S''

/-- A sequence of `Calls65` is a sequence of `CallsAny`. -/
theorem calls65_any {C : Address} {S S' : State.TransactionState} (h : Calls65 C S S') :
    CallsAny C S S' := by
  induction h with
  | nil => exact .nil _
  | call hg _ ih => exact .call hg ih
  | permit hp _ ih => exact .permit hp ih
  | permitBytes65 hp _ ih => exact .permitBytes hp.any ih
  | other hu _ ih => exact .other hu ih

/-- `Inv C` along every finite sequence of successful calls to `C`, both `permit` included (the
one with a signature as bytes for every signature length), and of changes that keep the storage
of `C`. Each call carries its own hypothesis on keccak. -/
theorem inv_callsAny {C : Address} {S S' : State.TransactionState}
    (h : CallsAny C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | permit hp _ ih => exact ih (inv_permitCall hp hI)
  | permitBytes hp _ ih => exact ih (inv_permitBytesCall hp hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- From Paris and before Glamsterdam, a top-level `permit` message with a signature as bytes of
any length to `C` (code `CODE`, no value moved, no precompile), run by EthLib's
`processMessage`, that ends with no error, is a `PermitBytesCall` from its start state to its
end state. -/
theorem permitBytesCall_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noValue : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0))
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hok : ended.val.error = none) :
    PermitBytesCall message.currentTarget state ended.val.state := by
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

/-- From Paris and before Glamsterdam, EVERY top-level message to `C` whose code is `CODE` (no
precompile, call data below 2^256 bytes), run by EthLib's `processMessage` to the end, is a step
of `CallsAny C`: a `GoodCall`, a `PermitCall` or a `PermitBytesCall` when it ends with no error,
and an `Untouched` step when it ends with an error. There is no hypothesis on the selector and
none on the signature: a `permit(bytes)` call of any signature length is covered. `K` is the
hypothesis on keccak (not proved); `hdel` is used by the two `permit` only. -/
theorem process_step_any (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    GoodCall message.currentTarget state ended.val.state ∨
      PermitCall message.currentTarget state ended.val.state ∨
      PermitBytesCall message.currentTarget state ended.val.state ∨
      Untouched message.currentTarget state ended.val.state := by
  by_cases herr : ended.val.error = none
  · by_cases ht : message.shouldTransferValue = true ∧ message.value ≠ 0
    · exact absurd herr (process_value_fails (Nat.le_trans (by decide) hparis) hmc noPrecompile
        hsize ht.2 hproc)
    · by_cases hsel0 : selector message.data = 0x9fd5a6cf
      · exact .inr (.inr (.inl (permitBytesCall_process hparis hglam hmc ht noPrecompile hsize
          hsel0 hdel K hproc herr)))
      · by_cases hsel : selector message.data = 0xd505accf
        · exact .inr (.inl (permitCall_process hparis hglam hmc ht noPrecompile hsize hsel hdel
            K hproc herr))
        · exact .inl (goodCall_process hparis hglam hmc ht noPrecompile hsize hsel0 hsel K hproc herr)
  · exact .inr (.inr (.inr (untouched_process_failed hproc herr _)))

/-- From Paris and before Glamsterdam, a top-level message of `CODE` to `C` that
`processMessage` ends, with any selector and any call data: `Inv` at its start gives `Inv` at
its end. -/
theorem process_step_any_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state := by
  rcases process_step_any hparis hglam hmc noPrecompile hsize hdel K hproc with h | h | h | h
  · exact inv_goodCall h hI
  · exact inv_permitCall h hI
  · exact inv_permitBytesCall h hI
  · exact inv_untouched h hI

/-- A top-level message of `CODE` to `C` with any selector and any call data, then a sequence
of steps, is a sequence of steps. -/
theorem callsAny_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {S' : State.TransactionState}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : CallsAny message.currentTarget ended.val.state S') :
    CallsAny message.currentTarget state S' := by
  rcases process_step_any hparis hglam hmc noPrecompile hsize hdel K hproc with h | h | h | h
  · exact .call h rest
  · exact .permit h rest
  · exact .permitBytes h rest
  · exact .other h rest

/-- permit(owner, spender, value, deadline, signature) with a signature of any length, under the
real runner, from Paris and before Glamsterdam. A run that ends with no error passed the checks
of `PermitBytesChecks` and was not static. Then: nothing is returned; `nonces[owner]` is the
old word plus 1; `allowance[owner][spender]` is `value`; every other slot keeps its word; the
logs are the logs at the start and then exactly one log, Approval(owner, spender, value). This
holds on every path (which one was taken, and what each needs, is in `ok_permitBytes_full`).
`hsep` is the hypothesis on keccak (not proved); it is used for one fact, that the allowance
slot is not the nonce slot. -/
theorem permitBytes_readable (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x9fd5a6cf)
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitBytesChecks message ∧ message.isStatic = false ∧ s.output = ByteArray.empty ∧
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
  obtain ⟨hchecks, hstatic, hacc, st', ss', hacc', hsame', hlogs', hout, hst, hlogs⟩ :=
    permitBytes_end hparis hglam hsize' hsel hdel start within hrun hok
  clear start hrun hok
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
  refine ⟨hchecks, hstatic, hout, ?_, ?_, ?_, ?_⟩
  · rw [hst, storageAt_writeSlot_of_ne hacc' hne, hsame', storageAt_writeSlot_self hacc1]
  · rw [hst, storageAt_writeSlot_self hacc']
  · intro k hk1 hk2
    rw [hst, storageAt_writeSlot_of_ne hacc' hk2, hsame', storageAt_writeSlot_of_ne hacc1 hk1,
      storageAt_readSlot]
  · rw [hlogs, hlogs']

end SkyVerify

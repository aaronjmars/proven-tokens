import UsdeVerify.Usde.Permit
import UsdeVerify.Usde.Seq
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt

/-!
# `permit` keeps the supply invariant, and sequences with `permit`

`Usde/Seq.lean` leaves `permit` out (its `GoodCall` has `selector message.data ≠ 0xd505accf`),
because `supply_preserved` is stated for any runner of child messages and `permit` needs the
real one. This file adds it back, with the hypotheses that `ok_permit_real` needs:
from Paris and before Glamsterdam, and `NoDelegation1 S` (the account at address 1 holds no
EIP-7702 delegation code in the start state).

- `permitDone_facts`: what `PermitDone` says, in one shape: the checks after the call, the end
  state (the nonce write, then the allowance write) and the one log.
- `supply_permit`: a successful `permit` keeps `Inv` (the sum of balances is `totalSupply`),
  under `Sep (callKeys message)`. It changes neither side.
- `PermitCall C S S'`: a successful run of `permit`, with those hypotheses.
- `CallsP C S S'`: a finite sequence of `GoodCall`, `PermitCall` and `Untouched` steps.
  `inv_callsP`: `Inv C` at its start gives `Inv C` at its end. `callsP_of_calls`: a sequence of
  `Calls` is one.
- `permit_readable`: `permit` in plain terms over the start state.
- `process_step_all`: from Paris and before Glamsterdam, every top-level message of `CODE` to
  `C` that `processMessage` ends, with any selector, is one of the three steps.
  `process_step_all_inv`: so `Inv` at its start gives `Inv` at its end.
-/

set_option maxRecDepth 4096

namespace UsdeVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open UsdeVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

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

/-- The owner of a `permit` message: its first argument as an address word. -/
abbrev permitOwner (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 4 32)

/-- The spender of a `permit` message: its second argument as an address word. -/
abbrev permitSpender (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 36 32)

/-- The state from which `permit` writes the allowance: the nonce is incremented and the reads
of the call of ECRECOVER are recorded (they change no storage). -/
abbrev permitS2 (m : Message fork) (S : State.TransactionState) : State.TransactionState :=
  ((permitS1 m S).recordAccountRead (toAddressMasked 1)).recordAccountRead m.currentTarget

/-- The storage of `permitS2` is the storage of `permitS1`. -/
theorem storageAt_permitS2 (m : Message fork) (S : State.TransactionState) (C : Address)
    (k : U256) : storageAt (permitS2 m S) C k = storageAt (permitS1 m S) C k := rfl

/-- What `PermitDone` says, in one shape: the recovered word is not the zero address and is the
owner (both as addresses), the owner and the spender are not 0, the contract has its account,
nothing is returned, the end state is `permitS2` with the allowance written, and the one log. -/
theorem permitDone_facts {gas c : Nat} {s : Evm fork Nat} {D : U256}
    (h : PermitDone fork message state substate gas s D c) :
    bitwiseAnd (permitRec message state D) (1461501637330902918203684832716283019655932542975 : U256) ≠ 0 ∧
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (permitRec message state D) = permitOwner message ∧
    permitOwner message ≠ 0 ∧ permitSpender message ≠ 0 ∧
    hasAccount (permitS2 message state) message.currentTarget ∧
    s.output = ByteArray.empty ∧
    s.state = writeSlot (permitS2 message state) message.currentTarget
      (mapSlot (permitSpender message) (mapSlot (permitOwner message) (3 : U256)))
      (loadWord message.data 68 32) ∧
    s.substate.logs = substate.logs.push (Readable.log3 message.currentTarget (63486140976153616755203102783360879283472101686154884697241723088393386309925 : U256)
      (permitOwner message) (permitSpender message) (wordBytes (loadWord message.data 68 32))) := by
  unfold PermitDone Paths.permitTailC_ends at h
  obtain ⟨-, -, c1, c2, c3, c4, -, hacc, -, hout, -, hst, hsub⟩ := h
  have e2 := Readable.eq_of_equal c2
  simp only [and_mask_comm] at c1 c3 c4 hst hsub
  refine ⟨?_, e2, c3, c4, hacc, hout, hst, ?_⟩
  · rw [and_mask_comm]
    exact c1
  · rw [hsub]

/-- From Paris and before Glamsterdam, under the real runner: a successful `permit` keeps the
invariant. `hsep` is the hypothesis on keccak (not proved). -/
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
  obtain ⟨-, -, -, -, -, -, -, -, hacc0, hend⟩ :=
    ok_permit_real hparis hglam hsize' hsel hdel start within hrun hok
  obtain ⟨-, -, -, -, hacc, -, hst, -⟩ := permitDone_facts hend
  rw [hst]
  clear hst hend start hrun hok
  have hm2 : permitOwner message ∈ callKeys message :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hm3 : permitSpender message ∈ callKeys message :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hacc1 := hasAccount_readSlot (other := message.currentTarget)
    (n := mapSlot (permitOwner message) (9 : U256)) hacc0
  have hA : Inv message.currentTarget (writeSlot
      (readSlot state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
      message.currentTarget (mapSlot (permitOwner message) (9 : U256))
      (add (storageAt state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
        (1 : U256))) := by
    unfold Inv Supply.Inv at hinv ⊢
    rw [D_nonce hsep hm2 hacc1, Supply.D_read]
    exact hinv
  have hS1 : permitS1 message state = writeSlot
      (readSlot state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
      message.currentTarget (mapSlot (permitOwner message) (9 : U256))
      (add (storageAt state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
        (1 : U256)) := by
    simp only [permitS1, nonceSlot, and_mask_comm]
  have hB : Inv message.currentTarget (permitS2 message state) :=
    (Supply.inv_congr (fun n => storageAt_permitS2 message state message.currentTarget n)).mpr
      (hS1 ▸ hA)
  unfold Inv Supply.Inv at hB ⊢
  rw [D_allow hsep hm2 hm3 hacc]
  exact hB

/-- One run of `permit` on `CODE` for a message to `C` that ends with no error, from `S` to
`S'`, under the hypotheses of `supply_permit`. -/
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

/-- One successful `permit` keeps `Inv C`. -/
theorem inv_permitCall {C : Address} {S S' : State.TransactionState}
    (h : PermitCall C S S') (hI : Inv C S) : Inv C S' := by
  obtain ⟨fork, message, substate, gas, bound, evm, s, within, hC, hparis, hglam, hsize, hsel,
    hdel, K, start, hrun, hok, rfl⟩ := h
  subst hC
  exact supply_permit hparis hglam hsize hsel hdel K hI start within hrun hok

/-- A finite sequence of successful calls to `C` (`permit` or any other function) and of changes
that keep the storage of `C`. -/
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

/-- `Inv C` along every finite sequence of successful calls to `C`, `permit` included, and of
changes that keep the storage of `C`. Each call carries its own hypothesis on keccak. -/
theorem inv_callsP {C : Address} {S S' : State.TransactionState}
    (h : CallsP C S S') (hI : Inv C S) : Inv C S' := by
  induction h with
  | nil => exact hI
  | call hg _ ih => exact ih (inv_goodCall hg hI)
  | permit hp _ ih => exact ih (inv_permitCall hp hI)
  | other hu _ ih => exact ih (inv_untouched hu hI)

/-- From Paris and before Glamsterdam, a top-level `permit` message to `C` (code `CODE`, no
value moved, no precompile), run by EthLib's `processMessage`, that ends with no error, is a
`PermitCall` from its start state to its end state. -/
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
precompile, call data below 2^256 bytes, any selector), run by EthLib's `processMessage` to the
end, is a step of `CallsP C`: a `GoodCall` or a `PermitCall` when it ends with no error, and an
`Untouched` step when it ends with an error. `K` is the hypothesis on keccak (not proved);
`hdel` is used by `permit` only. -/
theorem process_step_all (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
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
      · exact .inl (goodCall_process hparis hmc ht noPrecompile hsize hsel K hproc herr)
  · exact .inr (.inr (untouched_process_failed hproc herr _))

/-- From Paris and before Glamsterdam, a top-level message of `CODE` to `C` that
`processMessage` ends, with any selector: `Inv` at its start gives `Inv` at its end. -/
theorem process_step_all_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state := by
  rcases process_step_all hparis hglam hmc noPrecompile hsize hdel K hproc with h | h | h
  · exact inv_goodCall h hI
  · exact inv_permitCall h hI
  · exact inv_untouched h hI

/-- A top-level message of `CODE` to `C` with any selector, then a sequence of steps, is a
sequence of steps. -/
theorem callsP_process (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {S' : State.TransactionState}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hdel : NoDelegation1 fork state)
    (K : Sep (callKeys message))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (rest : CallsP message.currentTarget ended.val.state S') :
    CallsP message.currentTarget state S' := by
  rcases process_step_all hparis hglam hmc noPrecompile hsize hdel K hproc with h | h | h
  · exact .call h rest
  · exact .permit h rest
  · exact .other h rest

/-! ## `permit` in plain terms over the start state -/

/-- permit(owner, spender, value, deadline, v, r, s), under the real runner, from Paris and
before Glamsterdam. Success needs: no value, call data that holds the seven arguments, `owner`
and `spender` given as clean address words, `v` given as one byte, a time stamp of the block not
after the deadline, `s` at most half the order of secp256k1, a frame that may write, the account
of the contract, an owner and a spender that are not 0, and the address that ECRECOVER gives
(not 0) equal to the owner. The digest that is recovered from has the nonce `_nonces[owner]` of
the start state and the domain separator `domainSep message`.

Then: nothing is returned; `_nonces[owner]` is the old word plus 1; `_allowances[owner][spender]`
is `value`; every other slot keeps its word; exactly one log, Approval(owner, spender, value).
`hsep` is the hypothesis on keccak (not proved); it is used for one fact, that the allowance
slot is not the nonce slot. -/
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
    (message.value = 0 ∧ 4 + 224 ≤ message.data.size ∧
      loadWord message.data 4 32 = permitOwner message ∧
      loadWord message.data 36 32 = permitSpender message ∧
      (loadWord message.data 132 32).toNat < 256 ∧
      message.blockEnv.timestamp.toNat ≤ (loadWord message.data 100 32).toNat ∧
      (loadWord message.data 196 32).toNat ≤
        57896044618658097711785492504343953926418782139537452191302581570759080747168 ∧
      message.isStatic = false ∧ hasAccount state message.currentTarget ∧
      permitOwner message ≠ 0 ∧ permitSpender message ≠ 0 ∧
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (permitRec message state (domainSep message)) ≠ 0 ∧
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (permitRec message state (domainSep message)) = permitOwner message) ∧
    (s.output = ByteArray.empty ∧
      storageAt s.state message.currentTarget (mapSlot (permitOwner message) (9 : U256)) =
        add (storageAt state message.currentTarget
          (mapSlot (permitOwner message) (9 : U256))) (1 : U256) ∧
      storageAt s.state message.currentTarget
        (mapSlot (permitSpender message) (mapSlot (permitOwner message) (3 : U256))) =
          loadWord message.data 68 32 ∧
      (∀ k, k ≠ mapSlot (permitOwner message) (9 : U256) →
        k ≠ mapSlot (permitSpender message) (mapSlot (permitOwner message) (3 : U256)) →
        storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      s.substate.logs = substate.logs.push (Readable.log3 message.currentTarget (63486140976153616755203102783360879283472101686154884697241723088393386309925 : U256)
        (permitOwner message) (permitSpender message)
        (wordBytes (loadWord message.data 68 32)))) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨hsize, -, -⟩ := ends_ok_dispatch hberlin hsize' start ⟨within, hrun⟩ hok
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hstat, hacc0, hend⟩ :=
    ok_permit_real hparis hglam hsize' hsel hdel start within hrun hok
  obtain ⟨hr0, hrec, ho, hsp, hacc, hout, hst, hlogs⟩ := permitDone_facts hend
  clear hend start hrun hok
  have hm2 : permitOwner message ∈ callKeys message :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hm3 : permitSpender message ∈ callKeys message :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hne : mapSlot (permitOwner message) (9 : U256) ≠
      mapSlot (permitSpender message) (mapSlot (permitOwner message) (3 : U256)) :=
    fun e => (hsep.nonce _ hm2).2.2 _ hm2 _ hm3 e.symm
  have hacc1 := hasAccount_readSlot (other := message.currentTarget)
    (n := mapSlot (permitOwner message) (9 : U256)) hacc0
  have hS1 : ∀ k, storageAt (permitS2 message state) message.currentTarget k =
      storageAt (writeSlot
        (readSlot state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
        message.currentTarget (mapSlot (permitOwner message) (9 : U256))
        (add (storageAt state message.currentTarget (mapSlot (permitOwner message) (9 : U256)))
          (1 : U256))) message.currentTarget k := by
    intro k
    rw [storageAt_permitS2]
    simp only [permitS1, nonceSlot, and_mask_comm]
  have e3 := Readable.eq_of_equal hc3
  have e4 := Readable.eq_of_equal hc4
  have e5 := Readable.eq_of_equal hc5
  rw [and_mask_comm] at e3 e4
  have h5 : (loadWord message.data 132 32).toNat < 256 := by
    rw [e5]
    unfold bitwiseAnd
    rw [BitVec.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hr0' : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (permitRec message state (domainSep message)) ≠ 0 := by
    rw [and_mask_comm] at hr0
    exact hr0
  refine ⟨⟨Readable.value_of_cond hc1, Readable.size_of_slt hsize hsize' (by decide) hc2,
    e3, e4, h5, Readable.le_of_cond_gt1 hc6, Readable.le_of_cond_gt1 hc7, hstat, hacc0, ho, hsp,
    hr0', hrec⟩, hout, ?_, ?_, ?_, hlogs⟩
  · rw [hst, storageAt_writeSlot_of_ne hacc hne, hS1, storageAt_writeSlot_self hacc1]
  · rw [hst, storageAt_writeSlot_self hacc]
  · intro k hk1 hk2
    rw [hst, storageAt_writeSlot_of_ne hacc hk2, hS1, storageAt_writeSlot_of_ne hacc1 hk1,
      storageAt_readSlot]

end UsdeVerify

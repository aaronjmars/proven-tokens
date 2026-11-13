import DaiVerify.Dai.Permit
import DaiVerify.Dai.Seq
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt

/-!
# `permit` keeps the supply invariant, and sequences with `permit`

`Dai/Seq.lean` leaves `permit` out (its `GoodCall` has `selector message.data ≠ 0x8fcbaf0c`),
because `supply_preserved` is stated for any runner of child messages and `permit` needs the
real one. This file adds it back, with the hypotheses that `ok_permit_real` needs:
from Paris and before Glamsterdam, and `NoDelegation1 S` (the account at address 1 holds no
EIP-7702 delegation code in the start state).

- `permitTail_state`: every way `Paths.permitTail_ends` holds has the same shape of end state:
  a write of the nonce slot of the holder, then a write of the allowance slot.
- `supply_permit`: a successful `permit` keeps `Inv` (the sum of balances is `totalSupply`),
  under `Sep (callKeys message)`. It changes neither side.
- `PermitCall C S S'`: a successful run of `permit`, with those hypotheses.
- `CallsP C S S'`: a finite sequence of `GoodCall`, `PermitCall` and `Untouched` steps.
  `inv_callsP`: `Inv C` at its start gives `Inv C` at its end. `callsP_of_calls`: a sequence of
  `Calls` is one.
- `permitTail_facts`, `permit_readable`: `permit` in plain terms over the start state.
- `process_step_all`: from Paris and before Glamsterdam, every top-level message of `CODE` to
  `C` that `processMessage` ends, with any selector, is one of the three steps.
  `process_step_all_inv`: so `Inv` at its start gives `Inv` at its end.
-/

set_option maxRecDepth 4096

namespace DaiVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open DaiVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

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

/-- The end state of every way `Paths.permitTail_ends` holds: the contract has its account, and
the state is the start state with the nonce slot of the holder written (the nonce plus 1) and
then the allowance slot written. -/
theorem permitTail_state {gas : Nat} {s : Evm fork Nat}
    {dg sS sR sV allowed expiry nonce spender holder sel rec : U256}
    (h : Paths.permitTail_ends fork message state substate gas s dg sS sR sV allowed expiry nonce
      spender holder sel rec) :
    hasAccount state message.currentTarget ∧ ∃ v : U256,
      s.state = writeSlot (writeSlot
        (readSlot state message.currentTarget
          (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder))
            (4 : U256)))
        message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder))
          (4 : U256))
        (add (1 : U256) (storageAt state message.currentTarget
          (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder))
            (4 : U256)))))
        message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) spender))
          (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder))
            (3 : U256))) v := by
  unfold Paths.permitTail_ends at h
  rcases h with ⟨-, -, -, -, -, -, hacc, -, -, -, hst, -⟩ |
    ⟨-, -, -, -, -, -, hacc, -, -, -, hst, -⟩ |
    ⟨-, -, -, -, -, hacc, -, -, -, hst, -⟩ |
    ⟨-, -, -, -, -, hacc, -, -, -, hst, -⟩ <;> exact ⟨hacc, _, hst⟩

/-- From Paris and before Glamsterdam, under the real runner: a successful `permit` keeps the
invariant. `hsep` is the hypothesis on keccak (not proved). -/
theorem supply_permit (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8fcbaf0c)
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
  obtain ⟨-, -, -, -, -, hend⟩ :=
    ok_permit_real hparis hglam hsize' hsel hdel start within hrun hok
  obtain ⟨hacc, v, hst⟩ := permitTail_state hend
  rw [hst]
  clear hst hend start hrun hok
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  have hS1 : Inv message.currentTarget
      (((readSlot state message.currentTarget (5 : U256)).recordAccountRead
        (toAddressMasked 1)).recordAccountRead message.currentTarget) :=
    (Supply.inv_congr (fun n => storageAt_readSlot state message.currentTarget
      message.currentTarget (5 : U256) n)).mpr hinv
  simp only [and_mask_comm, mask_idem] at hacc ⊢
  unfold Inv Supply.Inv at hS1 ⊢
  simp (disch := slot_side) only [Supply.D_read, D_allow hsep, D_nonce hsep]
  exact hS1

/-- One run of `permit` on `CODE` for a message to `C` that ends with no error, from `S` to
`S'`, under the hypotheses of `supply_permit`. -/
def PermitCall (C : Address) (S S' : State.TransactionState) : Prop :=
  ∃ (fork : Fork) (message : Message fork) (substate : Substate) (gas bound : Nat)
    (evm s : Evm fork Nat)
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = C ∧ .paris ≤ fork ∧ fork < .glamsterdam ∧
    message.data.size < 2 ^ 256 ∧ selector message.data = 0x8fcbaf0c ∧ NoDelegation1 fork S ∧
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
    (hsize : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8fcbaf0c)
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
    · by_cases hsel : selector message.data = 0x8fcbaf0c
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

/-- Three ISZERO are one. -/
theorem isZero3 (w : U256) : isZero (isZero (isZero w)) = isZero w := by
  by_cases e : w = 0
  · subst e
    decide
  · have e1 : isZero w = 0 := by unfold isZero; exact if_neg e
    rw [e1]
    decide

/-- A mask of the low byte, twice. -/
theorem and255_idem (w : U256) :
    bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) w) = bitwiseAnd (255 : U256) w := by
  unfold bitwiseAnd
  rw [← BitVec.and_assoc, BitVec.and_self]

/-- What every way `Paths.permitTail_ends` holds says, in one shape: the recovered word is the
holder (both as addresses), the expiry is 0 or not before the time stamp of the block, the nonce
is the one in storage, the frame may write, nothing is returned, and for the word `v` written to
the allowance (0 when `allowed` is 0, else the largest word) the end state and the one log. -/
theorem permitTail_facts {gas : Nat} {s : Evm fork Nat}
    {dg sS sR sV allowed expiry nonce spender holder sel rec : U256}
    (h : Paths.permitTail_ends fork message state substate gas s dg sS sR sV allowed expiry nonce
      spender holder sel rec) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) rec ∧
    (expiry = 0 ∨ message.blockEnv.timestamp.toNat ≤ expiry.toNat) ∧
    nonce = storageAt state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder)) (4 : U256)) ∧
    message.isStatic = false ∧ s.output = ByteArray.empty ∧
    ∃ v : U256, ((allowed = 0 ∧ v = 0) ∨ (allowed ≠ 0 ∧ v = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256))) ∧
      s.state = writeSlot (writeSlot
        (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder)) (4 : U256)))
        message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder)) (4 : U256))
        (add (1 : U256) (storageAt state message.currentTarget
          (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder)) (4 : U256)))))
        message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) spender)) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder)) (3 : U256))) v ∧
      s.substate.logs = substate.logs.push (Readable.log3 message.currentTarget (63486140976153616755203102783360879283472101686154884697241723088393386309925 : U256)
        (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) holder) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) spender) (wordBytes v)) := by
  unfold Paths.permitTail_ends at h
  rcases h with ⟨c1, -, ct, cn, ca, hs, -, -, hout, -, hst, hsub⟩ |
    ⟨c1, -, ct, cn, ca, hs, -, -, hout, -, hst, hsub⟩ |
    ⟨c1, ce, cn, ca, hs, -, -, hout, -, hst, hsub⟩ |
    ⟨c1, ce, cn, ca, hs, -, -, hout, -, hst, hsub⟩
  · exact ⟨Readable.eq_of_equal c1, .inr (Readable.le_of_cond_gt1 ct), Readable.eq_of_equal cn,
      hs, hout, _, .inl ⟨ca, rfl⟩, hst, by rw [hsub]⟩
  · exact ⟨Readable.eq_of_equal c1, .inr (Readable.le_of_cond_gt1 ct), Readable.eq_of_equal cn,
      hs, hout, _, .inr ⟨ca, rfl⟩, hst, by rw [hsub]⟩
  · exact ⟨Readable.eq_of_equal c1, .inl (Readable.value_of_cond ce), Readable.eq_of_equal cn,
      hs, hout, _, .inl ⟨ca, rfl⟩, hst, by rw [hsub]⟩
  · exact ⟨Readable.eq_of_equal c1, .inl (Readable.value_of_cond ce), Readable.eq_of_equal cn,
      hs, hout, _, .inr ⟨ca, rfl⟩, hst, by rw [hsub]⟩

/-- The holder of a `permit` message: its first argument as an address word. -/
abbrev permitHolder (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 4 32)

/-- The spender of a `permit` message: its second argument as an address word. -/
abbrev permitSpender (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 36 32)

/-- The word that ECRECOVER gives for a `permit` message in the state `S`: EthLib's
`Precompiles.Ecrecover.compute` (through `recoveredWord`) on the digest of the domain separator
of storage slot 5 and of the struct hash of the arguments (holder, spender, nonce, expiry, and
`allowed` as 0 or 1), with `v` (its low byte), `r` and `s` of the call data. -/
def permitRecovered (m : Message fork) (S : State.TransactionState) : U256 :=
  recoveredWord (permitInput
    (permitDigest (storageAt S m.currentTarget (5 : U256))
      (permitStruct (permitHolder m) (permitSpender m) (loadWord m.data 68 32)
        (loadWord m.data 100 32) (isZero (isZero (loadWord m.data 132 32)))))
    (bitwiseAnd (255 : U256) (loadWord m.data 164 32))
    (loadWord m.data 196 32) (loadWord m.data 228 32))

/-- permit(holder, spender, nonce, expiry, allowed, v, r, s), under the real runner, from Paris
and before Glamsterdam. Success needs: no value, a nonzero holder, the address that ECRECOVER
gives equal to the holder, an expiry that is 0 or not before the time stamp of the block, the
nonce equal to `nonces[holder]`, and a frame that may write. Then: nothing is returned;
`nonces[holder]` is 1 plus the old word (modulo 2^256: the code does not check this sum); `allowance[holder][spender]` is 0 when `allowed` is 0
and the largest word when it is not; every other slot keeps its word; exactly one log,
Approval(holder, spender, that word). `hsep` is the hypothesis on keccak (not proved); it is
used for one fact, that the allowance slot is not the nonce slot. -/
theorem permit_readable (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x8fcbaf0c)
    (hdel : NoDelegation1 fork state)
    (hsep : Sep (callKeys message))
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    (message.value = 0 ∧ permitHolder message ≠ 0 ∧
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (permitRecovered message state) = permitHolder message ∧
      (loadWord message.data 100 32 = 0 ∨
        message.blockEnv.timestamp.toNat ≤ (loadWord message.data 100 32).toNat) ∧
      loadWord message.data 68 32 =
        storageAt state message.currentTarget (mapSlot (permitHolder message) (4 : U256)) ∧
      message.isStatic = false) ∧
    (s.output = ByteArray.empty ∧
      ∃ v : U256, ((loadWord message.data 132 32 = 0 ∧ v = 0) ∨
          (loadWord message.data 132 32 ≠ 0 ∧ v = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256))) ∧
        storageAt s.state message.currentTarget (mapSlot (permitHolder message) (4 : U256)) =
          add (1 : U256) (storageAt state message.currentTarget
            (mapSlot (permitHolder message) (4 : U256))) ∧
        storageAt s.state message.currentTarget
          (mapSlot (permitSpender message) (mapSlot (permitHolder message) (3 : U256))) = v ∧
        (∀ k, k ≠ mapSlot (permitHolder message) (4 : U256) →
          k ≠ mapSlot (permitSpender message) (mapSlot (permitHolder message) (3 : U256)) →
          storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
        s.substate.logs = substate.logs.push (Readable.log3 message.currentTarget (63486140976153616755203102783360879283472101686154884697241723088393386309925 : U256)
          (permitHolder message) (permitSpender message) (wordBytes v))) := by
  obtain ⟨hc1, -, hc3, -, -, hend⟩ :=
    ok_permit_real hparis hglam hsize' hsel hdel start within hrun hok
  obtain ⟨hacc, -, -⟩ := permitTail_state hend
  obtain ⟨hrec, hexp, hnonce, hstat, hout, v, hv, hst, hlogs⟩ := permitTail_facts hend
  clear hend start hrun hok
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  have hne : mapSlot (permitHolder message) (4 : U256) ≠
      mapSlot (permitSpender message) (mapSlot (permitHolder message) (3 : U256)) :=
    fun e => (hsep.nonce _ hm2).2.2 _ hm2 _ hm3 e.symm
  have hrd : ∀ k, storageAt (((readSlot state message.currentTarget (5 : U256)).recordAccountRead
      (toAddressMasked 1)).recordAccountRead message.currentTarget) message.currentTarget k =
      storageAt state message.currentTarget k :=
    fun k => storageAt_readSlot state message.currentTarget message.currentTarget (5 : U256) k
  simp only [and_mask_comm, mask_idem, isZero3, and255_idem, hrd] at hc3 hrec hnonce hst hlogs hacc
  have hacc1 := hasAccount_readSlot (other := message.currentTarget)
    (n := mapSlot (permitHolder message) (4 : U256)) hacc
  have hacc2 := hasAccount_writeSlot (n := mapSlot (permitHolder message) (4 : U256))
    (v := add (1 : U256) (storageAt state message.currentTarget
            (mapSlot (permitHolder message) (4 : U256)))) hacc1
  have hne0 : permitHolder message ≠ 0 := fun e => hc3 (by
    have e' : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32) = 0 := e
    rw [e']
    decide)
  refine ⟨⟨Readable.value_of_cond hc1, hne0, hrec.symm, hexp, hnonce, hstat⟩, hout, v, ?_, ?_, ?_,
    ?_, hlogs⟩
  · rcases hv with ⟨a, e⟩ | ⟨a, e⟩
    · exact .inl ⟨Readable.zero_of_cond2z a, e⟩
    · exact .inr ⟨Readable.ne_of_cond2z a, e⟩
  · rw [hst, storageAt_writeSlot_of_ne hacc2 hne, storageAt_writeSlot_self hacc1]
  · rw [hst, storageAt_writeSlot_self hacc2]
  · intro k hk1 hk2
    rw [hst, storageAt_writeSlot_of_ne hacc2 hk2, storageAt_writeSlot_of_ne hacc1 hk1,
      storageAt_readSlot, hrd]

end DaiVerify

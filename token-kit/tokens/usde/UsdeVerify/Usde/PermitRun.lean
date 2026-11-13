import UsdeVerify.Usde.Instance
import UsdeVerify.Usde.Sanity.Domain

/-!
# A real `permit` that succeeds (audit 4, fix 6)

Written by hand (not generated). The auditors found that no theorem showed one `permit` call
that ends with no error, so the success paths of `permit` could have been empty. This file gives
that run, with a real secp256k1 signature that EthLib's own `Precompiles.Ecrecover.compute`
checks inside the Lean kernel. Nothing about ECRECOVER is assumed.

The call `m1`: `permit(K, K, 7, 2^256 - 1, v, r, s)` sent by `HOLDER` to the deployed address
`USDE`, in a block with chain id 1 and time stamp 0 (so the code takes the branch of the cached
domain separator), in the state with one account at `USDE` and all-zero storage (the nonce of
`K` is 0). `K` is the address of the private key `0x11...11` (public on purpose). `(v, r, s)`
is the signature of that key over the digest the code builds (nonce `k = 0x22...22`), computed
outside Lean; Lean only checks it.

- `processMessage_precompile_ok`: a message with no value to a precompile never makes
  `processMessage` fail (it gives a frame, with or without an error).
- `ecrecover_call_runs`: the FORWARD rule for `GAS STATICCALL` to address 1 under EthLib's real
  runner `processRunner`: with enough gas the loop of the interpreter goes on from the opcode
  after STATICCALL with 1 pushed and the output of `Ecrecover.compute` written. (The kit had
  only the backward rule.)
- `recovered_m1`: computed by the kernel: ECRECOVER on the digest of this call gives `K`.
- `permit_runs`: THE WITNESS. From 100000 gas the run of `m1` under the real runner ends with
  no error; the allowance of `(K, K)` is then 7 and the nonce of `K` is 1.
- `supply_permit_m1`: the closed instance of `supply_permit` for this call: every hypothesis
  but the fork range and `KeyFacts` (the keccak facts that cannot be proved, `Instance.lean`)
  is discharged, `NoDelegation1` included.
- `permit_runs_inv`: both together: the run exists, and (under `KeyFacts`) it ends in a state
  where the invariant holds.

Not witnessed: the two branches that rebuild the domain separator (another chain id, another
address). Their digest depends on the address or the chain id, so each needs its own signature.

Fork: Paris <= fork < Glamsterdam.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace UsdeVerify.Instance

open UsdtVerify
open TokenKit
open UsdeVerify UsdeVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The forward rule for the call of ECRECOVER -/

/-- A message with no value to a precompile that is not disabled: `processMessage` does not
fail (it gives a frame, which may hold an error). -/
theorem processMessage_precompile_ok {msg : Message fork} {st : State.TransactionState}
    {ss : Substate} {address : Nat}
    (noValue : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0))
    (hpre : precompileAddress fork msg = some address)
    (enabled : msg.disablePrecompiles = false)
    (h : ∃ e, processMessage (Meter := Nat) fork msg st ss = .error e) : False := by
  obtain ⟨e, h⟩ := h
  rw [processMessage] at h
  simp only [Except.map, hpre, noValue, enabled, ite_false, bind, pure, Except.bind,
    Except.pure, Bool.false_eq_true] at h
  split at h <;> rename_i heq
  · split at heq <;> cases heq
  · cases h

set_option linter.deprecated false in
/-- The 63/64 rule for a call with no value and no growth of memory, when the gas left covers
the price `E`: what the message gets and what the caller pays. -/
theorem mcg_facts (htw : Fork.tangerineWhistle ≤ fork) {asked gas E : Nat} (h : E ≤ gas) :
    (messageCallGas fork 0 asked gas 0 E).subCall = min asked (gas - E - (gas - E) / 64) ∧
      (messageCallGas fork 0 asked gas 0 E).cost = min asked (gas - E - (gas - E) / 64) + E := by
  have hc : fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas := ⟨htw, h⟩
  have hs : (messageCallGas fork 0 asked gas 0 E).subCall =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) +
      (if (0 : U256) = 0 then 0 else CALL_STIPEND) := rfl
  have hk : (messageCallGas fork 0 asked gas 0 E).cost =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) + E := rfl
  have hx : maxMessageCallGas (gas - 0 - E) = gas - 0 - E - (gas - 0 - E) / 64 := rfl
  rw [hs, hk, if_pos hc, if_pos (rfl : (0 : U256) = 0), hx]
  simp only [Nat.sub_zero, Nat.add_zero, and_self]

/-- Before Glamsterdam an SSTORE costs at most 22100. -/
theorem writeMax_le (hglam : fork < .glamsterdam) : Gas.writeMax fork ≤ 22100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [Gas.writeMax, hng]

variable {code : ByteArray} {message : Message fork} {pc : Nat} {memory : ByteArray}
  {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- THE FORWARD RULE for `GAS STATICCALL` to address 1, from Paris and before Glamsterdam, under
EthLib's real runner. The frame is at GAS with the address 1 on top and the two ranges inside
the memory; the account at address 1 has the hash of the empty code; the message is below the
depth limit; the frame has at least 5700 gas (2 for GAS, at most 2600 for the access, 3000 for
the precompile and the 64th that stays behind).

Then the loop of the interpreter runs this frame exactly as it runs a frame `after` at the
opcode after STATICCALL, with 1 pushed, the start of the output of `Ecrecover.compute` (on the
bytes of the input range) written to the output range, the two reads recorded in the state,
address 1 accessed, and at most 5602 gas less. -/
theorem ecrecover_call_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    (hlt : pc + 1 < code.size)
    (bg : code[pc]'(by omega) = 0x5a) (bs : code[pc + 1]'hlt = 0xfa)
    (hrest : rest.length + 6 < STACK_LIMIT)
    (hin : inputStart.toNat + inputSize.toNat ≤ memory.size)
    (hout : outputStart.toNat + outputSize.toNat ≤ memory.size)
    (hempty : (state.getAccount (toAddressMasked 1)).codeHash = EMPTY_CODE_HASH)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : 5700 ≤ gas) (hgas' : gas < 2 ^ 256)
    {bound : Nat} {evm : Evm fork Nat}
    (start : At code message pc
      (1 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ after, gas - 5602 ≤ after.gas ∧
      At code message (pc + 2) (1 :: rest)
        (memoryWrite memory outputStart.toNat
          ((Precompiles.Ecrecover.compute
            (memoryReadBytes memory inputStart.toNat inputSize.toNat)).extract 0
            (min outputSize.toNat (Precompiles.Ecrecover.compute
              (memoryReadBytes memory inputStart.toNat inputSize.toNat)).size)))
        after.gas
        ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
            within =
          Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after
            within' := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hnp : ¬fork < Fork.paris := Nat.not_lt.mpr hparis
  have hlim : STACK_LIMIT = 1024 := rfl
  have hE : extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)] =
      ⟨0, 0⟩ := extendMemory_two hin hout
  have hcode : state.getCode (state.getAccount (toAddressMasked 1)).codeHash =
      .ok ByteArray.empty := by
    rw [hempty]
    simp [State.TransactionState.getCode]
  have hroute : Routes fork state ByteArray.empty none :=
    fun _ => Payee.delegatedAddress_empty
  -- GAS
  obtain ⟨a1, hr1, hat1⟩ := At.gas_rule (fork := fork) (show pc < code.size by omega) bg
    (show 2 ≤ gas by omega)
    (by rw [hlim] at hrest ⊢; simp only [List.length_cons]; omega) evm start
  have w1 : GasMeter.gasHeld a1.gas ≤ bound :=
    Nat.le_trans (hr1.gasHeld_le Step.gasHeld_le) within
  have e1 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq hr1 within
  -- the price of the call
  have hcb : callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) ≤
      2600 := by
    rw [callBaseCost_of_berlin hberlin hglam]
    split <;> omega
  have hrc : routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none = 0 :=
    rfl
  have hask : (BitVec.ofNat 256 (gas - 2)).toNat = gas - 2 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hsub, hcost⟩ := mcg_facts (fork := fork) (asked := gas - 2) (gas := gas - 2)
    (E := callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) + 0)
    (Nat.le_trans (by decide) hberlin) (by omega)
  -- STATICCALL
  obtain ⟨a2, hr2, hq⟩ := callKindRoute (kind := .staticcall)
    (callee := Ran (processRunner fork bound)) (asked := BitVec.ofNat 256 (gas - 2))
    (to := 1) (inputStart := inputStart) (inputSize := inputSize)
    (outputStart := outputStart) (outputSize := outputSize) (rest := rest)
    (returnData := a1.returnData) (route := none) (calleeCode := ByteArray.empty)
    hberlin hlt bs
    (ofByte_of_decode (op := .staticcall) rfl (Nat.le_trans (by decide) hberlin))
    instruction_staticcall
    (messageInstruction_staticcall (Nat.le_trans (by decide) hberlin))
    hcode hroute hdepth
    (by rw [hE, hrc]; show _ + 0 + 0 ≤ gas - 2; omega)
    bound (processRunner fork bound) (meetsOk_ran _) a1 hat1.toLogic w1
  have w2 : GasMeter.gasHeld a2.gas ≤ bound :=
    Nat.le_trans (hr2.gasHeld_le StepBy.gasHeld_le) w1
  have e2 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    StepBy.gasHeld_le StepBy.runFrame_eq hr2 w1
  rcases hq with ⟨caller, msg, child, hsend, hran, -, hat2⟩ | hfail
  · obtain ⟨cs, css, cgas, -, -, -, ctarget, cca, -, cdis, cdata, cvalue, -⟩ := hsend
    rw [hE, hrc, hask] at cgas
    rw [hE] at cdata hat2
    rw [hrc, hask] at hat2
    simp only [memoryExtend_zero] at cdata hat2
    have cgas' : msg.gas = min (gas - 2) (gas - 2 -
        (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) + 0) -
        (gas - 2 -
          (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) + 0)) /
          64) := cgas.trans hsub
    have hm := Nat.min_le_right (gas - 2) (gas - 2 -
        (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) + 0) -
        (gas - 2 -
          (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) + 0)) /
          64)
    have hm3 : 3000 ≤ msg.gas := by
      rw [cgas']
      exact Nat.le_min.mpr ⟨by omega, by omega⟩
    rcases ecrecover_ran hran ctarget cca cdis (by rw [cvalue]; rfl) with
      ⟨hlow, -⟩ | ⟨-, herr, hstate, hsub', hout', hcg⟩
    · omega
    · have hflag : (if child.error.isNone then (1 : U256) else 0) = 1 := by rw [herr]; rfl
      obtain ⟨istate, isub⟩ := incorporateChild_precompile hparis herr hsub'
      have hstart : startState fork msg caller.state = caller.state := by
        simp only [startState, hnp, ite_false]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hat2
      refine ⟨a2, ?_, ⟨h1, h2, h3, h4, by rw [h5, hflag], ?_, rfl, h8, h9, h10, ?_, ?_⟩, w2,
        e1.trans e2⟩
      · rw [h7, hcost, hcg, ← cgas.trans hsub]
        omega
      · rw [h6, hout', cdata]
      · rw [h11, istate, hstate, hstart, cs]
        rfl
      · rw [h12, isub, css]
        rfl
  · obtain ⟨-, caller, msg, resume, -, hsend, lt, e, herr⟩ := hfail
    obtain ⟨-, -, -, -, -, -, ctarget, cca, -, cdis, -, cvalue, -⟩ := hsend
    have hp : processRunner fork bound caller msg lt =
        processMessage fork msg caller.state caller.substate.child := by
      simp only [processRunner, ctarget]
    rw [hp] at herr
    exact (processMessage_precompile_ok (fun h => h.2 (by rw [cvalue]; rfl))
      (precompileAddress_one cca) cdis ⟨e, herr⟩).elim

/-! ## The call -/

/-- The call data of `permit(K, K, 7, 2^256 - 1, v, r, s)`: the selector `0xd505accf` and seven
words. `v = 27`, and `r`, `s` are the words of `sigR`, `sigS` below. -/
def permitData : ByteArray := ⟨#[
    213, 5, 172, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 231, 227, 118, 231, 194, 19, 183,
    231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    25, 231, 227, 118, 231, 194, 19, 183, 231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255,
    42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 7, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 70, 109, 127,
    202, 229, 99, 229, 203, 9, 160, 209, 135, 11, 181, 128, 52, 72, 4, 97, 120, 121, 161, 73, 73,
    207, 34, 40, 95, 27, 174, 63, 39, 50, 206, 83, 166, 16, 77, 186, 95, 21, 235, 142, 106, 207,
    86, 20, 64, 187, 255, 91, 7, 102, 133, 217, 26, 130, 240, 174, 154, 105, 42, 21, 132]⟩

/-- `r` of the signature. -/
abbrev sigR : U256 := 31855367722742370537280679280108010854876607759940877706949385967087672770343

/-- `s` of the signature. -/
abbrev sigS : U256 := 22980190246522569071124655846125347551271052147343720977696294916619248473476

/-- The block `b` with the chain id 1 and the time stamp 0. -/
abbrev atBlock (b : BlockEnvironment fork) : BlockEnvironment fork :=
  { b with chainId := 1, timestamp := 0 }

/-- The call `permit(K, K, 7, 2^256 - 1, 27, sigR, sigS)` from `HOLDER` to the deployed address
`USDE`, in the block `atBlock b`. -/
abbrev m1 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) : Message fork :=
  sMsg (atBlock b) t USDE HOLDER CODE permitData

theorem size_permitData : permitData.size = 228 := by decide +kernel

theorem selector_permitData : selector permitData = 0xd505accf := by decide +kernel

theorem arg1_permitData : loadWord permitData 4 32 = K := by decide +kernel

theorem arg2_permitData : loadWord permitData 36 32 = K := by decide +kernel

theorem arg3_permitData : loadWord permitData 68 32 = (7 : U256) := by decide +kernel

theorem arg4_permitData : loadWord permitData 100 32 =
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) := by
  decide +kernel

theorem arg5_permitData : loadWord permitData 132 32 = (27 : U256) := by decide +kernel

theorem arg6_permitData : loadWord permitData 164 32 = sigR := by decide +kernel

theorem arg7_permitData : loadWord permitData 196 32 = sigS := by decide +kernel

/-- The mapping keys of the call `m1` are the one word `K`, three times. -/
theorem callKeys_m1 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) :
    callKeys (m1 b t) = [K, K, K] := by
  have hc : (m1 b t).caller.toU256 = K := holder_toU256
  have h1 : loadWord (m1 b t).data 4 32 = K := arg1_permitData
  have h2 : loadWord (m1 b t).data 36 32 = K := arg2_permitData
  have hm : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) K = K := by
    decide
  unfold callKeys
  rw [hc, h1, h2, hm]

/-- COMPUTED BY THE KERNEL, with EthLib's own secp256k1 recovery and keccak: ECRECOVER on the
digest that the code builds for this call (the cached domain separator, the struct hash of
`(K, K, 7, nonce 0, deadline 2^256 - 1)`) and on `(27, sigR, sigS)` gives the address word
`K`. -/
theorem recovered_m1 :
    recoveredWord (permitInput (permitDigest CACHED_DOMAIN (permitStruct K K 7 0
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256)))
      27 sigR sigS) = K := by
  decide +kernel

/-- A read of an account leaves the storage words as they are. -/
theorem storageAt_recordAccountRead (S : State.TransactionState) (a C : Address) (n : U256) :
    storageAt (S.recordAccountRead a) C n = storageAt S C n := rfl

/-- A read of an account leaves the accounts as they are. -/
theorem hasAccount_recordAccountRead {S : State.TransactionState} {C : Address} (a : Address)
    (h : hasAccount S C) : hasAccount (S.recordAccountRead a) C := h

/-! ## The witness -/

set_option maxHeartbeats 4000000 in
/-- THE WITNESS for `permit`, from Paris and before Glamsterdam, under EthLib's real runner
(the precompile ECRECOVER is run, not assumed). The call `m1` from the state with all-zero
storage, with 100000 gas, for every substate and every bound of at least 100000: the loop of
the interpreter ends in a frame `s` with no error. In its state the allowance of `(K, K)` is
7 and the nonce of `K` is 1. -/
theorem permit_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t) 0 [] .empty 100000 (sState USDE []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧
      storageAt s.state USDE (mapSlot K (mapSlot K 3)) = (7 : U256) ∧
      storageAt s.state USDE (mapSlot K 9) = (1 : U256) := by
  have hparis' : Fork.paris ≤ fork := Nat.le_trans (by decide) hparis
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis'
  have hsz : (m1 b t).data.size = 228 := size_permitData
  have hsl : selector (m1 b t).data = 0xd505accf := selector_permitData
  have hA1 : loadWord (m1 b t).data 4 32 = K := arg1_permitData
  have hA2 : loadWord (m1 b t).data 36 32 = K := arg2_permitData
  have hA3 : loadWord (m1 b t).data 68 32 = (7 : U256) := arg3_permitData
  have hA4 : loadWord (m1 b t).data 100 32 =
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) :=
    arg4_permitData
  have hA5 : loadWord (m1 b t).data 132 32 = (27 : U256) := arg5_permitData
  have hA6 : loadWord (m1 b t).data 164 32 = sigR := arg6_permitData
  have hA7 : loadWord (m1 b t).data 196 32 = sigS := arg7_permitData
  have hval : (m1 b t).value = 0 := rfl
  have hct : (m1 b t).currentTarget = USDE := rfl
  have hcw : (m1 b t).currentTarget.toU256 = (437426098194082895061803372304124391670360729779 : U256) :=
    usde_toU256
  have hch : (m1 b t).blockEnv.chainId.toNat = 1 := rfl
  have hts : (m1 b t).blockEnv.timestamp = 0 := rfl
  have hacc : hasAccount (sState USDE []) USDE := hasAccount_sState USDE _
  have wc : ∀ o c n cold, Gas.writeCost fork o c n cold ≤ 22100 := fun o c n cold =>
    Nat.le_trans (Gas.writeCost_le hberlin o c n cold) (writeMax_le hglam)
  -- the code before the call (the branch of the cached domain separator)
  have hpre := Paths.permit_p8 (fork := fork) (message := m1 b t) (state := sState USDE [])
    (substate := ss) (gas := 100000) hberlin
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    hsl
    rfl
    hacc
    (by rw [hval]; decide)
    (by rw [hsz]; decide)
    (by rw [hA1]; decide +kernel)
    (by rw [hA2]; decide +kernel)
    (by rw [hA5]; decide +kernel)
    (by rw [hts, hA4]; decide +kernel)
    (by rw [hcw]; decide +kernel)
    (by rw [hch]; decide +kernel)
    (by rw [hA7]; decide +kernel)
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.add_lt_add_of_le_of_lt
      (Nat.add_le_add_left (_root_.UsdtVerify.slotCost_le _) _)
      (Nat.lt_succ_of_le (wc _ _ _ _))) _) (by decide))
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m1 b t) (sState USDE []) ss 100000)
    (at_sFrame _ rfl _ _ _)
  have within : GasMeter.gasHeld (sFrame (m1 b t) (sState USDE []) ss 100000).gas ≤ bound := hb
  have w0 : GasMeter.gasHeld z.gas ≤ bound :=
    Nat.le_trans ((hrz.mono And.left).gasHeld_le Step.gasHeld_le) within
  have e0 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq (hrz.mono And.left) within
  obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, m352, m384, m416, m448, m480⟩ :=
    Paths.permit_p8_mem (message := m1 b t) (state := sState USDE [])
  have t384 : (384 : U256).toNat = 384 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t352 : (352 : U256).toNat = 352 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  -- the call
  obtain ⟨a, hga, hat, w2, e2⟩ := ecrecover_call_runs hparis' hglam (pc := 6035)
    (by code_fact) (by code_fact) (by code_fact) (by simp [STACK_LIMIT])
    (by rw [msz]; decide) (by rw [msz]; decide)
    (by rw [getAccount_writeSlot]; exact codeHash_sState USDE [] _)
    (by show (0 : Nat) + 1 ≤ STACK_DEPTH_LIMIT; decide)
    (by
      refine Nat.le_trans ?_ (Nat.sub_le_sub_left (Nat.add_le_add (Nat.add_le_add_left
        (_root_.UsdtVerify.slotCost_le _) _) (wc _ _ _ _)) _)
      decide)
    (by omega) hz w0
  have hga' : 60000 ≤ a.gas := by
    refine Nat.le_trans (Nat.le_trans ?_ (Nat.sub_le_sub_right (Nat.sub_le_sub_left
      (Nat.add_le_add (Nat.add_le_add_left (_root_.UsdtVerify.slotCost_le _) _)
        (wc _ _ _ _)) _) _)) hga
    decide
  simp only [t384, t128, t352, t32] at hat
  rw [read4_raw m384 m416 m448 m480 msz (by decide)] at hat
  have hfit' : ∀ {M : ByteArray}, M.size = 512 → 352 + 32 ≤ M.size := fun h => by
    rw [h]; decide
  have hfit := hfit' msz
  have hS1 : hasAccount (writeSlot (readSlot (sState USDE []) USDE (mapSlot (bitwiseAnd K
      (1461501637330902918203684832716283019655932542975 : U256)) (9 : U256))) USDE
      (mapSlot (bitwiseAnd K (1461501637330902918203684832716283019655932542975 : U256))
        (9 : U256)) (add (storageAt (sState USDE []) USDE (mapSlot (bitwiseAnd K
          (1461501637330902918203684832716283019655932542975 : U256)) (9 : U256))) (1 : U256)))
      USDE := hasAccount_writeSlot (hasAccount_readSlot hacc)
  -- the code after the call
  obtain ⟨s, hs, hH⟩ := SpecG.runFrame (Paths.permitTailC_p5 (fork := fork) hberlin
    ((size_ecrecover_write _ hfit).trans msz)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans m64)
    (load_ecrecover _ hfit m352)
    (rfl : (m1 b t).isStatic = false)
    (by
      simp only [hA1, hct]
      exact hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _ hS1))
    (by
      rw [digest_bytes_352 (ws := _) (by rfl) (memW_load 11 (by rfl) (by rfl) (by rfl))]
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hct, storageAt_sState_nil]
      decide +kernel)
    (by
      rw [digest_bytes_352 (ws := _) (by rfl) (memW_load 11 (by rfl) (by rfl) (by rfl))]
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hct, storageAt_sState_nil]
      decide +kernel)
    (by rw [hA1]; decide +kernel)
    (by rw [hA2]; decide +kernel)
    (gas := a.gas)
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_right
      (Nat.add_lt_add_left (Nat.lt_succ_of_le (wc _ _ _ _)) _) _) (by omega))) hat w2
  obtain ⟨-, he, -, -, hst, -⟩ := hH
  refine ⟨_, s, within, at_sFrame _ rfl _ _ _, e0.trans (e2.trans hs), by simpa using he, ?_, ?_⟩
  · rw [hst]
    simp only [hA1, hA2, hA3, hct]
    simp only [storageAt_sState_nil]
    decide +kernel
  · rw [hst]
    simp only [hA1, hA2, hA3, hct]
    simp only [storageAt_sState_nil]
    decide +kernel

/-! ## The closed instance of `supply_permit` -/

/-- THE CLOSED INSTANCE of `supply_permit`: the call `m1` from the state with all-zero storage.
Every run under the real runner that ends with no error ends in a state where the invariant
holds. The start invariant, `NoDelegation1`, the size of the call data and the selector are
discharged; the only hypotheses left are the fork range and `KeyFacts`. -/
theorem supply_permit_m1 (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (keys : KeyFacts)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    {substate : Substate} {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE (m1 b t) 0 [] .empty gas (sState USDE []) substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv USDE s.state := by
  have hsz : (m1 b t).data.size = 228 := size_permitData
  have hsl : selector (m1 b t).data = 0xd505accf := selector_permitData
  have hsep : Sep (callKeys (m1 b t)) := by
    rw [callKeys_m1]
    exact sep_iff.mpr keys
  exact supply_permit hparis hglam (by rw [hsz]; decide) hsl (noDelegation1_sState USDE [])
    hsep (inv_start USDE) start within hrun hok

/-- The run of `permit_runs` exists and, under `KeyFacts`, ends in a state where the invariant
holds: the success case of `supply_permit` is not empty. -/
theorem permit_runs_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (keys : KeyFacts)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t) 0 [] .empty 100000 (sState USDE []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧ Inv USDE s.state := by
  obtain ⟨evm, s, within, start, hrun, hok, -, -⟩ := permit_runs hparis hglam b t ss hb
  exact ⟨evm, s, within, start, hrun, hok,
    supply_permit_m1 hparis hglam keys b t start within hrun hok⟩

end UsdeVerify.Instance

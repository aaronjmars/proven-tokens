import SkyVerify.Sky.Instance

/-!
# A real `permit` that succeeds (audit 4, fix 6, SKY-5)

Written by hand (not generated). The auditors found that no theorem showed one `permit` call
that ends with no error, so the success paths of `permit` could have been empty. This file gives
that run, with a real secp256k1 signature that EthLib's own `Precompiles.Ecrecover.compute`
checks inside the Lean kernel. Nothing about ECRECOVER is assumed.

The call `m1`: `permit(SIGNER, SIGNER, 1000, 2^256 - 1, 27, sigR, sigS)` sent by
`Witness.CALLER1` to `C`, in a block with chain id 1 (the code then uses the domain separator
that it holds as a constant, so the digest does not depend on `C`), in the state with one
account at `C` and all-zero storage (the nonce of `SIGNER` is 0). `SIGNER` is the address of the
private key `0x11...11` (public on purpose). `(27, sigR, sigS)` is the signature of that key
over the digest the code builds (nonce `k = 0x22...22`), computed outside Lean; Lean only
checks it.

- `processMessage_precompile_ok`, `mcg_facts`, `writeMax_le`, `ecrecover_call_runs`: the FORWARD
  rule for `GAS STATICCALL` to address 1 under EthLib's real runner `processRunner`: with enough
  gas the loop of the interpreter goes on from the opcode after STATICCALL with 1 pushed and
  the output of `Ecrecover.compute` written. (The kit has only the backward rule
  `ecrecover_call_ok`. These four are the same text as in `tokens/dai/.../PermitRun.lean`,
  written by part close-e; they should move to the kit.)
- `permit_runs`: THE WITNESS. From 100000 gas the run of `m1` under the real runner ends with
  no error; the allowance of `(SIGNER, SIGNER)` is then 1000 and the nonce of `SIGNER` is 1.
  It is the signature way of `permit(v, r, s)` (ECRECOVER gives the owner). No witness is given
  for the ERC-1271 way (the owner is a contract that answers) or for `permit(bytes)`.
- `permit_runs_inv`: the run exists and, under the keccak hypothesis `Sep` of this call (not
  proved), it ends in a state where the invariant holds: the success case of `supply_permit`
  is not empty.

Fork: Paris <= fork < Glamsterdam.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace SkyVerify.Instance

open UsdtVerify
open TokenKit
open SkyVerify SkyVerify.Sanity

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

/-- The address word of the private key `0x11...11`. -/
abbrev SIGNER : U256 := 0x19e7e376e7c213b7e7e7e46cc70a5dd086daff2a

/-- The call data of `permit(SIGNER, SIGNER, 1000, 2^256 - 1, 27, sigR, sigS)`: 228 bytes. -/
def permitData : ByteArray := ⟨#[
    213, 5, 172, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 231, 227, 118, 231, 194, 19, 183,
    231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    25, 231, 227, 118, 231, 194, 19, 183, 231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255,
    42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    3, 232, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 70, 109, 127,
    202, 229, 99, 229, 203, 9, 160, 209, 135, 11, 181, 128, 52, 72, 4, 97, 120, 121, 161, 73, 73,
    207, 34, 40, 95, 27, 174, 63, 39, 13, 255, 166, 112, 32, 145, 107, 242, 79, 32, 147, 181,
    115, 52, 138, 65, 31, 33, 151, 45, 45, 26, 182, 168, 33, 70, 94, 93, 58, 0, 30, 98]⟩

/-- `r` of the signature. -/
abbrev sigR : U256 := 31855367722742370537280679280108010854876607759940877706949385967087672770343

/-- `s` of the signature. -/
abbrev sigS : U256 := 6331761745938361344323600105393760440747667267279728451886013155447280770658

/-- The largest word: the deadline of the call. -/
abbrev MAXW : U256 :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- The call `permit(SIGNER, SIGNER, 1000, 2^256 - 1, 27, sigR, sigS)` from `Witness.CALLER1`
to `C`. -/
abbrev m1 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    Message fork :=
  sMsg b t C Witness.CALLER1 CODE permitData

theorem size_permitData : permitData.size = 228 := by decide +kernel

theorem selector_permitData : selector permitData = 0xd505accf := by decide +kernel

theorem arg1_permitData : loadWord permitData 4 32 = SIGNER := by decide +kernel

theorem arg2_permitData : loadWord permitData 36 32 = SIGNER := by decide +kernel

theorem arg3_permitData : loadWord permitData 68 32 = (1000 : U256) := by decide +kernel

theorem arg4_permitData : loadWord permitData 100 32 = MAXW := by decide +kernel

theorem arg5_permitData : loadWord permitData 132 32 = (27 : U256) := by decide +kernel

theorem arg6_permitData : loadWord permitData 164 32 = sigR := by decide +kernel

theorem arg7_permitData : loadWord permitData 196 32 = sigS := by decide +kernel

/-- No time stamp is after the deadline `2^256 - 1`. -/
theorem deadline_ok (x : U256) : isZero (greaterThan x MAXW) ≠ 0 := by
  have hm : (MAXW).toNat = 2 ^ 256 - 1 := by decide
  have hx : x.toNat < 2 ^ 256 := x.isLt
  have h0 : greaterThan x MAXW = 0 := by
    unfold greaterThan
    split
    · omega
    · rfl
  rw [h0]
  decide

/-- A read of an account leaves the storage words as they are. -/
theorem storageAt_recordAccountRead (S : State.TransactionState) (a C : Address) (n : U256) :
    storageAt (S.recordAccountRead a) C n = storageAt S C n := rfl

/-- A read of an account leaves the accounts as they are. -/
theorem hasAccount_recordAccountRead {S : State.TransactionState} {C : Address} (a : Address)
    (h : hasAccount S C) : hasAccount (S.recordAccountRead a) C := h

/-! ## The witness -/

set_option maxHeartbeats 4000000 in
/-- THE WITNESS for `permit(v, r, s)`, from Paris and before Glamsterdam, under EthLib's real
runner (the precompile ECRECOVER is run, not assumed). The call `m1` in a block with chain id 1,
from the state with all-zero storage, with 100000 gas, for every substate and every bound of at
least 100000: the loop of the interpreter ends in a frame `s` with no error. In its state the
allowance of `(SIGNER, SIGNER)` is 1000 and the nonce of `SIGNER` is 1. -/
theorem permit_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hchain : b.chainId = 1) (t : TransactionEnvironment fork)
    (C : Address) (ss : Substate) {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t C) 0 [] .empty 100000 (sState C []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧
      storageAt s.state C (mapSlot SIGNER (mapSlot SIGNER 3)) = (1000 : U256) ∧
      storageAt s.state C (mapSlot SIGNER 4) = (1 : U256) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz : (m1 b t C).data.size = 228 := size_permitData
  have hsl : selector (m1 b t C).data = 0xd505accf := selector_permitData
  have hA1 : loadWord (m1 b t C).data 4 32 = SIGNER := arg1_permitData
  have hA2 : loadWord (m1 b t C).data 36 32 = SIGNER := arg2_permitData
  have hA3 : loadWord (m1 b t C).data 68 32 = (1000 : U256) := arg3_permitData
  have hA4 : loadWord (m1 b t C).data 100 32 = MAXW := arg4_permitData
  have hA5 : loadWord (m1 b t C).data 132 32 = (27 : U256) := arg5_permitData
  have hA6 : loadWord (m1 b t C).data 164 32 = sigR := arg6_permitData
  have hA7 : loadWord (m1 b t C).data 196 32 = sigS := arg7_permitData
  have hval : (m1 b t C).value = 0 := rfl
  have hct : (m1 b t C).currentTarget = C := rfl
  have hts : (m1 b t C).blockEnv = b := rfl
  have hacc : hasAccount (sState C []) C := hasAccount_sState C _
  have wc : ∀ o c n cold, Gas.writeCost fork o c n cold ≤ 22100 := fun o c n cold =>
    Nat.le_trans (Gas.writeCost_le hberlin o c n cold) (writeMax_le hglam)
  have hcost : permitCost1 1811 fork (m1 b t C) (sState C []) ss ≤ 1811 + 2100 + 22100 :=
    Nat.add_le_add (Nat.add_le_add_left (_root_.UsdtVerify.slotCost_le _) _) (wc _ _ _ _)
  -- the code before the call
  have hpre := Paths.permit_p9 (fork := fork) (message := m1 b t C) (state := sState C [])
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
    (by rw [hA4]; exact deadline_ok _)
    (by rw [hA1]; decide +kernel)
    (by rw [hts, hchain]; decide)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right hcost 2300) (by decide))
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m1 b t C) (sState C []) ss 100000)
    (at_sFrame _ rfl _ _ _)
  have within : GasMeter.gasHeld (sFrame (m1 b t C) (sState C []) ss 100000).gas ≤ bound := hb
  have w0 : GasMeter.gasHeld z.gas ≤ bound :=
    Nat.le_trans ((hrz.mono And.left).gasHeld_le Step.gasHeld_le) within
  have e0 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq (hrz.mono And.left) within
  obtain ⟨m0, m64, -, -, w96, w128, w160, w192, -, -, -, -, -, -, -, -, -, -, w547, w579,
    w611, w643, w675, t224, -⟩ :=
    Paths.permit_p9_mem (message := m1 b t C) (state := sState C [])
  have t579 : (579 : U256).toNat = 579 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t547 : (547 : U256).toNat = 547 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hz' : At CODE (m1 b t C) 3501 _ _
      (100000 - permitCost1 1811 fork (m1 b t C) (sState C []) ss) _ _ z := hz
  have hS1 : hasAccount (permitState1 (m1 b t C) (sState C [])) C :=
    hasAccount_writeSlot (hasAccount_readSlot hacc)
  -- the call
  obtain ⟨a, hga, hat, w2, e2⟩ := ecrecover_call_runs hparis hglam (pc := 3501)
    (by code_fact) (by code_fact) (by code_fact) (by simp [STACK_LIMIT])
    (by rw [m0]; decide) (by rw [m0]; decide)
    (by rw [getAccount_writeSlot, getAccount_readSlot]; exact codeHash_sState C [] _)
    (by show (0 : Nat) + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) (by omega) hz' w0
  simp only [t579, t128, t547, t32] at hat
  rw [read4_raw w579 w611 w643 w675 m0 (by decide)] at hat
  have hfit' : ∀ {M : ByteArray}, M.size = 736 → 547 + 32 ≤ M.size := fun h => by
    rw [h]; decide
  have hfit := hfit' m0
  have hS2 : hasAccount (((permitState1 (m1 b t C) (sState C [])).recordAccountRead
      (toAddressMasked 1)).recordAccountRead C) C :=
    hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _ hS1)
  -- the code after the call
  obtain ⟨s, hs, hH⟩ := SpecG.runFrame (Paths.permitRecA_p1 (fork := fork) hberlin
    ((size_ecrecover_write _ hfit).trans m0)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans m64)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans w96)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans w128)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans w160)
    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans w192)
    (load_ecrecover _ hfit w547)
    (top_same (fun _ _ hd => read_ecrecover_other _ hfit hd) (size_ecrecover_write _ hfit) t224
      (.inl (by decide)) (by rw [m0]; decide))
    (rfl : (m1 b t C).isStatic = false)
    hS2
    (by
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hct, storageAt_sState_nil]
      decide +kernel)
    (gas := a.gas)
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.add_lt_add_left
      (Nat.lt_succ_of_le (wc _ _ _ _)) 2190) 2300) (by omega))) hat w2
  obtain ⟨-, he, -, -, hst, -⟩ := hH
  refine ⟨_, s, within, at_sFrame _ rfl _ _ _, e0.trans (e2.trans hs), by simpa using he, ?_, ?_⟩
  · rw [hst]
    simp (disch := first
        | exact hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _
            (hasAccount_writeSlot (hasAccount_readSlot hacc)))
        | exact hasAccount_readSlot hacc) only
      [permitState1, permitNonceKey, permitOwner, hA1, hA2, hA3, hct,
        storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil]
    decide +kernel
  · rw [hst]
    simp (disch := first
        | exact hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _
            (hasAccount_writeSlot (hasAccount_readSlot hacc)))
        | exact hasAccount_readSlot hacc) only
      [permitState1, permitNonceKey, permitOwner, hA1, hA2, hA3, hct,
        storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil]
    decide +kernel

set_option maxHeartbeats 2000000 in
/-- The run of `permit_runs` exists and, under the keccak hypothesis `Sep` of this call (not
proved), ends in a state where the invariant holds: the success case of `supply_permit` is not
empty. The start invariant, `NoDelegation1`, the size of the call data and the selector are
discharged. -/
theorem permit_runs_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hchain : b.chainId = 1) (t : TransactionEnvironment fork)
    (C : Address) (hsep : Sep (callKeys (m1 b t C))) (ss : Substate)
    {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t C) 0 [] .empty 100000 (sState C []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧ Inv C s.state := by
  obtain ⟨evm, s, within, start, hrun, hok, -, -⟩ := permit_runs hparis hglam b hchain t C ss hb
  have hsz : (m1 b t C).data.size = 228 := size_permitData
  exact ⟨evm, s, within, start, hrun, hok,
    supply_permit (message := m1 b t C) (state := sState C []) hparis hglam
      (by rw [hsz]; decide) selector_permitData
      (noDelegation1_sState C []) hsep (inv_start C) start within hrun hok⟩

end SkyVerify.Instance

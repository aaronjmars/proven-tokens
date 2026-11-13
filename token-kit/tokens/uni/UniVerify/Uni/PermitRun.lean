import UniVerify.Uni.Instance

/-!
# A real `permit` and a real `delegateBySig` that succeed (audit 4, fix 6, UNI-3)

Written by hand (not generated). The auditors found that no theorem showed one `permit` or one
`delegateBySig` call that ends with no error, so their success paths could have been empty. This
file gives one such run of each, with a real secp256k1 signature that EthLib's own `Precompiles.Ecrecover.compute`
checks inside the Lean kernel. Nothing about ECRECOVER is assumed.

The call `m1`: `permit(SIGNER, SIGNER, 2^256 - 1, 2^256 - 1, 27, sigR, sigS)` sent by
`Witness.CALLER1` to the address `C0` (the address of UNI on mainnet: the code puts its own
address into the digest, so the witness needs one fixed address), in a block with chain id 1,
in the state with one account at `C0` and all-zero storage (the nonce of `SIGNER` is 0).
`SIGNER` is the address of the private key `0x11...11` (public on purpose). `(27, sigR, sigS)`
is the signature of that key over the digest the code builds (nonce `k = 0x22...22`), computed
outside Lean; Lean only checks it.

- `processMessage_precompile_ok`, `mcg_facts`, `writeMax_le`, `ecrecover_call_runs`: the FORWARD
  rule for `GAS STATICCALL` to address 1 under EthLib's real runner `processRunner`: with enough
  gas the loop of the interpreter goes on from the opcode after STATICCALL with 1 pushed and
  the output of `Ecrecover.compute` written. (The kit has only the backward rule
  `ecrecover_call_ok`. These four are the same text as in `tokens/dai/.../PermitRun.lean`,
  written by part close-e; they should move to the kit.)
- `permit_runs`: THE WITNESS. From 100000 gas the run of `m1` under the real runner ends with
  no error; the allowance of `(SIGNER, SIGNER)` is then `2^96 - 1` and the nonce of `SIGNER`
  is 1. It is the way of `permit` with the largest amount. No witness is given for `permit`
  with another amount.
- `permit_runs_inv`: the run exists and, under the keccak hypothesis `RealSep` of this call
  (not proved), it ends in a state where the invariant holds: the success case of
  `supply_preserved_real` is not empty for `permit`.
- `one256`, `c0w`, `pmk0` ... `pmk12`, `dm10`, `dm11`, `dmk11`: the memory of the two digests,
  one write at a time on lists of words, and the hashes of the two type strings.
- `delegateBySig_runs`: THE WITNESS for `delegateBySig`. The call `m2`:
  `delegateBySig(SIGNER, 0, 2^256 - 1, 27, sigR, sigS2)` from `Witness.CALLER1` to `C0`, chain
  id 1, all-zero storage, 200000 gas: the run under the real runner ends with no error and the
  delegate of `SIGNER` is then `SIGNER`. No votes move (the balance of `SIGNER` is 0).
- `writeCost_le22100`, `gas_bound`, `acc_side`: side conditions, also used by `Runs.lean`.

Fork: Paris <= fork < Glamsterdam.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace UniVerify.Instance

open UsdtVerify
open TokenKit
open UniVerify UniVerify.Sanity

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

/-! ## Side conditions -/

/-- Before Glamsterdam, from Berlin, an SSTORE costs at most 22100. -/
theorem writeCost_le22100 (hberlin : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (o c n : U256) (cold : Bool) : Gas.writeCost fork o c n cold ≤ 22100 :=
  Nat.le_trans (Gas.writeCost_le hberlin o c n cold) (writeMax_le hglam)

/-- A read of an account leaves the storage words as they are. -/
theorem storageAt_recordAccountRead (S : State.TransactionState) (a C : Address) (n : U256) :
    storageAt (S.recordAccountRead a) C n = storageAt S C n := rfl

/-- A read of an account leaves the accounts as they are. -/
theorem hasAccount_recordAccountRead {S : State.TransactionState} {C : Address} (a : Address)
    (h : hasAccount S C) : hasAccount (S.recordAccountRead a) C := h

/-- Gas side conditions: every `slotCost` is at most 2100 and every `writeCost` at most 22100;
the rest is linear arithmetic. -/
macro "gas_bound" : tactic => `(tactic| (
  repeat (generalize hx : slotCost _ = x
          have : x ≤ 2100 := by rw [← hx]; exact UsdtVerify.slotCost_le _
          clear hx)
  repeat (generalize hx : Gas.writeCost _ _ _ _ _ = x
          have : x ≤ 22100 := by
            rw [← hx]; exact writeCost_le22100 (by assumption) (by assumption) _ _ _ _
          clear hx)
  omega))

/-- The contract has its account after reads and writes of its slots and reads of accounts. -/
macro "acc_side" : tactic => `(tactic| (repeat' (first
  | assumption
  | apply UsdtVerify.hasAccount_writeSlot
  | apply UsdtVerify.hasAccount_readSlot
  | apply hasAccount_recordAccountRead)))

/-! ## The call -/

/-- The address word of the private key `0x11...11`. -/
abbrev SIGNER : U256 := 0x19e7e376e7c213b7e7e7e46cc70a5dd086daff2a

/-- The address of the witness: the address of UNI on mainnet. -/
def C0 : Address := toAddressMasked 0x1f9840a85d5aF5bf1D1762F925BDADdC4201F984

/-- The call data of `permit(SIGNER, SIGNER, 2^256 - 1, 2^256 - 1, 27, sigR, sigS)`: 228
bytes. -/
def permitData : ByteArray := ⟨#[
    213, 5, 172, 207, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 231, 227, 118, 231, 194, 19, 183,
    231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    25, 231, 227, 118, 231, 194, 19, 183, 231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255,
    42, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 70, 109, 127, 202, 229, 99, 229, 203,
    9, 160, 209, 135, 11, 181, 128, 52, 72, 4, 97, 120, 121, 161, 73, 73, 207, 34, 40, 95, 27,
    174, 63, 39, 123, 167, 172, 120, 241, 23, 227, 50, 30, 150, 166, 119, 17, 223, 18, 211, 181,
    59, 130, 150, 16, 207, 111, 76, 245, 15, 93, 96, 25, 143, 39, 166]⟩

/-- `r` of the signature. -/
abbrev sigR : U256 := 31855367722742370537280679280108010854876607759940877706949385967087672770343

/-- `s` of the signature. -/
abbrev sigS : U256 := 55930734196515093020875536300439976436833095122019933013973192827431933650854

/-- The largest word: the amount and the deadline of the call. -/
abbrev MAXW : U256 :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- The call `permit(SIGNER, SIGNER, 2^256 - 1, 2^256 - 1, 27, sigR, sigS)` from
`Witness.CALLER1` to `C0`. -/
abbrev m1 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) : Message fork :=
  sMsg b t C0 Witness.CALLER1 CODE permitData

theorem size_permitData : permitData.size = 228 := by decide +kernel

theorem selector_permitData : selector permitData = 0xd505accf := by decide +kernel

theorem arg1_permitData : loadWord permitData 4 32 = SIGNER := by decide +kernel

theorem arg2_permitData : loadWord permitData 36 32 = SIGNER := by decide +kernel

theorem arg3_permitData : loadWord permitData 68 32 = MAXW := by decide +kernel

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

/-! ## The memory of the digest, one write at a time

The code of UNI builds the two type hashes of EIP-712 from strings that it copies into memory.
Each write below is rewritten on lists of words (`memW_set`), so that the kernel only has to
evaluate the two reads that are hashed. -/

theorem one256 : BitVec.ofNat 256 (UInt64.toNat 1) = (1 : U256) := by decide

theorem c0w : bitwiseAnd 1461501637330902918203684832716283019655932542975 C0.toU256 =
    (180374059643543449999388718682590567161426737540 : U256) := by decide +kernel

/-- The hash of the 67 bytes at 128 of the memory of `permit` after write 0. -/
theorem pmk0 :
    keccak (memoryReadBytes (memW
      [0,
       0,
       128,
       0,
       31339120015659993862160253144463915315563489969021235592778650402122642896182,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096]) 128 67) =
    (63630494520926674092677056046569304749177344945028501797992170511073678501990 : U256) := by
  decide +kernel

/-- Write 1 of `permit` into memory, on lists of words. -/
theorem pm1 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       128,
       0,
       31339120015659993862160253144463915315563489969021235592778650402122642896182,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096]) 0) 64
      (wordBytes 192) =
    memW
      [0,
       0,
       192,
       0,
       31339120015659993862160253144463915315563489969021235592778650402122642896182,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096] :=
  memW_set 2 rfl rfl rfl rfl

/-- Write 2 of `permit` into memory, on lists of words. -/
theorem pm2 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       31339120015659993862160253144463915315563489969021235592778650402122642896182,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096]) 0) 128
      (wordBytes 7) =
    memW
      [0,
       0,
       192,
       0,
       7,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096] :=
  memW_set 4 rfl rfl rfl rfl

/-- Write 3 of `permit` into memory, on lists of words. -/
theorem pm3 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       14649649421915637344621520266599775164314850317324210588512076930339073978977,
       44984209240857883444306039193905058771011290509921117659624855548403275268096]) 0) 160
      (wordBytes 38641673103035791190642274847805266032865247065289303281015917237975035936768) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096] :=
  memW_set 5 rfl rfl rfl rfl

/-- Write 4 of `permit` into memory, on lists of words. -/
theorem pm4 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096]) 32) 224
      (wordBytes 63630494520926674092677056046569304749177344945028501797992170511073678501990) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990] :=
  memW_set 7 rfl rfl rfl rfl

/-- Write 5 of `permit` into memory, on lists of words. -/
theorem pm5 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990]) 32) 256
      (wordBytes 69550820474613135285068131891700207053450730286089234916939683685459009358213) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213] :=
  memW_set 8 rfl rfl rfl rfl

/-- Write 6 of `permit` into memory, on lists of words. -/
theorem pm6 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213]) 32) 288
      (wordBytes 1) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1] :=
  memW_set 9 rfl rfl rfl rfl

/-- Write 7 of `permit` into memory, on lists of words. -/
theorem pm7 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1]) 32) 320
      (wordBytes 180374059643543449999388718682590567161426737540) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540] :=
  memW_set 10 rfl rfl rfl rfl

/-- Write 8 of `permit` into memory, on lists of words. -/
theorem pm8 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       44984209240857883444306039193905058771011290509921117659624855548403275268096,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540]) 0) 192
      (wordBytes 128) =
    memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540] :=
  memW_set 6 rfl rfl rfl rfl

/-- Write 9 of `permit` into memory, on lists of words. -/
theorem pm9 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       192,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540]) 0) 64
      (wordBytes 352) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540] :=
  memW_set 2 rfl rfl rfl rfl

/-- Write 10 of `permit` into memory, on lists of words. -/
theorem pm10 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540]) 32) 352
      (wordBytes 36364269189027223877068423077536277388017466150737530773468790605722156232805) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805] :=
  memW_set 11 rfl rfl rfl rfl

/-- Write 11 of `permit` into memory, on lists of words. -/
theorem pm11 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805]) 32) 384
      (wordBytes 49931798205134128319682575132504856176474202354739289583216949559915153613669) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805,
       49931798205134128319682575132504856176474202354739289583216949559915153613669] :=
  memW_set 12 rfl rfl rfl rfl

/-- Write 12 of `permit` into memory, on lists of words. -/
theorem pm12 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805,
       49931798205134128319682575132504856176474202354739289583216949559915153613669]) 32) 416
      (wordBytes 20109214105440218598748808833522204877362758516655735916536819911168521928704) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805,
       49931798205134128319682575132504856176474202354739289583216949559915153613669,
       20109214105440218598748808833522204877362758516655735916536819911168521928704] :=
  memW_set 13 rfl rfl rfl rfl

/-- The hash of the 82 bytes at 352 of the memory of `permit` after write 12. -/
theorem pmk12 :
    keccak (memoryReadBytes (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       36364269189027223877068423077536277388017466150737530773468790605722156232805,
       49931798205134128319682575132504856176474202354739289583216949559915153613669,
       20109214105440218598748808833522204877362758516655735916536819911168521928704]) 352 82) =
    (49955707469362902507454157297736832118868343942642399513960811609542965143241 : U256) := by
  decide +kernel

/-- Write 10 of `delegateBySig` into memory, on lists of words. -/
theorem dm10 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540]) 32) 352
      (wordBytes 30936473379652054583795126985927503730624564310361089039571661727158641191278) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       30936473379652054583795126985927503730624564310361089039571661727158641191278] :=
  memW_set 11 rfl rfl rfl rfl

/-- Write 11 of `delegateBySig` into memory, on lists of words. -/
theorem dm11 :
    memoryWrite (memoryExtend (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       30936473379652054583795126985927503730624564310361089039571661727158641191278]) 32) 384
      (wordBytes 52557000040706743965561480640911802844422718583088367087768606517336574263296) =
    memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       30936473379652054583795126985927503730624564310361089039571661727158641191278,
       52557000040706743965561480640911802844422718583088367087768606517336574263296] :=
  memW_set 12 rfl rfl rfl rfl

/-- The hash of the 58 bytes at 352 of the memory of `delegateBySig` after write 11. -/
theorem dmk11 :
    keccak (memoryReadBytes (memW
      [0,
       0,
       352,
       0,
       7,
       38641673103035791190642274847805266032865247065289303281015917237975035936768,
       128,
       63630494520926674092677056046569304749177344945028501797992170511073678501990,
       69550820474613135285068131891700207053450730286089234916939683685459009358213,
       1,
       180374059643543449999388718682590567161426737540,
       30936473379652054583795126985927503730624564310361089039571661727158641191278,
       52557000040706743965561480640911802844422718583088367087768606517336574263296]) 352 58) =
    (103359069561928152843793640083012950350530901667116492021891118459870908603103 : U256) := by
  decide +kernel

/-! ## The witness -/

set_option maxHeartbeats 4000000 in
/-- THE WITNESS for `permit`, from Paris and before Glamsterdam, under EthLib's real runner (the
precompile ECRECOVER is run, not assumed). The call `m1` in a block with chain id 1, from the
state with all-zero storage, with 100000 gas, for every substate and every bound of at least
100000: the loop of the interpreter ends in a frame `s` with no error. In its state the
allowance of `(SIGNER, SIGNER)` is `2^96 - 1` and the nonce of `SIGNER` is 1. -/
theorem permit_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hchain : b.chainId = 1) (t : TransactionEnvironment fork)
    (ss : Substate) {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t) 0 [] .empty 100000 (sState C0 []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧
      storageAt s.state C0 (mapSlot SIGNER (mapSlot SIGNER 3)) =
        (79228162514264337593543950335 : U256) ∧
      storageAt s.state C0 (mapSlot SIGNER 8) = (1 : U256) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz : (m1 b t).data.size = 228 := size_permitData
  have hsl : selector (m1 b t).data = 0xd505accf := selector_permitData
  have hA1 : loadWord (m1 b t).data 4 32 = SIGNER := arg1_permitData
  have hA2 : loadWord (m1 b t).data 36 32 = SIGNER := arg2_permitData
  have hA3 : loadWord (m1 b t).data 68 32 = MAXW := arg3_permitData
  have hA4 : loadWord (m1 b t).data 100 32 = MAXW := arg4_permitData
  have hA5 : loadWord (m1 b t).data 132 32 = (27 : U256) := arg5_permitData
  have hA6 : loadWord (m1 b t).data 164 32 = sigR := arg6_permitData
  have hA7 : loadWord (m1 b t).data 196 32 = sigS := arg7_permitData
  have hval : (m1 b t).value = 0 := rfl
  have hct : (m1 b t).currentTarget = C0 := rfl
  have hts : (m1 b t).blockEnv = b := rfl
  have hacc : hasAccount (sState C0 []) C0 := hasAccount_sState C0 _
  have wc : ∀ o c n cold, Gas.writeCost fork o c n cold ≤ 22100 := fun o c n cold =>
    Nat.le_trans (Gas.writeCost_le hberlin o c n cold) (writeMax_le hglam)
  have hcost : permitPreMax (m1 b t) (sState C0 []) ss ≤ 4438 + 2100 + 22100 :=
    Nat.add_le_add (Nat.add_le_add_left (_root_.UsdtVerify.slotCost_le _) _) (wc _ _ _ _)
  -- the code before the call
  have hpre := Paths.permit_p6 (fork := fork) (message := m1 b t) (state := sState C0 [])
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
    (by rw [hA3]; decide +kernel)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right hcost 2300) (by decide))
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m1 b t) (sState C0 []) ss 100000)
    (at_sFrame _ rfl _ _ _)
  have within : GasMeter.gasHeld (sFrame (m1 b t) (sState C0 []) ss 100000).gas ≤ bound := hb
  have w0 : GasMeter.gasHeld z.gas ≤ bound :=
    Nat.le_trans ((hrz.mono And.left).gasHeld_le Step.gasHeld_le) within
  have e0 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq (hrz.mono And.left) within
  obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, mout, w0', w1,
    w2', w3, -⟩ :=
    Paths.permit_p6_mem (message := m1 b t) (state := sState C0 [])
  have t706 : (706 : U256).toNat = 706 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t674 : (674 : U256).toNat = 674 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  have hz' : At CODE (m1 b t) 4886 _ _
      (100000 - permitPreMax (m1 b t) (sState C0 []) ss) _ _ z := hz
  have hS1 : hasAccount (permitS1 (m1 b t) (sState C0 [])) C0 :=
    hasAccount_writeSlot (hasAccount_readSlot hacc)
  -- the call
  obtain ⟨a, hga, hat, w2, e2⟩ := ecrecover_call_runs hparis hglam (pc := 4886)
    (by code_fact) (by code_fact) (by code_fact) (by simp [STACK_LIMIT])
    (by rw [msz]; decide) (by rw [msz]; decide)
    (by rw [getAccount_writeSlot, getAccount_readSlot]; exact codeHash_sState C0 [] _)
    (by show (0 : Nat) + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) (by omega) hz' w0
  simp only [t706, t128, t674, t32] at hat
  rw [read4_raw w0' w1 w2' w3 msz (by decide)] at hat
  have hfit' : ∀ {M : ByteArray}, M.size = 864 → 674 + 32 ≤ M.size := fun h => by
    rw [h]; decide
  have hfit := hfit' msz
  have hS2 : hasAccount (((permitS1 (m1 b t) (sState C0 [])).recordAccountRead
      (toAddressMasked 1)).recordAccountRead C0) C0 :=
    hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _ hS1)
  -- the code after the call
  have key := fun h1 h2 h3 hg => SpecG.runFrame (runChild := processRunner fork bound)
    (Paths.permitMaxTail_p4 (fork := fork) hberlin
      ((size_ecrecover_write _ hfit).trans msz)
      ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans m64)
      (load_ecrecover _ hfit mout)
      (rfl : (m1 b t).isStatic = false)
      hS2 h1 h2 h3 (gas := a.gas) hg) hat w2
  obtain ⟨s, hs, hH⟩ := key
    (by
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hct, hts, hchain, storageAt_sState_nil,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9, pm10, pm11, pm12, pmk12, one256, c0w]
      decide +kernel)
    (by
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hct, hts, hchain, storageAt_sState_nil,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9, pm10, pm11, pm12, pmk12, one256, c0w]
      decide +kernel)
    (by rw [hA4]; exact deadline_ok _)
    (Nat.lt_of_lt_of_le (Nat.add_lt_add_right (Nat.add_lt_add_of_le_of_lt
      (Nat.add_le_add_left (_root_.UsdtVerify.slotCost_le _) _)
      (Nat.lt_succ_of_le (wc _ _ _ _))) _) (by omega))
  obtain ⟨-, he, -, -, hst, -⟩ := hH
  refine ⟨_, s, within, at_sFrame _ rfl _ _ _, e0.trans (e2.trans hs), by simpa using he, ?_, ?_⟩
  · rw [hst]
    simp (disch := first
        | exact hasAccount_readSlot (hasAccount_recordAccountRead _
            (hasAccount_recordAccountRead _ (hasAccount_writeSlot (hasAccount_readSlot hacc))))
        | exact hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _
            (hasAccount_writeSlot (hasAccount_readSlot hacc)))
        | exact hasAccount_readSlot hacc) only
      [permitS1, hA1, hA2, hA3, hct, storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil]
    decide +kernel
  · rw [hst]
    simp (disch := first
        | exact hasAccount_readSlot (hasAccount_recordAccountRead _
            (hasAccount_recordAccountRead _ (hasAccount_writeSlot (hasAccount_readSlot hacc))))
        | exact hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _
            (hasAccount_writeSlot (hasAccount_readSlot hacc)))
        | exact hasAccount_readSlot hacc) only
      [permitS1, hA1, hA2, hA3, hct, storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil]
    decide +kernel

set_option maxHeartbeats 2000000 in
/-- The run of `permit_runs` exists and, under the keccak hypothesis `RealSep` of this call (not
proved), ends in a state where the invariant holds: the success case of
`supply_preserved_real` is not empty for `permit`. The start invariant, `NoDelegation1` and the
size of the call data are discharged. -/
theorem permit_runs_inv (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hchain : b.chainId = 1) (t : TransactionEnvironment fork)
    (hsep : RealSep (m1 b t) (sState C0 [])) (ss : Substate)
    {bound : Nat} (hb : 100000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m1 b t) 0 [] .empty 100000 (sState C0 []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧ Inv C0 s.state := by
  obtain ⟨evm, s, within, start, hrun, hok, -, -⟩ := permit_runs hparis hglam b hchain t ss hb
  have hsz : (m1 b t).data.size = 228 := size_permitData
  exact ⟨evm, s, within, start, hrun, hok,
    supply_preserved_real (message := m1 b t) (state := sState C0 []) hparis hglam
      (by rw [hsz]; decide) (noDelegation1_sState C0 []) hsep (inv_start C0) start within hrun
      hok⟩

/-! ## `delegateBySig` -/

/-- The call data of `delegateBySig(SIGNER, 0, 2^256 - 1, 27, sigR, sigS2)`: 196 bytes. -/
def delegData : ByteArray := ⟨#[
    195, 205, 165, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 231, 227, 118, 231, 194, 19, 183,
    231, 231, 228, 108, 199, 10, 93, 208, 134, 218, 255, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
    255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 70, 109, 127, 202, 229, 99, 229, 203, 9, 160, 209,
    135, 11, 181, 128, 52, 72, 4, 97, 120, 121, 161, 73, 73, 207, 34, 40, 95, 27, 174, 63, 39, 2,
    250, 159, 155, 201, 92, 192, 212, 172, 59, 56, 56, 87, 88, 155, 103, 39, 66, 244, 199, 62,
    96, 137, 173, 245, 16, 175, 123, 154, 72, 227, 73]⟩

/-- `s` of the signature of the delegation (`r` is `sigR`: the same nonce `k`). -/
abbrev sigS2 : U256 := 1347439041027929064405390728695950059542801758534601950294459629613731078985

/-- The call `delegateBySig(SIGNER, 0, 2^256 - 1, 27, sigR, sigS2)` from `Witness.CALLER1` to
`C0`: `SIGNER` delegates to itself, by signature. -/
abbrev m2 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) : Message fork :=
  sMsg b t C0 Witness.CALLER1 CODE delegData

theorem size_delegData : delegData.size = 196 := by decide +kernel

theorem selector_delegData : selector delegData = 0xc3cda520 := by decide +kernel

theorem arg1_delegData : loadWord delegData 4 32 = SIGNER := by decide +kernel

theorem arg2_delegData : loadWord delegData 36 32 = (0 : U256) := by decide +kernel

theorem arg3_delegData : loadWord delegData 68 32 = MAXW := by decide +kernel

theorem arg4_delegData : loadWord delegData 100 32 = (27 : U256) := by decide +kernel

theorem arg5_delegData : loadWord delegData 132 32 = sigR := by decide +kernel

theorem arg6_delegData : loadWord delegData 164 32 = sigS2 := by decide +kernel

set_option maxHeartbeats 8000000 in
/-- THE WITNESS for `delegateBySig`, from Paris and before Glamsterdam, under EthLib's real
runner (the precompile ECRECOVER is run, not assumed). The call `m2` in a block with chain id 1,
from the state with all-zero storage, with 200000 gas: the loop of the interpreter ends in a
frame `s` with no error, and the delegate of `SIGNER` is then `SIGNER`. The run is the path
`delegateBySig_p4`, the call of ECRECOVER, the path `delegateBySigTail_p5` and the path
`mvSrc5_p10` of the `_moveDelegates` code (no votes move: the balance of `SIGNER` is 0). -/
theorem delegateBySig_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hchain : b.chainId = 1) (t : TransactionEnvironment fork)
    (ss : Substate) {bound : Nat} (hb : 200000 ≤ bound) :
    ∃ (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (m2 b t) 0 [] .empty 200000 (sState C0 []) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
        within = .ok s ∧
      s.error = none ∧
      storageAt s.state C0 (mapSlot SIGNER 5) = SIGNER := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz : (m2 b t).data.size = 196 := size_delegData
  have hsl : selector (m2 b t).data = 0xc3cda520 := selector_delegData
  have hA1 : loadWord (m2 b t).data 4 32 = SIGNER := arg1_delegData
  have hA2 : loadWord (m2 b t).data 36 32 = (0 : U256) := arg2_delegData
  have hA3 : loadWord (m2 b t).data 68 32 = MAXW := arg3_delegData
  have hA4 : loadWord (m2 b t).data 100 32 = (27 : U256) := arg4_delegData
  have hA5 : loadWord (m2 b t).data 132 32 = sigR := arg5_delegData
  have hA6 : loadWord (m2 b t).data 164 32 = sigS2 := arg6_delegData
  have hval : (m2 b t).value = 0 := rfl
  have hct : (m2 b t).currentTarget = C0 := rfl
  have hts : (m2 b t).blockEnv = b := rfl
  have hacc : hasAccount (sState C0 []) C0 := hasAccount_sState C0 _
  -- the code before the call
  have hpre := Paths.delegateBySig_p4 (fork := fork) (message := m2 b t)
    (state := sState C0 []) (substate := ss) (gas := 200000) hberlin
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    hsl
    (by rw [hval]; decide)
    (by rw [hsz]; decide)
    (by rw [hA1]; decide +kernel)
    (by rw [hA4]; decide +kernel)
    (by omega)
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m2 b t) (sState C0 []) ss 200000)
    (at_sFrame _ rfl _ _ _)
  have within : GasMeter.gasHeld (sFrame (m2 b t) (sState C0 []) ss 200000).gas ≤ bound := hb
  have w0 : GasMeter.gasHeld z.gas ≤ bound :=
    Nat.le_trans ((hrz.mono And.left).gasHeld_le Step.gasHeld_le) within
  have e0 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq (hrz.mono And.left) within
  obtain ⟨msz, m64, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, mout, w0', w1, w2',
    w3, -⟩ := Paths.delegateBySig_p4_mem (message := m2 b t)
  have t642 : (642 : U256).toNat = 642 := by decide
  have t128 : (128 : U256).toNat = 128 := by decide
  have t610 : (610 : U256).toNat = 610 := by decide
  have t32 : (32 : U256).toNat = 32 := by decide
  -- the call
  obtain ⟨a, hga, hat, w2, e2⟩ := ecrecover_call_runs hparis hglam (pc := 4071)
    (by code_fact) (by code_fact) (by code_fact) (by simp [STACK_LIMIT])
    (by rw [msz]; decide) (by rw [msz]; decide)
    (by exact codeHash_sState C0 [] _)
    (by show (0 : Nat) + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) (by omega) hz w0
  simp only [t642, t128, t610, t32] at hat
  rw [read4_raw w0' w1 w2' w3 msz (by decide)] at hat
  have hfit' : ∀ {M : ByteArray}, M.size = 800 → 610 + 32 ≤ M.size := fun h => by
    rw [h]; decide
  have hfit := hfit' msz
  have hm1 := fun data : ByteArray => (size_ecrecover_write data hfit).trans msz
  have hm2 := fun data : ByteArray =>
    (congrArg (loadWord · 0 32) (read_ecrecover_other data hfit (.inl (by decide)))).trans m64
  have hm3 := fun data : ByteArray => load_ecrecover data hfit mout
  -- the code after the call, up to the entry of `_moveDelegates`
  have key := fun h1 h2 h3 hg => (Paths.delegateBySigTail_p5 (fork := fork) hberlin
    (hm1 _) (hm2 _) (hm3 _)
    (rfl : (m2 b t).isStatic = false)
    (hasAccount_recordAccountRead _ (hasAccount_recordAccountRead _ hacc))
    h1 h2 h3 (gas := a.gas) hg) a hat
  obtain ⟨z2, hrz2, hz2⟩ := key
    (by
      simp only [hA1, hA2, hA3, hA4, hA5, hA6, hct, hts, hchain,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9,
        dm10, dm11, dmk11, one256, c0w]
      decide +kernel)
    (by
      simp only [hA2, hct, storageAt_recordAccountRead, storageAt_sState_nil]
      decide +kernel)
    (by rw [hA3]; exact deadline_ok _)
    (by gas_bound)
  have w3' : GasMeter.gasHeld z2.gas ≤ bound :=
    Nat.le_trans ((hrz2.mono And.left).gasHeld_le Step.gasHeld_le) w2
  have e3 := runFrame_eq_of_reaches (bound := bound) (runChild := processRunner fork bound)
    Step.gasHeld_le Step.runFrame_eq (hrz2.mono And.left) w2
  -- `_moveDelegates`: the amount is 0
  have key2 := fun h1 h2 hg => (Paths.mvSrc5_p10 (fork := fork) hberlin
    (Paths.delegateBySigTail_p5_mem (dg := 0) (sh := 0) (ds := 0) (sigS := 0) (sigR := 0)
      (sigV := 0) (expiry := 0) (nonce := 0) (delegatee := 0) (sel := 0)
      (hm1 _) (hm2 _) (hm3 _)).1
    (Paths.delegateBySigTail_p5_mem (dg := 0) (sh := 0) (ds := 0) (sigS := 0) (sigR := 0)
      (sigV := 0) (expiry := 0) (nonce := 0) (delegatee := 0) (sel := 0)
      (hm1 _) (hm2 _) (hm3 _)).2.1
    h1 h2 hg) z2 hz2
  obtain ⟨s, hr3, hrun, hH⟩ := key2
    (by
      simp (disch := acc_side) only [hA1, hA2, hA3, hA4, hA5, hA6, hct, hts, hchain,
        storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9,
        dm10, dm11, dmk11, one256, c0w] <;> decide +kernel)
    (by
      simp (disch := acc_side) only [hA1, hA2, hA3, hA4, hA5, hA6, hct, hts, hchain,
        storageAt_recordAccountRead, storageAt_readSlot,
        TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9,
        dm10, dm11, dmk11, one256, c0w] <;> decide +kernel)
    (by gas_bound)
  obtain ⟨_, e4⟩ := Witness.endsL_of_reaches hr3 hrun (processRunner fork bound) w3'
  obtain ⟨-, he, -, -, hst, -⟩ := hH
  refine ⟨_, s, within, at_sFrame _ rfl _ _ _, e0.trans (e2.trans (e3.trans e4)),
    by simpa using he, ?_⟩
  rw [hst]
  simp (disch := acc_side) only [hA1, hA2, hA3, hA4, hA5, hA6, hct, hts, hchain,
    storageAt_recordAccountRead, storageAt_readSlot,
    TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_nil,
        pmk0, pm1, pm2, pm3, pm4, pm5, pm6, pm7, pm8, pm9,
        dm10, dm11, dmk11, one256, c0w] <;> decide +kernel

end UniVerify.Instance

import WethVerify.Weth.Sanity.Zero
import WethVerify.Weth.WithdrawAll
import TokenKit.Evm.Stipend
import EthLib.Execution.Proofs.Evm.Logic.Callee

/-!
# Sanity: withdraw of a nonzero amount runs to the end under the runner of the interpreter

The theorems on `withdraw` hold for every runner of messages. This file shows that they are not
empty for the real one: under `processRunner` (EthLib's `processMessage`), a call of `withdraw`
with `wad` not 0 from a caller with no code runs to the end with no error.

- `callValueOn`: the rule of a CALL with value, in EthLib's `HoareOn`: when the run aborts
  because the runner fails, it failed on the message of `CallSend`. (`callL` of Evm/Call.lean
  does not say on which message the runner failed.)
- `withdraw_on`: `withdraw_path` in that form.
- `withdraw_succeeds`: for EVERY state, from Berlin and before Glamsterdam: when the caller has
  no code and is no precompile and is not the contract, holds `wad` or more tokens, the contract
  holds `wad` or more wei, `wad` is not 0, the depth has room and the gas is enough, the loop
  under `processRunner` returns a frame with no error and an empty output. The proof shows that
  `processMessage` does not fail on the message of the CALL: the move of the ether succeeds and
  the empty code stops at once.
- `wS`: a sample state: one account at the contract, with 5 wei and `balanceOf[caller]` = 5.
- `withdraw_runs`: `withdraw(1)` in that state runs to the end with no error under
  `processRunner`. Every hypothesis of `withdraw_succeeds` is proved for it, apart from two
  facts about the address of the caller that are kept as hypotheses: it is not the contract
  (`hne`) and it is not the address of a precompile (`noPre`).
- `withdraw_runs_closed`: the same with the two addresses fixed (`CONTRACT2`, `CALLER1`) and the
  two facts proved: no hypothesis is left but the fork range.

The witness that was here before used a stub runner that ended every message at once, and
`wad` = 0. It is removed (`stubRunner`, `meets_stub`).

Forks: Berlin, London, Paris, Shanghai, Cancun, Prague, Osaka (before Glamsterdam, as the rules
of the CALL step).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace WethVerify.Sanity

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify WethVerify.Paths WethVerify.Blocks WethVerify.Complete UsdtVerify.Complete
open UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The CALL with value, with the message on which the runner may fail -/

section Rule

variable {message : Message fork} {state : State.TransactionState} {substate : Substate}

/-- CALL of `v` wei, not 0 and at most the balance of the current account, with empty ranges,
from a frame that is not static. As `callL`, in the form that names the message on which the
runner may fail: it is the message of `CallSend`. -/
theorem callValueOn (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop}
    {asked to v inputStart outputStart : U256} {rest : List U256} {calleeCode : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hv : v ≠ 0)
    (hstatic : message.isStatic = false)
    (hbal : v ≤ (state.getAccount message.currentTarget).balance)
    (hcode : state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hgas : callExtra fork state substate to v ≤ gas) :
    HoareOn fork callee
      (fun caller msg => CallSend message gas state substate asked to v calleeCode caller msg)
      (At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
        memory gas state substate)
      fun after => ∃ caller msg child, callee caller msg child ∧
        CallSend message gas state substate asked to v calleeCode caller msg ∧
        At code message (pc + 1) ((if child.error.isNone then 1 else 0) :: rest) memory
          (gas - (callGas fork state substate asked to v gas).cost + child.gas)
          (incorporateChild fork caller child).state (incorporateChild fork caller child).substate
          after := by
  apply HoareOn.of_child
  intro evm hp
  obtain ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩ := id hp
  have hext : extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have hprice : (callBaseCost fork
        (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) +
      callNewAccountCost fork evm.state (toAddressMasked to) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)]).cost =
      callExtra fork state substate to v := by
    rw [hext, hs, hss]
    rfl
  have hgasEq : messageCallGas fork v asked.toNat evm.gas
      (extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)]).cost
      (callBaseCost fork (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) +
        callNewAccountCost fork evm.state (toAddressMasked to) v + callValueCost fork v) =
      callGas fork state substate asked to v gas := by
    rw [hext, hs, hss, hg]
  obtain ⟨caller, msg, hstep, c1, c2, c3, c4, c5, c6, c7, c8, c9, co, c10, c11, m1, m2, m3, mt,
      mca, m4, md, m5, m6, m7, m8⟩ :=
    callStep_value (i := inputStart) (isz := 0) (o := outputStart) (osz := 0) hfork hglam hst hv
      (by rw [hm]; exact hstatic) (by rw [hs, hm]; exact hbal) (by rw [hs]; exact hcode) hdel
      (by rw [hm]; exact hdepth) (by rw [hprice, hg]; exact hgas)
  have hsend : CallSend message gas state substate asked to v calleeCode caller msg := by
    refine ⟨by rw [c10, hs, hm], by rw [c11, hss] <;> rfl, by rw [m1, hgasEq], by rw [m2, hm],
      m3, mt, mca, m4, ?_, m5, fun _ => m6, by rw [m7, hm], m8⟩
    simpa [hext, memoryExtend_zero, memoryReadBytes] using md
  refine ⟨hrun, caller, msg, resumeCall fork caller 0 outputStart 0, ?_, hsend, ?_⟩
  · rw [step_at_call hp hlt hbyte]
    exact hstep
  · intro child hchild hcallee
    have hlen : caller.stack.val.length < STACK_LIMIT := by
      have := evm.stack.property
      rw [hst] at this
      rw [c5]
      simp at this
      omega
    obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, ao, a10, a11, a12⟩ :=
      resumeCall_eq (child := child) (o := outputStart) (osz := 0) hlen
    refine .inl ⟨after, hres, caller, msg, child, hcallee, hsend, ?_⟩
    refine ⟨by rw [a1, c1, hc], by rw [a2, c2, hj], by rw [a3, c3, hm], by rw [a4, c4, hpc],
      by rw [a5, c5], ?_, ?_, by rw [a8, c8, hrun], by rw [a9, c9, herr], by rw [ao, co, hout],
      a10, a11⟩
    · rw [a6, c6, hext]
      simpa [memoryExtend_zero, memoryWrite] using hmem
    · rw [a7, c7, hgasEq, hext, hg] <;> rfl

/-- `withdraw(wad)` with `wad` not 0, from pc 0, in the form that names the message on which
the runner may fail. -/
theorem withdraw_on (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hc1 : isZero message.value ≠ 0)
    (hc2 : isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
      (wAmt message)))) ≠ 0)
    (hbal : wAmt message ≤ etherOf state message.currentTarget)
    (hv : wAmt message ≠ 0)
    {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {gas : Nat}
    (hg : wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message) + 2300 + 1489 ≤ gas) :
    SpecOn fork callee
      (fun caller msg => CallSend message (gas - wPre fork message state substate)
        (wState message state) (wSub fork message state substate) (wAsk message) (wSrc message)
        (wAmt message) calleeCode caller msg)
      (At CODE message 0 [] .empty gas state substate)
      fun s => ∃ caller msg child, callee caller msg child ∧
        CallSend message (gas - wPre fork message state substate) (wState message state)
          (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
          calleeCode caller msg ∧
        (child.error = none → s.error = none ∧ s.output = ByteArray.empty ∧
          s.state = (incorporateChild fork caller child).state) := by
  have hx := callExtra_wState (fork := fork) message state substate (wSrc message) (wAmt message)
  have hcl := callGas_cost_le fork (wState message state) (wSub fork message state substate)
    (wAsk message) (wSrc message) (wAmt message) (gas - wPre fork message state substate)
  have hask := wAsk_le message
  have hbal' : wAmt message ≤ etherOf (wState message state) message.currentTarget :=
    le_of_le_of_eq hbal (etherOf_wState message state message.currentTarget).symm
  have hcode' : (wState message state).getCode
      ((wState message state).getAccount (toAddressMasked (wSrc message))).codeHash =
        .ok calleeCode := by
    rw [toAddressMasked_wSrc, getCode_wState]
    exact hcode
  refine HoareOn.seq (HoareOn.of_hoare
    (withdraw_at hfork hsize hsize' hsel hstatic hacc hc1 hc2 (by omega)).toHoare) ?_
  refine HoareOn.seq (callValueOn (callee := callee) (calleeCode := calleeCode) hfork hglam
    (by code_fact) (by code_fact) hv hstatic hbal' hcode' hdel hdepth
    (by rw [hx]; omega)) ?_
  rintro bound runChild meets evm ⟨caller, msg, child, hc, hsend, hat⟩ within
  by_cases he : child.error = none
  · obtain ⟨after, hr, hq | hab⟩ := HoareOn.of_hoare (callee := callee)
      (S := fun caller msg => CallSend message (gas - wPre fork message state substate)
        (wState message state) (wSub fork message state substate) (wAsk message) (wSrc message)
        (wAmt message) calleeCode caller msg)
      (withdrawTail_p1 hfork hstatic (callFlag_ne.mpr he) (by omega)).toSpec bound runChild meets
      evm hat within
    · obtain ⟨-, herr, hout, -, hst, -⟩ := hq.2
      exact ⟨after, hr, .inl ⟨hq.1, caller, msg, child, hc, hsend,
        fun _ => ⟨by simpa using herr, hout, hst⟩⟩⟩
    · exact ⟨after, hr, .inr hab⟩
  · obtain ⟨after, hr, hq | hab⟩ := HoareOn.of_hoare (callee := callee)
      (S := fun caller msg => CallSend message (gas - wPre fork message state substate)
        (wState message state) (wSub fork message state substate) (wAsk message) (wSrc message)
        (wAmt message) calleeCode caller msg)
      (withdrawTail_p0 hfork hstatic
        (Classical.not_not.mp fun h => he (callFlag_ne.mp h)) (by omega)).toSpec bound runChild
      meets evm hat within
    · exact ⟨after, hr, .inl ⟨hq.1, caller, msg, child, hc, hsend, fun h => absurd h he⟩⟩
    · exact ⟨after, hr, .inr hab⟩

/-- Under the runner of the interpreter, for every state, from Berlin and before Glamsterdam:
`withdraw(wad)` with `wad` not 0, called with no value by a caller that has no code, is no
precompile and is not the contract, when the caller holds `wad` tokens or more and the contract
holds `wad` wei or more, with room in the call depth and enough gas: the interpreter loop
returns a frame with no error and an empty output. -/
theorem withdraw_succeeds (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hc1 : isZero message.value ≠ 0)
    (hc2 : isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
      (wAmt message)))) ≠ 0)
    (hbal : wAmt message ≤ etherOf state message.currentTarget)
    (hv : wAmt message ≠ 0)
    (heoa : state.getCode (state.getAccount message.caller).codeHash = .ok ByteArray.empty)
    (hne : message.currentTarget ≠ message.caller)
    (hroom : (etherOf state message.caller).toNat + (wAmt message).toNat < 2 ^ 256)
    (noPre : Precompiles.isPrecompile fork message.caller.toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas bound : Nat}
    (hg : wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message) + 2300 + 1489 ≤ gas)
    {evm : Evm fork Nat} (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) bound
        (processRunner (Meter := Nat) fork bound) evm within = .ok s ∧
      s.error = none ∧ s.output = ByteArray.empty := by
  have hspec := withdraw_on (callee := PaidNoCode (fork := fork)) (gas := gas)
    (substate := substate) hfork hglam hsize hsize' hsel hstatic hacc hc1 hc2 hbal hv heoa
    (fun _ => by first | rfl | decide | simp [delegatedAddress]) hdepth hg
  -- facts about the message of the CALL
  have key : ∀ (caller : Evm fork Nat) (msg : Message fork),
      CallSend message (gas - wPre fork message state substate) (wState message state)
        (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
        ByteArray.empty caller msg →
      msg.code = .empty ∧ msg.target = some message.caller ∧
        precompileAddress fork msg = none ∧
        (msg.shouldTransferValue = true ∧ msg.value ≠ 0) ∧
        ∃ moved, (startState fork msg caller.state).moveEther fork msg.caller msg.currentTarget
          msg.value = .ok moved := by
    intro caller msg hsend
    obtain ⟨hcs, -, -, hcaller, hto, htarget, hca, hcode, -, hval, hstv, -, -⟩ := hsend
    rw [toAddressMasked_wSrc] at hto htarget hca
    have hq0 := Stipend.quiet_startState (fork := fork) msg caller.state
    have hacct : ∀ a, (startState fork msg caller.state).getAccount a = state.getAccount a := by
      intro a
      rw [hq0.1, hcs]
      simp only [wState, State.TransactionState.getAccount_recordAccountRead,
        getAccount_writeSlot, getAccount_readSlot]
    refine ⟨hcode, htarget, ?_, ⟨hstv hv, by rw [hval]; exact hv⟩, ?_⟩
    · simp [precompileAddress, hca, noPre]
    · refine (State.TransactionState.moveEther_isOk_iff (fork := fork)
        (tx := startState fork msg caller.state) (sender := msg.caller)
        (recipient := msg.currentTarget) (amount := msg.value)
        (by rw [hcaller, hto]; exact hne)).mpr ⟨?_, ?_⟩
      · rw [hacct, hcaller, hval]
        exact BitVec.not_lt.mpr hbal
      · rw [hacct, hto, hval]
        exact hroom
  rcases SpecOn.runFrame hspec (meets_paidNoCode bound).ok start within with
    ⟨s, hrun, caller, msg, child, hc, hsend, hgood⟩ |
    ⟨after, caller, msg, resume, lt, e, -, -, -, hsend, herr, -⟩
  · obtain ⟨hcode, htarget, hpre, htr, -⟩ := key caller msg hsend
    obtain ⟨moved, -, hce, -⟩ := hc hcode (by rw [htarget]; rfl) hpre htr
    obtain ⟨he, ho, -⟩ := hgood hce
    exact ⟨s, hrun, he, ho⟩
  · exfalso
    obtain ⟨hcode, htarget, hpre, htr, moved, hm⟩ := key caller msg hsend
    have hp : processRunner fork bound caller msg lt =
        processMessage fork msg caller.state caller.substate.child := by
      simp only [processRunner, htarget]
    rw [hp] at herr
    obtain ⟨stopped, ran, hse, hss⟩ := runFrame_startFrame_empty (fork := fork) (message := msg)
      (state := moved)
      (substate := { caller.substate.child with
        logs := pushTransferLog fork caller.substate.child.logs msg.caller msg.currentTarget
          msg.value })
      (runChild := processRunner fork msg.gas) (within := Nat.le_refl _) hcode
    have hmap := processMessage_map_val_value htr hm hpre ran
    rw [herr] at hmap
    cases hmap

end Rule

/-! ## A sample state with ether and a token balance -/

/-- The slot of `balanceOf[caller]`, as the code computes it. -/
abbrev balKey (caller : Address) : U256 :=
  mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256))
    (3 : U256)

/-- A state with one account, at `C`, that holds 5 wei, has nonce 1 and no code hash, and whose
slots are those of `kvs`. -/
def wS (C : Address) (kvs : List (U256 × U256)) : State.TransactionState :=
  State.TransactionState.ofBlock
    { preState :=
        { accounts := (∅ : Std.ExtTreeMap Address State.Account).insert C
            { S_ACCOUNT with balance := 5 }
          storage := (∅ : State.StorageMap).insert C (slotMap kvs)
          code := ∅ }
      accountWrites := ∅
      storageWrites := ∅
      codeWrites := ∅
      storageClears := ∅ }

theorem hasAccount_wS (C : Address) (kvs : List (U256 × U256)) : hasAccount (wS C kvs) C := by
  simp [hasAccount, wS, State.TransactionState.ofBlock,
    State.TransactionState.getAccountOptional, State.State.getAccountOptional]

/-- The storage of the sample state is the storage of `sState`. -/
theorem storageAt_wS (C : Address) (kvs : List (U256 × U256)) (n : U256) :
    storageAt (wS C kvs) C n = storageAt (sState C kvs) C n := by
  rw [storageAt_sState]
  simp [storageAt, wS, State.TransactionState.ofBlock, State.TransactionState.getStorage,
    State.State.getStorage, State.StorageMap.slot]

/-- The contract holds 5 wei in the sample state. -/
theorem ether_wS (C : Address) (kvs : List (U256 × U256)) : etherOf (wS C kvs) C = 5 := by
  simp [etherOf, wS, S_ACCOUNT, State.TransactionState.ofBlock,
    State.TransactionState.getAccount, State.TransactionState.getAccountOptional,
    State.State.getAccountOptional]

/-- In the sample state every account has the hash of no code. -/
theorem codeHash_wS (C : Address) (kvs : List (U256 × U256)) (a : Address) :
    ((wS C kvs).getAccount a).codeHash = State.EMPTY_CODE_HASH := by
  unfold State.TransactionState.getAccount
  cases h : (wS C kvs).getAccountOptional a with
  | none => rfl
  | some acc =>
    simp only [wS, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
      State.State.getAccountOptional] at h
    simp [Std.ExtTreeMap.getElem?_insert] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- In the sample state every account holds at most 5 wei. -/
theorem ether_wS_le (C : Address) (kvs : List (U256 × U256)) (a : Address) :
    (etherOf (wS C kvs) a).toNat ≤ 5 := by
  unfold etherOf State.TransactionState.getAccount
  cases h : (wS C kvs).getAccountOptional a with
  | none => exact Nat.zero_le _
  | some acc =>
    simp only [wS, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
      State.State.getAccountOptional] at h
    simp [Std.ExtTreeMap.getElem?_insert] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _

/-- The four bytes of the selector of `withdraw(uint256)`. -/
def SEL_withdraw : ByteArray := ⟨#[0x2e, 0x1a, 0x7d, 0x4d]⟩

theorem size_SEL_withdraw : SEL_withdraw.size = 4 := by decide

/-- The call `withdraw(1)` from `caller` to `C`. -/
abbrev mW (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE (data1 SEL_withdraw 1)

/-- The success path of `withdraw` is not empty under the runner of the interpreter: in the
sample state, where the caller holds 5 tokens and the contract 5 wei, `withdraw(1)` from a
caller with no code runs to the end with no error. -/
theorem withdraw_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (ss : Substate) (hne : C ≠ caller)
    (noPre : Precompiles.isPrecompile fork caller.toU256.toNat = false) :
    ∃ (gas bound : Nat) (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (mW b t C caller) 0 [] .empty gas (wS C [(balKey caller, 5)]) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound
        (processRunner (Meter := Nat) fork bound) evm within = .ok s ∧
      s.error = none ∧ s.output = ByteArray.empty := by
  have hdata : (mW b t C caller).data = data1 SEL_withdraw 1 := rfl
  have hsz : (mW b t C caller).data.size = 36 := by
    rw [hdata]; exact size_data1 size_SEL_withdraw _
  have hsl : selector (mW b t C caller).data = selector SEL_withdraw := by
    rw [hdata]; exact selector_data1 size_SEL_withdraw _
  have hA1 : wAmt (mW b t C caller) = 1 := by
    show loadWord (mW b t C caller).data 4 32 = 1
    rw [hdata]; exact Witness.arg1_data1 size_SEL_withdraw _
  have hval : (mW b t C caller).value = 0 := rfl
  have hstore : storageAt (wS C [(balKey caller, 5)]) C (wKey (mW b t C caller)) = 5 := by
    rw [storageAt_wS, storageAt_sState_cons]
    split
    · rfl
    · rename_i h
      exact absurd rfl h
  have h1 : (wAmt (mW b t C caller)).toNat = 1 := by rw [hA1]; rfl
  have hle := ether_wS_le C [(balKey caller, 5)] caller
  obtain ⟨s, hrun, he, ho⟩ := withdraw_succeeds (fork := fork) (message := mW b t C caller)
    (state := wS C [(balKey caller, 5)]) (substate := ss) (bound := _) hfork hglam
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (hasAccount_wS C _)
    (by rw [hval]; decide)
    (by
      show isZero (isZero (isZero (lessThan
        (storageAt (wS C [(balKey caller, 5)]) C (wKey (mW b t C caller)))
        (wAmt (mW b t C caller))))) ≠ 0
      rw [hstore, hA1]
      decide)
    (by
      show wAmt (mW b t C caller) ≤ etherOf (wS C [(balKey caller, 5)]) C
      rw [hA1, ether_wS]
      decide)
    (by rw [hA1]; decide)
    (by
      rw [codeHash_wS]
      simp [State.TransactionState.getCode])
    hne
    (by
      show (etherOf (wS C [(balKey caller, 5)]) caller).toNat + _ < 2 ^ 256
      omega)
    noPre
    (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide)
    (Nat.le_refl _)
    (at_sFrame (mW b t C caller) rfl _ ss _) (Nat.le_refl _)
  exact ⟨_, _, _, s, Nat.le_refl _, at_sFrame (mW b t C caller) rfl _ ss _, hrun, he, ho⟩

/-- The sample caller `CALLER1` (20 bytes 01) is the address of no precompile, on every fork. -/
theorem caller1_noPre (fork : Fork) :
    Precompiles.isPrecompile fork Witness.CALLER1.toU256.toNat = false := by
  have h : Precompiles.addedAt Witness.CALLER1.toU256.toNat = none := by decide
  simp [Precompiles.isPrecompile, h]

/-- The sample contract address: 20 bytes 02. -/
def CONTRACT2 : Address := Vector.replicate 20 2

/-- `withdraw_runs` with no hypothesis left but the fork range: the contract at `CONTRACT2`, the
caller `CALLER1`. From Berlin and before Glamsterdam, under the runner of the interpreter,
`withdraw(1)` runs to the end with no error. -/
theorem withdraw_runs_closed (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas bound : Nat) (evm s : Evm fork Nat) (within : GasMeter.gasHeld evm.gas ≤ bound),
      At CODE (mW b t CONTRACT2 Witness.CALLER1) 0 [] .empty gas
        (wS CONTRACT2 [(balKey Witness.CALLER1, 5)]) ss evm ∧
      Evm.runFrame (step fork) (step_decreases fork) bound
        (processRunner (Meter := Nat) fork bound) evm within = .ok s ∧
      s.error = none ∧ s.output = ByteArray.empty :=
  withdraw_runs hfork hglam b t CONTRACT2 Witness.CALLER1 ss (by decide) (caller1_noPre fork)

end WethVerify.Sanity

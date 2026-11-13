import EthLib.Execution.Proofs.Evm.Call.StaticMessage
import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# A message with at most 2300 gas changes no account and no storage word

The stipend of a call that sends value is 2300 gas (`CALL_STIPEND`). This file proves, by
induction over EthLib's interpreter, what a message that starts with at most 2300 gas can do to
the state, whatever its code is and however deep its own calls go.

`Quiet S S'`: every account of `S'` reads as in `S` (balance, nonce, code hash; an absent
account reads as the empty one), and every storage word of `S'` reads as in `S`. Transient
storage, logs, the substate and the records of reads are NOT in `Quiet`: a frame with 2300 gas
can run TSTORE (100 gas) and LOG.

Why a frame that holds at most 2300 gas is quiet, opcode by opcode (EthLib's gas rules):

- SSTORE fails when the gas left is at most 2300 (the sentry of EIP-2200, from Istanbul). It
  fails before it reads or writes.
- CALL and CALLCODE with a value that is not 0 pay more than 2300 before the message is sent
  (`callExtraGas_bounds`: 9000 before Glamsterdam), so a call that is sent has value 0.
  DELEGATECALL and STATICCALL move no value.
- CREATE and CREATE2 pay 32000 (12000 from Glamsterdam) before anything else.
- SELFDESTRUCT pays 5000 (from Tangerine Whistle) before it moves the balance.
- TSTORE changes transient storage only. LOG changes the logs only.
- Every other instruction keeps the state, up to the records of reads (EthLib's `StaticStep`).
- A precompile keeps the state.
- A message that a quiet frame sends has less gas than the frame (EthLib's `Decreases`), so it
  is quiet too: strong induction on the gas of the message (`processMessage_quiet`).
- EIP-7702: a call to a delegated account runs the code of the delegate with the gas of the
  call. That code is any code, so the statement covers it.

## Theorems

- `lowResult_step`: one step of a frame that holds at most 2300 gas keeps `Quiet`, and a message
  that it sends is a call (not a creation) that moves no value.
- `quiet_runFrame`: a whole run of such a frame.
- `processMessage_quiet`: a call message with at most 2300 gas that EthLib's `processMessage`
  ends with no error: the end state is `Quiet` from the state after the move of its own value
  (when it moves one), or from the state it is sent from (when it moves none).
- `quiet_processMessage_noValue`: with no value moved, also when it ends with an error.

Forks: from Istanbul (the SSTORE sentry) on, for every gas meter that EthLib calls lawful. The
users of this file apply it before Glamsterdam with the one-counter meter.

Nothing here is about one token.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TokenKit.Stipend

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState)
open EthLib.Execution.Evm
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Every account and every storage word of `S'` reads as in `S`. -/
def Quiet (S S' : TransactionState) : Prop :=
  (∀ a, S'.getAccount a = S.getAccount a) ∧ ∀ a k, S'.getStorage a k = S.getStorage a k

theorem Quiet.refl (S : TransactionState) : Quiet S S := ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem Quiet.trans {a b c : TransactionState} (h1 : Quiet a b) (h2 : Quiet b c) : Quiet a c :=
  ⟨fun x => (h2.1 x).trans (h1.1 x), fun x k => (h2.2 x k).trans (h1.2 x k)⟩

theorem Quiet.of_sameOutside {S S' : TransactionState}
    (h : TransactionState.SameOutside [] S S') : Quiet S S' :=
  ⟨fun a => by
      have := (h a (by simp)).1
      simp [TransactionState.getAccount, this],
    fun a k => (h a (by simp)).2.1 k⟩

theorem Quiet.of_touchesOnly {touched : List Address} {S S' : TransactionState}
    (h : TouchesOnly touched S S') : Quiet S S' :=
  ⟨h.getAccount_eq, h.2.1⟩

theorem Quiet.of_staticStep {a b : Evm fork Meter} (h : StaticStep a b) :
    Quiet a.state b.state :=
  Quiet.of_sameOutside h.state

theorem Quiet.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    Quiet a.state b.state := by
  rw [h.state]
  exact Quiet.refl _

/-- The state at the start of a message reads as the state it is sent from (before Paris the
target is touched, and an absent account reads as the empty one). -/
theorem quiet_startState (message : Message fork) (state : TransactionState) :
    Quiet state (startState fork message state) := by
  obtain ⟨touched, h, -⟩ := touchesOnly_startState message state
  exact Quiet.of_touchesOnly h

/-! ## Prices above the stipend -/

/-- A frame that holds at most 2300 gas, reaches a frame for free and then pays `n`: `n` is at
most 2300. -/
theorem low_of_pays {n : Nat} {a b c : Evm fork Meter} (h0 : Pays 0 a b) (h : Pays n b c)
    (hlow : GasMeter.gasHeld a.gas ≤ 2300) : n ≤ 2300 := by
  have := h0.gasHeld
  have := h.gasHeld
  omega

/-- A frame reached for free holds no more gas. -/
theorem low_of_free {a b : Evm fork Meter} (h0 : Pays 0 a b)
    (hlow : GasMeter.gasHeld a.gas ≤ 2300) : GasMeter.gasHeld b.gas ≤ 2300 := by
  have := h0.gasHeld
  omega

/-- SELFDESTRUCT costs 5000 or more from Tangerine Whistle. -/
theorem selfdestructCost_ge (htw : .tangerineWhistle ≤ fork) (cold creates : Bool) :
    5000 ≤ selfdestructCost fork cold creates := by
  have hb : (gasSchedule fork).OPCODE_SELFDESTRUCT_BASE = 5000 := by
    simp only [gasSchedule]
    simp only [htw, ↓reduceIte]
  unfold selfdestructCost
  dsimp only
  omega

/-- A creation costs more than 2300 at every fork. -/
theorem createBaseCost_gt (fork : Fork) : 2300 < createBaseCost fork := by
  unfold createBaseCost
  split <;> decide

/-! ## The instructions that could write -/

/-- From Istanbul, SSTORE does not complete in a frame that holds at most 2300 gas. -/
theorem sstoreStep_ne_ok_of_low [LawfulGasMeter Meter] (hist : .istanbul ≤ fork)
    {evm after : Evm fork Meter} (hlow : GasMeter.gasHeld evm.gas ≤ 2300) :
    sstoreStep evm ≠ .ok after := by
  intro h
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hnot
    have p : Pays 0 evm e2 := ((popWord_pays h1).trans (popWord_pays h2)).mono
    have g := low_of_free p hlow
    have l := LawfulGasMeter.gasLeft_le_gasHeld e2.gas
    exact hnot ⟨hist, Nat.le_trans l g⟩

/-- TSTORE changes transient storage only. -/
theorem quiet_tstoreStep {evm after : Evm fork Meter} (h : tstoreStep evm = .ok after) :
    Quiet evm.state after.state := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  have hs : e3.state = evm.state := by
    rw [(chargeGas_sameContext h3).state, (popWord_sameContext h2).state,
      (popWord_sameContext h1).state]
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · cases h
    show Quiet evm.state (e3.state.setTransientStorage _ _ _)
    rw [hs]
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- From Tangerine Whistle, SELFDESTRUCT in a frame that holds at most 2300 gas halts the frame
with its reads, or fails: it never moves the balance. -/
theorem quiet_selfdestructStep_of_low [LawfulGasMeter Meter] (htw : .tangerineWhistle ≤ fork)
    {evm after : Evm fork Meter} (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (h : selfdestructStep fork evm = .ok after) : Quiet evm.state after.state := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  have pa : Pays 0 e1 e2 := by
    have := accessAddress_pays e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c := ((StaticStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (staticStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    have p : Pays 0 evm (recordAccountRead e2 (toAddressMasked w)) :=
      (((popWord_pays h1).trans pa).trans (recordAccountRead_pays _ _)).mono
    have hle := low_of_pays p (chargeGas_pays h3) hlow
    exact absurd (Nat.le_trans (selfdestructCost_ge htw _ _) hle) (by decide)
  · exact Quiet.of_staticStep (c.trans (staticStep_exceptionalHalt _ _))

/-- A creation does not complete in a frame that holds at most 2300 gas. -/
theorem createStep_ne_ok_of_low [LawfulGasMeter Meter] {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hlow : GasMeter.gasHeld evm.gas ≤ 2300) :
    createStep create2 evm ≠ .ok result := by
  intro h
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have p : Pays 0 evm e4 :=
    ((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
      (popSalt_pays h4)).mono
  have hle := low_of_pays p (chargeGasAndMemory_pays h5) hlow
  have hb := createBaseCost_gt fork
  exact absurd (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hle)
    (Nat.not_le.mpr hb)

/-- Each instruction that gives the next frame keeps `Quiet` in a frame that holds at most 2300
gas, from Istanbul. -/
theorem quiet_instruction_of_low [LawfulGasMeter Meter] (hist : .istanbul ≤ fork) {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (h : run evm = .ok after) : Quiet evm.state after.state := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hist
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_staticStep (staticStep_returnOpStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact Quiet.of_staticStep (staticStep_accountStep hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hf
    case sload => subst hf; exact Quiet.of_staticStep (staticStep_sloadStep h)
    case sstore => subst hf; exact absurd h (sstoreStep_ne_ok_of_low hist hlow)
  rcases orElse_eq_some hrun with hf | hrun
  · cases op <;> simp only [transientStorageStep, reduceCtorEq] at hf <;> split at hf <;>
      simp only [Option.some.injEq, reduceCtorEq] at hf <;> subst hf
    all_goals first
      | exact Quiet.of_sameContext (tloadStep_sameContext h)
      | exact quiet_tstoreStep h
  rcases orElse_eq_some hrun with hf | hf
  · cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    obtain ⟨_, _, _, _, hs, _⟩ := logStep_eq_ok h
    rw [hs]
    exact Quiet.refl _
  · cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
    subst hf
    exact quiet_selfdestructStep_of_low htw hlow h

/-! ## The calls -/

/-- A message that a frame with at most 2300 gas may send: a call, and it moves no value. -/
def LowMessage (message : Message fork) : Prop :=
  message.target.isSome = true ∧ ¬(message.shouldTransferValue = true ∧ message.value ≠ 0)

/-- What a step of a frame that holds at most 2300 gas gives: the next frame, with a state that
reads the same, or a message that moves no value, sent from a frame whose state reads the same,
after which the frame goes on with the state of the frame that ends the message. -/
def LowResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => Quiet evm.state after.state
  | .child caller message resume =>
    Quiet evm.state caller.state ∧ LowMessage message ∧
      ∀ child after, resume child = .ok after → after.state = child.state

theorem LowResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : Quiet evm.state evm'.state) (r : LowResult evm' result) : LowResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, m, m4⟩ := r
    exact ⟨h.trans c, m, m4⟩

/-- A call that pays in a frame that holds at most 2300 gas sends no value. -/
theorem payCall_value_zero [LawfulGasMeter Meter] {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (above : call.value ≠ 0 → GasCosts.CALL_STIPEND < extraGas)
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    call.value = 0 := by
  apply Classical.byContradiction
  intro hv
  have hab : 2300 < extraGas := above hv
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    have := (chargeGas_pays h1).gasHeld
    omega
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    have g := (chargeGas_pays h1).gasHeld
    have hc : extraGas ≤ (messageCallGas fork call.value call.gas.toNat
        (GasMeter.gasLeft evm.gas) memoryCost extraGas).cost := by
      unfold messageCallGas
      dsimp only
      omega
    omega

theorem lowResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (hmsg : LowMessage message)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    LowResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact Quiet.of_staticStep ((⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩ : StaticStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans
        (staticStep_skipCall hs))
  · cases h
    exact ⟨Quiet.refl _, hmsg, fun child after hres => state_resumeCall hres⟩

theorem lowResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (hv : call.value = 0)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    LowResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  dsimp only at h
  have pre : StaticStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have refill : StaticStep (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget)
          (refillStateGas (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) := ⟨StateKept.refl _, rfl, rfl, rfl, rfl⟩
      exact Quiet.of_staticStep ((pre.trans refill).trans (staticStep_skipCall hs))
  · refine LowResult.lift (Quiet.of_staticStep pre) (lowResult_genericCall ?_ h)
    refine ⟨rfl, ?_⟩
    rintro ⟨ht, hval⟩
    cases kind <;> simp_all

/-- Each call in a frame that holds at most 2300 gas keeps `Quiet`, and sends no value. -/
theorem lowResult_callStep [LawfulGasMeter Meter] {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (h : callStep kind evm = .ok result) : LowResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨c1, -⟩ := staticStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticStep e1 e2 := by
    have := staticStep_accessAddress e1 call.address
    rwa [hacc] at this
  have pa : Pays 0 e1 e2 := by
    have := accessAddress_pays e1 call.address
    rwa [hacc] at this
  have s3 : StaticStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticStep evm e4 := s3.trans (staticStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have s5 : StaticStep evm e5 := s4.trans (staticStep_payCall h5)
      have p4 : Pays 0 evm e4 :=
        ((((popCallOperands_pays h1).trans pa).trans (recordAccountRead_pays _ call.address)).trans
          (accessDelegation_pays h4)).mono
      have hv : call.value = 0 :=
        payCall_value_zero (low_of_free p4 hlow)
          (callExtraGas_bounds (fork := fork) (kind := kind) (state := e4.state) (call := call)
            (cold := cold) (callee := callee)).2 h5
      exact LowResult.lift (Quiet.of_staticStep s5) (lowResult_finishCall hv h)
    · exact Quiet.of_staticStep (s4.trans (staticStep_exceptionalHalt _ _))
  · exact Quiet.of_staticStep (s3.trans (staticStep_exceptionalHalt _ _))

/-- Each instruction that may send a message, in a frame that holds at most 2300 gas. -/
theorem lowResult_messageInstruction [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (hlow : GasMeter.gasHeld evm.gas ≤ 2300) (h : run evm = .ok result) :
    LowResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact lowResult_callStep hlow h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact lowResult_callStep hlow h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact absurd h (createStep_ne_ok_of_low hlow))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact absurd h (createStep_ne_ok_of_low hlow)
         · cases hrun)

/-- From Istanbul, one step of a frame that holds at most 2300 gas: the state reads the same,
and a message that it sends is a call that moves no value. -/
theorem lowResult_step [LawfulGasMeter Meter] (hist : .istanbul ≤ fork) {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (h : step fork evm = .ok result) : LowResult evm result := by
  unfold step at h
  split at h
  · rename_i hlt
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact quiet_instruction_of_low hist hop hlow hr
      · split at h
        · rename_i hcall
          exact lowResult_messageInstruction hcall hlow h
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact Quiet.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

section Loop

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- A whole run of a frame that holds at most 2300 gas keeps `Quiet`, when each step does and
the runner ends each message that moves no value and has at most 2300 gas in a state that reads
as the state of its caller. -/
theorem quiet_runFrame
    (stepOk : ∀ {evm : Evm fork Meter} {result : StepResult fork Meter},
      GasMeter.gasHeld evm.gas ≤ 2300 → step evm = .ok result → LowResult evm result)
    (runs : ∀ {caller : Evm fork Meter} {message : Message fork} {lt : message.gas < bound}
      {c : Evm fork Meter} {used : GasMeter.gasHeld c.gas ≤ message.gas},
      message.gas ≤ 2300 → LowMessage message →
      runChild caller message lt = .ok ⟨c, used⟩ → Quiet caller.state c.state)
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hlow : GasMeter.gasHeld evm.gas ≤ 2300)
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    Quiet evm.state after.state := by
  fun_induction runFrame step decreases bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact Quiet.refl _
  case case3 =>
    rename_i result lower ih
    have n : Quiet _ _ := stepOk hlow result
    exact n.trans (ih (Nat.le_trans (gasHeld_le_of_measure_lt lower) hlow) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact Quiet.refl _
  case case7 =>
    rename_i evm0 within0 hrunning caller message resume result lower1 child used hx after0
      resumed lower ih
    obtain ⟨c0, hP, hres⟩ := stepOk hlow result
    have hq := runs (Nat.le_trans (Nat.le_of_lt lower1.1) hlow) hP hx
    have hs := hres _ _ resumed
    have ih' := ih (Nat.le_trans (gasHeld_le_of_measure_lt lower) hlow) h
    rw [hs] at ih'
    exact (c0.trans hq).trans ih'
  case case8 => cases h; exact Quiet.refl _

end Loop

/-! ## Whole messages -/

/-- From Istanbul, a call message with at most 2300 gas that EthLib's `processMessage` ends with
no error, whatever its code:

- when it moves its value, the move succeeds from the state at its start, and the end state
  reads as the state after the move;
- when it moves no value, the end state reads as the state it is sent from.

Strong induction on the gas of the message: the messages that its frame sends have less gas and
move no value. -/
theorem processMessage_quiet [LawfulGasMeter Meter] (hist : .istanbul ≤ fork) :
    ∀ (n : Nat) (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas),
      message.gas = n → n ≤ 2300 → message.target.isSome = true →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
      ended.val.error = none →
      (message.shouldTransferValue = true ∧ message.value ≠ 0 →
        ∃ moved, (startState fork message state).moveEther fork message.caller
            message.currentTarget message.value = .ok moved ∧ Quiet moved ended.val.state) ∧
      (¬(message.shouldTransferValue = true ∧ message.value ≠ 0) →
        Quiet state ended.val.state) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message state substate meter held hn hle htarget ended h herr
    rw [processMessage] at h
    obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
    have hval := congrArg Subtype.val rolled
    simp only at hval
    have he0 : ended.val = ended0.val := by
      by_cases hs : ended0.val.error.isSome = true
      · exfalso
        rw [← hval] at herr
        unfold rollbackOnError at herr
        rw [if_pos hs] at herr
        have hnone : ended0.val.error = none := herr
        rw [hnone] at hs
        cases hs
      · rw [← hval]
        unfold rollbackOnError
        rw [if_neg hs]
    have hlim : GasMeter.gasHeld meter ≤ 2300 := by omega
    rw [he0]
    dsimp only at hdo
    split at hdo
    all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
    all_goals
      have hq : Quiet state1 ended0.val.state := by
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            exact quiet_runFrame (hlow := hlim) (h := hrun)
              (fun hl hstep => lowResult_step hist hl hstep)
              (by
                intro caller' message' lt c used hle' hP hrun'
                split at hrun'
                · by_cases herr' : c.error.isSome = true
                  · exact Quiet.of_sameOutside (processMessage_sameOutside_of_error hrun' herr')
                  · have hnone : c.error = none := Option.not_isSome_iff_eq_none.mp herr'
                    exact (ih message'.gas (by omega) message' caller'.state _ _ _ rfl hle'
                      hP.1 ⟨c, used⟩ hrun' hnone).2 hP.2
                · have := hP.1
                  simp_all)
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact Quiet.refl _
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact Quiet.of_staticStep (staticStep_runPrecompile hrp)
            · cases hdo
              exact Quiet.refl _
    · have ht := ‹message.shouldTransferValue = true ∧ message.value ≠ 0›
      exact ⟨fun _ => ⟨state1, Base.mapError_ok_iff.mp hm, hq⟩, fun hno => absurd ht hno⟩
    · have ht := ‹¬(message.shouldTransferValue = true ∧ message.value ≠ 0)›
      cases hm
      exact ⟨fun h1 => absurd h1 ht, fun _ => (quiet_startState message state).trans hq⟩

/-- From Istanbul, a call message with at most 2300 gas that moves no value and that EthLib's
`processMessage` ends, with or without an error: the end state reads as the state it is sent
from. -/
theorem quiet_processMessage_noValue [LawfulGasMeter Meter] (hist : .istanbul ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Meter}
    {held : GasMeter.gasHeld meter ≤ message.gas} (hle : message.gas ≤ 2300)
    (htarget : message.target.isSome = true)
    (hno : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0)) {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    Quiet state ended.val.state := by
  by_cases herr : ended.val.error.isSome = true
  · exact Quiet.of_sameOutside (processMessage_sameOutside_of_error h herr)
  · exact (processMessage_quiet hist message.gas message state substate meter held rfl hle
      htarget ended h (Option.not_isSome_iff_eq_none.mp herr)).2 hno

end TokenKit.Stipend

import WethVerify.Weth.TxFrame

/-!
# Every message at any depth, for an invariant that reads the storage and the ether of `L`

GENERIC file: nothing here is about WETH (see the note at the top of `TxFrame.lean`; listed in
`status.json` under `to_merge_into_kit`).

`TokenKit/Seq/Run.lean` proves `processMessage_good_local` for an invariant `P` with
`StorageOnly L P`. Here the invariant may also read the ether of `L`, as long as more ether does
not break it:

- `Mono L P`: `P` is kept by every change of the state that keeps the storage of `L` and does
  not lower its ether.
- `FrameKeepsV fork L CODE P Q`: what a token proves from its bytecode, for EthLib's REAL runner
  (`processRunner`): a frame of `CODE` at `L`, started by `processMessage` from a good state
  (the move of value included: `startSt`), whose message satisfies `Q` and is `Paid`, that ends
  with no error, keeps `P`. There is no hypothesis on the runner: the token proof must handle
  the messages that its own frame sends.
- `processMessage_good_bal`, `processCreateMessage_good_bal`: a message at ANY depth, whatever
  code it runs and whatever it calls, re-entering `L` included, that starts from a good state
  ends in a good state, with or without an error. Every fork.

The induction is the one of `processMessage_ind_local`. The facts on the code of `L` (it stays
`CODE`, a creation is at another address, a call to `L` runs `CODE`) are taken from the kit,
used with the invariant `True`. The storage of `L` under a step of a frame at another address is
taken from the kit too (`res_step`, used with the invariant "the storage of `L` is the storage
before the step"). The ether of `L` is from `TxFrame.lean`.

Hypotheses: `delegatedAddress CODE = none`, `Mono`, `Clean` of the run (the kit's), and the
message is `Paid` (true of every message that a frame at another address sends, and of the
message of a transaction whose sender is not `L`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WethVerify.Bal

open TokenKit
open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open TokenKit.Seq

variable {fork : Fork} {L : Address} {CODE : ByteArray} {P : State.TransactionState → Prop}
  {Q : Message fork → TransactionState → Prop}

/-! ## The interface -/

/-- The invariant `P` is kept by every change of the state that keeps the storage of `L` and
does not lower its ether. -/
def Mono (L : Address) (P : State.TransactionState → Prop) : Prop :=
  ∀ S S', (∀ k, S'.getStorage L k = S.getStorage L k) → Up L S S' → P S → P S'

/-- What a token proves from its bytecode, for EthLib's real runner. `state` is the state before
the move of value of the message, `state1` the state after it, where the frame starts. -/
def FrameKeepsV (fork : Fork) (L : Address) (CODE : ByteArray)
    (P : State.TransactionState → Prop) (Q : Message fork → TransactionState → Prop) : Prop :=
  ∀ {bound : Nat} {message : Message fork}
    {state state1 : State.TransactionState} {substate : Substate} {gas : Nat}
    {evm s : Evm fork Nat}
    (within : GasMeter.gasHeld evm.gas ≤ bound),
    message.currentTarget = L → message.code = CODE → message.data.size < 2 ^ 256 →
    Paid L message → Good L CODE P state → startSt message state = .ok state1 →
    Q message state1 →
    UsdtVerify.At CODE message 0 [] .empty gas state1 substate evm →
    Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s →
    s.error = none → P s.state

/-! ## The kit, used with the invariant `True` and with "the storage of `L` is that of `S0`" -/

theorem storageOnly_true : StorageOnly L (fun _ => True) := fun _ _ _ _ => trivial

theorem frameKeepsR_true (G : Nat) : FrameKeepsR fork G L CODE (fun _ => True) Q := by
  unfold FrameKeepsR
  intros
  trivial

theorem storageOnly_eq (L : Address) (S0 : TransactionState) :
    StorageOnly L (fun S => ∀ k, S.getStorage L k = S0.getStorage L k) :=
  fun S S' h hp k => (h k).trans (hp k)

/-! ## One step of a frame at another address -/

/-- A step from the frame `a` to the frame `b` that keeps the message. In a frame at another
address than `L` it keeps a good state good. -/
structure V (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop)
    (a b : Evm fork Nat) : Prop where
  message : b.message = a.message
  good : a.message.currentTarget ≠ L → Good L CODE P a.state → Good L CODE P b.state

theorem V.refl (a : Evm fork Nat) : V L CODE P a a := ⟨rfl, fun _ => id⟩

theorem V.trans {a b c : Evm fork Nat} (hab : V L CODE P a b) (hbc : V L CODE P b c) :
    V L CODE P a c :=
  ⟨hbc.message.trans hab.message,
    fun t g => hbc.good (by rw [hab.message]; exact t) (hab.good t g)⟩

theorem V.of_step (mono : Mono L P) {a b : Evm fork Nat}
    (w : W L CODE (fun S => ∀ k, S.getStorage L k = a.state.getStorage L k) a b)
    (u : U L a b) : V L CODE P a b :=
  ⟨w.message, fun t g =>
    have r := w.good t ⟨g.1, fun _ => rfl⟩
    ⟨r.1, mono _ _ r.2 (u.up t) g.2⟩⟩

theorem v_of_qs (mono : Mono L P) {a b : Evm fork Nat} (h : QS a b) : V L CODE P a b :=
  ⟨h.message, fun _ g =>
    ⟨h.kept.holdsCode g.1, mono _ _ (h.kept.storage g.1.2.1) (up_of_qs h) g.2⟩⟩

theorem v_step_next (mono : Mono L P) (hdel : delegatedAddress CODE = none)
    {evm after : Evm fork Nat} (h : step fork evm = .ok (.next after)) :
    V L CODE P evm after := by
  have r := res_step (L := L) (CODE := CODE)
    (P := fun S => ∀ k, S.getStorage L k = evm.state.getStorage L k)
    (storageOnly_eq L evm.state) hdel h
  have u := resU_step (L := L) h
  exact V.of_step mono r u

theorem v_step_child (mono : Mono L P) (hdel : delegatedAddress CODE = none)
    {evm caller : Evm fork Nat} {message : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (h : step fork evm = .ok (.child caller message resume)) :
    V L CODE P evm caller ∧
      (HoldsCode L CODE evm.state → Sane0 L message ∧
        (evm.message.currentTarget ≠ L → Sane L CODE message ∧ Paid L message)) ∧
      ∀ child after, resume child = .ok after →
        after.message = caller.message ∧ after.state = child.state := by
  obtain ⟨c, s, hres⟩ := res_step (L := L) (CODE := CODE)
    (P := fun S => ∀ k, S.getStorage L k = evm.state.getStorage L k)
    (storageOnly_eq L evm.state) hdel h
  obtain ⟨cu, pu⟩ := resU_step (L := L) h
  exact ⟨V.of_step mono c cu, fun hold => ⟨(s hold).1, fun t => ⟨(s hold).2 t, pu t⟩⟩,
    fun child after hr => ⟨(hres child after hr).1, (hres child after hr).2.1⟩⟩

/-- The run of a frame is a `V` step, when the runner keeps the code of `L` and a good state on
the messages that this frame sends. -/
theorem v_runFrame (mono : Mono L P) (hdel : delegatedAddress CODE = none)
    {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {evm after : Evm fork Nat} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (runs : ∀ caller message lt ended, Sent runChild evm caller message →
      runChild caller message lt = .ok ended →
      (Sane0 L message → HoldsCode L CODE caller.state → HoldsCode L CODE ended.val.state) ∧
      (Sane L CODE message → Paid L message → Good L CODE P caller.state →
        P ended.val.state))
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    V L CODE P evm after := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 => cases h; first | exact V.refl _ | exact v_of_qs mono (qs_exceptionalHalt _ _)
  case case3 =>
    rename_i result _ ih
    have hrunning := ‹Evm.running _ = true›
    exact (v_step_next mono hdel result).trans
      (ih (fun c m lt e hs => runs c m lt e (Sent.next hrunning result hs)) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; first | exact V.refl _ | exact v_of_qs mono (qs_exceptionalHalt _ _)
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    have hrunning := ‹Evm.running _ = true›
    obtain ⟨c, s, hres⟩ := v_step_child (L := L) (CODE := CODE) (P := P) mono hdel hchild
    obtain ⟨hm, hst⟩ := hres _ _ resumed
    obtain ⟨r1, r2⟩ := runs _ _ _ _ (Sent.here hrunning hchild) hran
    refine V.trans ⟨hm.trans c.message, fun t g => ?_⟩
      (ih (fun c m lt e hs => runs c m lt e (Sent.resumed hrunning hchild hran resumed hs)) h)
    rw [hst]
    have gc := c.good t g
    exact ⟨r1 (s g.1).1 gc.1, r2 ((s g.1).2 t).1 ((s g.1).2 t).2 gc⟩
  case case8 => cases h; first | exact V.refl _ | exact v_of_qs mono (qs_exceptionalHalt _ _)

/-! ## Messages -/

/-- The start of a message keeps the code and the storage of `L`. -/
theorem kept_startSt {message : Message fork} {state state1 : TransactionState}
    (h : startSt message state = .ok state1) : Kept L state state1 := by
  unfold startSt at h
  split at h
  · exact (kept_startState message state).trans (kept_moveEther (Base.mapError_ok_iff.mp h))
  · cases h
    exact kept_startState message state

/-- The start of a message whose value does not come from `L` does not lower the ether of
`L`. -/
theorem up_startSt {message : Message fork} {state state1 : TransactionState}
    (h : startSt message state = .ok state1)
    (hp : message.shouldTransferValue = true → message.caller ≠ L) : Up L state state1 := by
  unfold startSt at h
  split at h
  · rename_i hc
    exact (up_startState message state).trans
      (up_moveEther (Base.mapError_ok_iff.mp h) (hp hc.1))
  · cases h
    exact up_startState message state

/-- The end of a creation at another address than `L` keeps `P`. -/
theorem p_depositCode (mono : Mono L P)
    {snapshot : TransactionState} {evm after : Evm fork Nat}
    (h : depositCode fork snapshot evm = .ok after)
    (hp : evm.state.parent = snapshot.parent) (hne : L ≠ evm.message.currentTarget)
    (gs : P snapshot) (ge : P evm.state) : P after.state := by
  have restored : P (evm.state.restoreTxState snapshot) :=
    mono _ _ (fun k => TransactionState.getStorage_restoreTxState hp L k) (up_restore hp) gs
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact restored
  split at h
  · cases h
    exact restored
  split at h
  · cases h
    exact restored
  split at h
  · cases h
    split
    · exact restored
    · exact ge
  split at h
  · cases h
    exact restored
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hset := Base.mapError_ok_iff.mp hst
  exact mono _ _
    (fun k => (TransactionState.sameOutside_setCode hset L (by simpa using hne)).2.1 k)
    (up_setCode hset hne) ge

/-- Every call and every creation, by strong induction on the gas of the message, for a clean
run. -/
theorem processMessage_ind_bal (mono : Mono L P) (fk : FrameKeepsV fork L CODE P Q)
    (hdel : delegatedAddress CODE = none) (n : Nat) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Nat)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        Clean L CODE Q message state substate meter →
        Sane L CODE message → Paid L message → Good L CODE P state → P ended.val.state) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Nat)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CleanCreate L CODE Q message state substate meter →
        message.currentTarget ≠ L →
        (message.shouldTransferValue = true → message.caller ≠ L) →
        Good L CODE P state → P ended.val.state) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Nat) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          Clean L CODE Q message state substate meter →
          Sane L CODE message → Paid L message → Good L CODE P state →
          P ended.val.state := by
      intro message state substate meter held hn ended h clean sane paid g
      have hpar := parent_processMessage h
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hval := congrArg Subtype.val rolled
      simp only at hval
      have hp0 : ended0.val.state.parent = state.parent := by
        rw [← hval, parent_rollbackOnError] at hpar
        exact hpar
      have core : ended0.val.error = none → P ended0.val.state := by
        dsimp only at hdo
        split at hdo
        all_goals rename_i hc
        all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
        all_goals
          have hm' : startSt message state = .ok state1 := by
            unfold startSt
            first
            | (rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact hm)
            | (rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact hm)
          have k1 : Kept L state state1 := kept_startSt hm'
          have g1 : Good L CODE P state1 :=
            ⟨k1.holdsCode g.1, mono _ _ (k1.storage g.1.2.1) (up_startSt hm' paid.1) g.2⟩
          rcases hpa : precompileAddress fork message with _ | addr
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
            · rename_i after hrun
              cases hdo
              have hrun' : runFrame (step fork) (step_decreases fork) message.gas
                  (Logic.processRunner fork (Meter := Nat) message.gas)
                  (startFrame message state1 (startSub message substate) meter) held =
                    .ok after := hrun
              have fo : FrameOf message state substate meter
                  (startFrame message state1 (startSub message substate) meter) :=
                ⟨hpa, state1, hm', rfl⟩
              intro herr
              by_cases ht : message.currentTarget = L
              · obtain ⟨hcode, -, hsize⟩ := sane ht
                unfold FrameKeepsV at fk
                exact fk (gas := meter) (substate := startSub message substate) held ht hcode
                  hsize paid g hm' (clean _ (Occurs.self hm') ht)
                  ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
                  hrun' herr
              · have v : V L CODE P
                    (startFrame message state1 (startSub message substate) meter) after := by
                  refine v_runFrame mono hdel ?_ hrun'
                  rintro caller' message' lt ⟨c, used⟩ hs hrun''
                  have cr : CleanRun L CODE Q caller' message' :=
                    fun e he => clean e (Occurs.sub fo hs he)
                  dsimp only [Logic.processRunner] at hrun''
                  split at hrun''
                  · have hsome : message'.target.isSome = true :=
                      Option.isSome_iff_exists.mpr ⟨_, by assumption⟩
                    have rk := (processMessage_ind_local (P := fun _ => True) (Q := Q)
                      storageOnly_true (frameKeepsR_true message'.gas) hdel message'.gas
                      (Nat.le_refl _)).1 message' caller'.state _ _ _
                      rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.call hsome he))
                    have r := (ih message'.gas (by omega)).1 message' caller'.state _ _ _
                      rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.call hsome he))
                    exact ⟨fun _ => rk.2.1, r⟩
                  · have htgt : message'.target = none := by assumption
                    have rk := (processMessage_ind_local (P := fun _ => True) (Q := Q)
                      storageOnly_true (frameKeepsR_true message'.gas) hdel message'.gas
                      (Nat.le_refl _)).2 message' caller'.state _ _ _
                      rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.create htgt he))
                    have r := (ih message'.gas (by omega)).2 message' caller'.state _ _ _
                      rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.create htgt he))
                    refine ⟨fun s0 => (rk (s0 htgt)).1,
                      fun sane' paid' g' => r ?_ paid'.1 g'⟩
                    intro e
                    have hsome := (sane' e).2.1
                    rw [htgt] at hsome
                    cases hsome
                exact (v.good ht g1).2
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
              intro _
              exact g1.2
            · split at hdo
              · rename_i after hrp
                cases hdo
                have q := qs_runPrecompile hrp
                intro _
                exact mono _ _ (q.kept.storage g1.1.2.1) (up_of_qs q :) g1.2
              · cases hdo
                intro _
                exact g1.2
      rw [← hval]
      unfold rollbackOnError
      split
      · exact mono _ _ (fun k => TransactionState.getStorage_restoreTxState hp0 L k)
          (up_restore hp0) g.2
      · rename_i herr
        have hnone : ended0.val.error = none := by
          cases he : ended0.val.error with
          | none => rfl
          | some x =>
            rw [he] at herr
            exact absurd rfl herr
        exact core hnone
    refine ⟨call, ?_⟩
    intro message state substate meter held hn ended h clean hne hcaller g
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      have rk := (processMessage_ind_local (P := fun _ => True) (Q := Q)
        storageOnly_true (frameKeepsR_true n) hdel n (Nat.le_refl _)).1 message prepared
        substate meter held hn _ hrun (fun e he => clean e (OccursCreate.init hp he))
      have rm : evm.message = message := rk.1
      have kp : Kept L state prepared := kept_prepareCreation hp hne.symm
      have gp : Good L CODE P prepared :=
        ⟨kp.holdsCode g.1, mono _ _ (kp.storage g.1.2.1) (up_prepareCreation hp) g.2⟩
      have r := call message prepared substate meter held hn _ hrun
        (fun e he => clean e (OccursCreate.init hp he))
        (fun e => absurd e hne) ⟨hcaller, fun e => absurd e hne⟩ gp
      have hpp : evm.state.parent = state.parent :=
        (parent_processMessage hrun).trans (parent_prepareCreation hp)
      exact p_depositCode mono ‹depositCode _ _ _ = .ok _› hpp
        (by rw [rm]; exact hne.symm) g.2 r

/-! ## The main results, run-local -/

/-- A sane and `Paid` call from a good state, whose run is clean, ends in a good state, with or
without an error. Every fork, every code that the call runs, every message that it sends. -/
theorem processMessage_good_bal (mono : Mono L P) (fk : FrameKeepsV fork L CODE P Q)
    (hdel : delegatedAddress CODE = none)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (sane : Sane L CODE message) (paid : Paid L message) (g : Good L CODE P state)
    (clean : Clean L CODE Q message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Good L CODE P ended.val.state :=
  ⟨((processMessage_ind_local (P := fun _ => True) (Q := Q) storageOnly_true
      (frameKeepsR_true message.gas) hdel message.gas (Nat.le_refl _)).1 message state substate
      meter held rfl ended h clean).2.1 g.1,
    (processMessage_ind_bal mono fk hdel message.gas).1 message state substate meter held rfl
      ended h clean sane paid g⟩

/-- A creation at another address than `L`, whose value does not come from `L`, from a good
state, whose run is clean, ends in a good state. -/
theorem processCreateMessage_good_bal (mono : Mono L P) (fk : FrameKeepsV fork L CODE P Q)
    (hdel : delegatedAddress CODE = none)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended}
    (hne : message.currentTarget ≠ L)
    (hcaller : message.shouldTransferValue = true → message.caller ≠ L)
    (g : Good L CODE P state)
    (clean : CleanCreate L CODE Q message state substate meter)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    Good L CODE P ended.val.state :=
  ⟨((processMessage_ind_local (P := fun _ => True) (Q := Q) storageOnly_true
      (frameKeepsR_true message.gas) hdel message.gas (Nat.le_refl _)).2 message state substate
      meter held rfl ended h clean hne).1 g.1,
    (processMessage_ind_bal mono fk hdel message.gas).2 message state substate meter held rfl
      ended h clean hne hcaller g⟩

end WethVerify.Bal

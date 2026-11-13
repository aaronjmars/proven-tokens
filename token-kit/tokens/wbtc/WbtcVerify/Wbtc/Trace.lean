import WbtcVerify.Wbtc.Reenter
import EthLib.Execution.Proofs.Evm.Interpreter
import EthLib.Execution.Proofs.Evm.Logic.Reach
import EthLib.Execution.Proofs.Evm.Logic.GasMono

/-!
# The reentrancy induction on RUN-LOCAL hypotheses (what happens during this run)

GENERIC: nothing here is about a particular token. It builds on `Reenter.lean` (unchanged) and
replaces its two universal hypotheses by hypotheses on the events of ONE run.

`Reenter.lean` proves "a good state stays good through every message" from
- a fact `FrameKeeps` about the code of `L` that must hold for EVERY message (so a token has to
  assume its keccak separation for every list of addresses: `SepAll`), and
- `NoCollision CODE`: NO byte string has the hash of `CODE` (EthLib keeps the code of every
  account in one table under its hash, `State.setCode` overwrites, so a creation that deposits a
  colliding code would change what `L` runs: the model does not let us avoid this).
Both are global and almost certainly false as mathematics. Here they are asked only of what the
run at hand really does.

## What "during this run" means

- `Sent runChild evm caller msg`: while EthLib's `runFrame` walks the frame `evm` (with the
  runner `runChild`), a step hands the message `msg` to the runner, from the frame `caller`. It
  is an inductive relation that follows the loop of `runFrame` case by case.
- `Event`: `enter m` (the interpreter starts the message `m`), `deposit a code` (a creation at
  `a` whose init code ended with no error reaches the deposit of `code`).
- `Occurs message state substate meter e`: the event `e` happens in the run of
  `processMessage fork message state substate meter`: the message itself, or an event of a
  message that its frame sends (`Sent` with the real runner `processRunner`), at any depth.
  `OccursRun caller msg e` (the run that the real runner makes of `msg`), `OccursCreate`
  (`processCreateMessage`) likewise. They mirror the definitions of EthLib exactly: the frame is
  `FrameOf` (the state after the move of value), a call starts from `caller.state` and
  `caller.substate.child`, a creation from the prepared state.
- `EventOk L CODE Q e`: an entered message that runs at `L` satisfies `Q` (for a token:
  `Sep (callKeys m)`); a deposited code with the hash of `CODE` is `CODE`.
- `Clean L CODE Q ...`: every event of the run is ok. `CleanRun`, `CleanCreate`, `CleanFrame`
  for the other three kinds of run.

## Results

- `FrameKeepsQ`: `Reenter.FrameKeeps` with the extra hypothesis `Q message` on the message of
  the frame (this is what a token proves from its bytecode with its LOCAL keccak hypothesis).
- `processMessage_good_local`, `processCreateMessage_good_local`, `processRunner_good_local`,
  `runFrame_keeps_local`: the results of `Reenter.lean` with `Clean...` in place of the global
  hypotheses, for the real interpreter, every callee, reentry included.
- `clean_of_global` (and the three siblings): the global hypotheses (`Q` for every message,
  `NoCollision CODE`) imply `Clean` for every run, so the global form is a corollary and nothing
  is lost.
- `clean_of_no_sent`, `not_sent_of_failing`, `not_sent_of_reaches`, `not_sent_of_specG`: a run
  whose frame sends no message is clean as soon as its own message is ok; a frame that runs to
  its end under a runner that always fails, or that meets a path specification `Logic.SpecG`,
  sends no message. With these the condition is checked on real runs (`TraceWit.lean`).
- `Sent.of_reaches`, `Sent.of_step_child`: to list the messages of a frame that does call, from
  its steps (not used here; for a witness of a calling function).

How the universal assumption of `FrameKeepsQ` on the runner is met with run-local knowledge: the
frame is run again with the runner `only runChild evm`, which equals `runChild` on the messages
that the frame sends and fails on every other message; `runFrame_agree` shows that the run is the
same, and for `only` the universal assumption needs the sent messages only.

Hypotheses: `delegatedAddress CODE = none` (closed fact of a token), `StorageOnly`.
Not covered: what `Reenter.lean` does not cover (the end of a transaction, a creation at `L`).
The condition `Clean` is an over-approximation in one place only: `deposit` also lists a code
that fails the size limit, the 0xEF rule or the deposit gas (it is then not written).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace WbtcVerify.Trace

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib
open EthLib.Execution
open EthLib.Execution.State (TransactionState EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open WbtcVerify.Reenter

variable {fork : Fork}

/-! ## The messages that a frame sends -/

/-- While `runFrame` walks the frame `evm` with the runner `runChild`, a step hands the message
`msg` to the runner, from the frame `caller`. -/
inductive Sent {bound : Nat} (runChild : MessageRunner fork Nat bound) :
    Evm fork Nat → Evm fork Nat → Message fork → Prop
  /-- The step of `evm` sends the message. -/
  | here {evm caller : Evm fork Nat} {message : Message fork}
      {resume : Evm fork Nat → Except EvmError (Evm fork Nat)} :
      evm.running = true → step fork evm = .ok (.child caller message resume) →
      Sent runChild evm caller message
  /-- The step of `evm` gives the frame `after`, which sends the message later. -/
  | next {evm after c : Evm fork Nat} {m : Message fork} :
      evm.running = true → step fork evm = .ok (.next after) →
      Sent runChild after c m → Sent runChild evm c m
  /-- The step of `evm` sends another message, the runner ends it, the frame resumes as `after`,
  which sends the message later. -/
  | resumed {evm caller after c : Evm fork Nat} {message m : Message fork}
      {resume : Evm fork Nat → Except EvmError (Evm fork Nat)} {lt : message.gas < bound}
      {child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ message.gas }} :
      evm.running = true → step fork evm = .ok (.child caller message resume) →
      runChild caller message lt = .ok child → resume child.val = .ok after →
      Sent runChild after c m → Sent runChild evm c m

/-- The runner that equals `runChild` on the messages that the frame `evm0` sends, and fails on
every other message. -/
noncomputable def only {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (evm0 : Evm fork Nat) : MessageRunner fork Nat bound :=
  fun caller message lt =>
    haveI := Classical.propDecidable (Sent runChild evm0 caller message)
    if Sent runChild evm0 caller message then runChild caller message lt
    else .error (.unspecifiedOpcode 0)

theorem only_eq {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm0 c : Evm fork Nat}
    {m : Message fork} (hs : Sent runChild evm0 c m) (lt : m.gas < bound) :
    only runChild evm0 c m lt = runChild c m lt := by
  unfold only
  simp only [hs, ite_true]

theorem only_ok {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm0 c : Evm fork Nat}
    {m : Message fork} {lt : m.gas < bound}
    {child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ m.gas }}
    (h : only runChild evm0 c m lt = .ok child) :
    Sent runChild evm0 c m ∧ runChild c m lt = .ok child := by
  unfold only at h
  by_cases hs : Sent runChild evm0 c m
  · simp only [hs, ite_true] at h
    exact ⟨hs, h⟩
  · simp only [hs, ite_false] at h
    cases h

/-- A run of a frame is the same under every runner that agrees with its runner on the messages
that the frame sends. -/
theorem runFrame_agree {bound : Nat} {r r' : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (agree : ∀ c m lt, Sent r evm c m → r' c m lt = r c m lt)
    (h : runFrame (step fork) (step_decreases fork) bound r evm within = .ok s) :
    runFrame (step fork) (step_decreases fork) bound r' evm within = .ok s := by
  fun_induction runFrame (step fork) (step_decreases fork) bound r evm within
  case case1 => cases h
  case case2 =>
    cases h
    exact runFrame_of_step_eq_error (by assumption) (by assumption)
      (Bool.eq_false_iff.mpr (by assumption))
  case case3 =>
    rename_i result _ ih
    have hrunning := ‹Evm.running _ = true›
    rw [runFrame_of_step_eq_next hrunning result]
    exact ih (fun c m lt hs => agree c m lt (Sent.next hrunning result hs)) h
  case case4 => cases h
  case case5 => cases h
  case case6 =>
    rename_i hchild _ _ _ hran _ failed _
    have hrunning := ‹Evm.running _ = true›
    cases h
    exact runFrame_of_step_eq_child_error hrunning hchild _
      ((agree _ _ _ (Sent.here hrunning hchild)).trans hran) failed
      (Bool.eq_false_iff.mpr (by assumption))
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    have hrunning := ‹Evm.running _ = true›
    rw [runFrame_of_step_eq_child hrunning hchild _
      ((agree _ _ _ (Sent.here hrunning hchild)).trans hran) resumed]
    exact ih (fun c m lt hs => agree c m lt (Sent.resumed hrunning hchild hran resumed hs)) h
  case case8 =>
    cases h
    exact runFrame_of_running_eq_false (Bool.eq_false_iff.mpr (by assumption))

/-- A frame that runs to its end under a runner that fails on every message sends no message,
under any runner. -/
theorem not_sent_of_failing {bound bound' : Nat} {r0 : MessageRunner fork Nat bound}
    (r : MessageRunner fork Nat bound') {evm s : Evm fork Nat}
    {within : GasMeter.gasHeld evm.gas ≤ bound}
    (fails : ∀ c m lt child, r0 c m lt ≠ .ok child)
    (h : runFrame (step fork) (step_decreases fork) bound r0 evm within = .ok s)
    (c : Evm fork Nat) (m : Message fork) : ¬ Sent r evm c m := by
  fun_induction runFrame (step fork) (step_decreases fork) bound r0 evm within
  case case1 => cases h
  case case2 =>
    rename_i hstep _
    intro hs
    cases hs with
    | here _ h1 => rw [hstep] at h1; cases h1
    | next _ h1 _ => rw [hstep] at h1; cases h1
    | resumed _ h1 _ _ _ => rw [hstep] at h1; cases h1
  case case3 =>
    rename_i result _ ih
    intro hs
    cases hs with
    | here _ h1 => rw [result] at h1; cases h1
    | next _ h1 h2 =>
      rw [result] at h1
      cases h1
      exact ih h h2
    | resumed _ h1 _ _ _ => rw [result] at h1; cases h1
  case case4 => cases h
  case case5 => cases h
  case case6 =>
    rename_i hchild _ _ _ hran _ failed _
    exact absurd hran (fails _ _ _ _)
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    exact absurd hran (fails _ _ _ _)
  case case8 =>
    rename_i hstop
    intro hs
    cases hs with
    | here h0 _ => exact hstop h0
    | next h0 _ _ => exact hstop h0
    | resumed h0 _ _ _ _ => exact hstop h0

/-- After a step that gives the next frame, the messages that the frame sends are sent by that
next frame. -/
theorem Sent.of_step_next {bound : Nat} {r : MessageRunner fork Nat bound}
    {evm after c : Evm fork Nat} {m : Message fork} (hn : step fork evm = .ok (.next after))
    (hs : Sent r evm c m) : Sent r after c m := by
  cases hs with
  | here _ h1 => rw [hn] at h1; cases h1
  | next _ h1 h2 =>
    rw [hn] at h1
    cases h1
    exact h2
  | resumed _ h1 _ _ _ => rw [hn] at h1; cases h1

/-- A message that a frame sends is sent by every frame that it reaches with the steps of EthLib
that send no message (`Logic.Reaches (Logic.Step fork)`): none is sent on the way. -/
theorem Sent.of_reaches {bound : Nat} {r : MessageRunner fork Nat bound}
    {evm evm1 c : Evm fork Nat} {m : Message fork}
    (hr : Logic.Reaches (Logic.Step fork) evm evm1) (hs : Sent r evm c m) : Sent r evm1 c m := by
  induction hr with
  | refl => exact hs
  | step h1 _ ih =>
    cases h1 with
    | next hr hn => exact ih (hs.of_step_next hn)
    | halt hr hn hab =>
      cases hs with
      | here _ h1 => rw [hn] at h1; cases h1
      | next _ h1 _ => rw [hn] at h1; cases h1
      | resumed _ h1 _ _ _ => rw [hn] at h1; cases h1

/-- At a step that sends the message `msg` from `caller`: a message that the frame sends is that
one, or the runner ends that one, the frame resumes, and the resumed frame sends it. With
`Sent.of_reaches` this lists the messages of a frame whose steps are known (a call site reached
by a path, then the path after it). -/
theorem Sent.of_step_child {bound : Nat} {r : MessageRunner fork Nat bound}
    {evm caller c : Evm fork Nat} {msg m : Message fork}
    {resume : Evm fork Nat → Except EvmError (Evm fork Nat)}
    (hstep : step fork evm = .ok (.child caller msg resume)) (hs : Sent r evm c m) :
    (c = caller ∧ m = msg) ∨
      ∃ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas })
        (after : Evm fork Nat),
        r caller msg lt = .ok child ∧ resume child.val = .ok after ∧ Sent r after c m := by
  cases hs with
  | here _ h1 =>
    rw [hstep] at h1
    cases h1
    exact .inl ⟨rfl, rfl⟩
  | next _ h1 _ => rw [hstep] at h1; cases h1
  | resumed _ h1 h2 h3 h4 =>
    rw [hstep] at h1
    cases h1
    exact .inr ⟨_, _, _, h2, h3, h4⟩

/-- A frame that the steps of EthLib take to a stopped frame, with no message on the way
(`Logic.Reaches (Logic.Step fork)`), sends no message under any runner. -/
theorem not_sent_of_reaches {evm s : Evm fork Nat} (hr : Logic.Reaches (Logic.Step fork) evm s)
    (hstop : s.running = false) {bound' : Nat} (r : MessageRunner fork Nat bound')
    (c : Evm fork Nat) (m : Message fork) : ¬ Sent r evm c m :=
  not_sent_of_failing (bound := evm.gas)
    (r0 := fun _ _ _ => .error (.unspecifiedOpcode 0)) r (within := Nat.le_refl _)
    (fun _ _ _ _ h => by cases h) (Logic.runFrame_of_reaches hr hstop _) c m

/-- A frame that meets the precondition of a specification `Logic.SpecG` (the form of the path
theorems of a token, for the functions that make no call) sends no message under any runner. -/
theorem not_sent_of_specG {Pre Post : Evm fork Nat → Prop} (spec : Logic.SpecG fork Pre Post)
    {evm : Evm fork Nat} (hp : Pre evm) {bound' : Nat} (r : MessageRunner fork Nat bound')
    (c : Evm fork Nat) (m : Message fork) : ¬ Sent r evm c m := by
  obtain ⟨s, hr, hstop, -⟩ := spec evm hp
  exact not_sent_of_reaches (hr.mono And.left) hstop r c m

/-! ## The events of a run -/

/-- An event of a run of the interpreter. -/
inductive Event (fork : Fork) where
  /-- The interpreter starts the message. -/
  | enter (message : Message fork)
  /-- A creation at `address`, whose init code ended with no error, reaches the deposit of
  `code`. -/
  | deposit (address : Address) (code : ByteArray)

/-- The state that `processMessage` starts the frame of a message from: the target is touched
before Paris, and the value is moved. It fails when the move of value fails. -/
def startSt (message : Message fork) (state : TransactionState) :
    Except EvmError TransactionState :=
  if message.shouldTransferValue ∧ message.value ≠ 0 then
    ((startState fork message state).moveEther fork message.caller message.currentTarget
      message.value).mapError .state
  else pure (startState fork message state)

/-- The substate that `processMessage` starts the frame of a message from: with the log of the
move of value, if any. -/
def startSub (message : Message fork) (substate : Substate) : Substate :=
  if message.shouldTransferValue ∧ message.value ≠ 0 then
    { substate with
      logs := pushTransferLog fork substate.logs message.caller message.currentTarget
        message.value }
  else substate

/-- `evm0` is the frame that `processMessage fork message state substate meter` runs with
`runFrame`: the message calls no precompile, and the frame starts from the state after the move
of value. -/
def FrameOf (message : Message fork) (state : TransactionState) (substate : Substate)
    (meter : Nat) (evm0 : Evm fork Nat) : Prop :=
  precompileAddress fork message = none ∧
    ∃ state1, startSt message state = .ok state1 ∧
      evm0 = startFrame message state1 (startSub message substate) meter

mutual

/-- The event `e` happens in the run of `processMessage fork message state substate meter`. -/
inductive Occurs : Message fork → TransactionState → Substate → Nat → Event fork → Prop
  /-- The message itself. -/
  | self (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Nat) : Occurs message state substate meter (.enter message)
  /-- An event of the run of a message that the frame of the message sends. -/
  | sub {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
      {evm0 caller : Evm fork Nat} {msg : Message fork} {e : Event fork} :
      FrameOf message state substate meter evm0 →
      Sent (Logic.processRunner fork (Meter := Nat) message.gas) evm0 caller msg →
      OccursRun caller msg e → Occurs message state substate meter e

/-- The event `e` happens in the run that the runner `processRunner` makes of the message `msg`
sent from the frame `caller`: a call, or a creation. -/
inductive OccursRun : Evm fork Nat → Message fork → Event fork → Prop
  | call {caller : Evm fork Nat} {msg : Message fork} {e : Event fork} :
      msg.target.isSome = true →
      Occurs msg caller.state caller.substate.child
        (GasMeter.start msg.gas msg.reservoir : Nat) e →
      OccursRun caller msg e
  | create {caller : Evm fork Nat} {msg : Message fork} {e : Event fork} :
      msg.target = none →
      OccursCreate msg caller.state caller.substate.child
        (GasMeter.start msg.gas msg.reservoir : Nat) e →
      OccursRun caller msg e

/-- The event `e` happens in the run of
`processCreateMessage fork message state substate meter`. -/
inductive OccursCreate : Message fork → TransactionState → Substate → Nat → Event fork → Prop
  /-- An event of the run of the init code, from the prepared state. -/
  | init {message : Message fork} {state prepared : TransactionState} {substate : Substate}
      {meter : Nat} {e : Event fork} :
      prepareCreation fork state message.currentTarget = .ok prepared →
      Occurs message prepared substate meter e → OccursCreate message state substate meter e
  /-- The init code ended with no error: its output is the code to deposit. -/
  | deposit {message : Message fork} {state prepared : TransactionState} {substate : Substate}
      {meter : Nat} {held : GasMeter.gasHeld meter ≤ message.gas}
      {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }} :
      prepareCreation fork state message.currentTarget = .ok prepared →
      processMessage fork message prepared substate meter held = .ok ended →
      ended.val.error = none →
      OccursCreate message state substate meter (.deposit message.currentTarget ended.val.output)

end

variable {G : Nat} {L : Address} {CODE : ByteArray} {P : State.TransactionState → Prop}
  {Q : Message fork → Prop}

/-- An event is ok: an entered message that runs at `L` satisfies `Q`; a deposited code with the
hash of `CODE` is `CODE`. -/
def EventOk (L : Address) (CODE : ByteArray) (Q : Message fork → Prop) : Event fork → Prop
  | .enter m => m.currentTarget = L → Q m
  | .deposit _ code =>
    Cryptography.Hash.Keccak.keccak256 code = Cryptography.Hash.Keccak.keccak256 CODE →
      code = CODE

/-- Every event of the run of `processMessage fork message state substate meter` is ok. -/
def Clean (L : Address) (CODE : ByteArray) (Q : Message fork → Prop) (message : Message fork)
    (state : TransactionState) (substate : Substate) (meter : Nat) : Prop :=
  ∀ e, Occurs message state substate meter e → EventOk L CODE Q e

/-- Every event of the run that `processRunner` makes of `msg` from `caller` is ok. -/
def CleanRun (L : Address) (CODE : ByteArray) (Q : Message fork → Prop) (caller : Evm fork Nat)
    (msg : Message fork) : Prop :=
  ∀ e, OccursRun caller msg e → EventOk L CODE Q e

/-- Every event of the run of `processCreateMessage fork message state substate meter` is ok. -/
def CleanCreate (L : Address) (CODE : ByteArray) (Q : Message fork → Prop)
    (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Nat) :
    Prop :=
  ∀ e, OccursCreate message state substate meter e → EventOk L CODE Q e

/-- Every event of the runs of the messages that the frame `evm` sends, under `runFrame` with
the runner `processRunner fork bound`, is ok. -/
def CleanFrame (L : Address) (CODE : ByteArray) (Q : Message fork → Prop) (bound : Nat)
    (evm : Evm fork Nat) : Prop :=
  ∀ caller msg, Sent (Logic.processRunner fork (Meter := Nat) bound) evm caller msg →
    CleanRun L CODE Q caller msg

/-! ## The global hypotheses imply the run-local ones -/

/-- Under the global hypotheses every event is ok. -/
theorem eventOk_of_global (hQ : ∀ m : Message fork, m.currentTarget = L → Q m)
    (hcol : NoCollision CODE) (e : Event fork) : EventOk L CODE Q e := by
  cases e with
  | enter m => exact hQ m
  | deposit a code => exact hcol code

theorem clean_of_global (hQ : ∀ m : Message fork, m.currentTarget = L → Q m)
    (hcol : NoCollision CODE) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Nat) : Clean L CODE Q message state substate meter :=
  fun e _ => eventOk_of_global hQ hcol e

theorem cleanRun_of_global (hQ : ∀ m : Message fork, m.currentTarget = L → Q m)
    (hcol : NoCollision CODE) (caller : Evm fork Nat) (msg : Message fork) :
    CleanRun L CODE Q caller msg :=
  fun e _ => eventOk_of_global hQ hcol e

theorem cleanCreate_of_global (hQ : ∀ m : Message fork, m.currentTarget = L → Q m)
    (hcol : NoCollision CODE) (message : Message fork) (state : TransactionState)
    (substate : Substate) (meter : Nat) : CleanCreate L CODE Q message state substate meter :=
  fun e _ => eventOk_of_global hQ hcol e

theorem cleanFrame_of_global (hQ : ∀ m : Message fork, m.currentTarget = L → Q m)
    (hcol : NoCollision CODE) (bound : Nat) (evm : Evm fork Nat) :
    CleanFrame L CODE Q bound evm :=
  fun caller msg _ => cleanRun_of_global hQ hcol caller msg

/-- An event that is ok for `Q` is ok for every weaker `Q'`. -/
theorem EventOk.mono {Q' : Message fork → Prop} (hq : ∀ m : Message fork, Q m → Q' m)
    {e : Event fork} (h : EventOk L CODE Q e) : EventOk L CODE Q' e := by
  cases e with
  | enter m => exact fun ht => hq m (h ht)
  | deposit a code => exact h

/-- A run that is clean for `Q` is clean for every weaker `Q'`. -/
theorem Clean.mono {Q' : Message fork → Prop} (hq : ∀ m : Message fork, Q m → Q' m)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    (c : Clean L CODE Q message state substate meter) :
    Clean L CODE Q' message state substate meter :=
  fun e he => (c e he).mono hq

/-- A run whose frame sends no message is clean as soon as its own message is ok. -/
theorem clean_of_no_sent {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Nat}
    (hno : ∀ evm0, FrameOf message state substate meter evm0 → ∀ c m,
      ¬ Sent (Logic.processRunner fork (Meter := Nat) message.gas) evm0 c m)
    (hq : message.currentTarget = L → Q message) :
    Clean L CODE Q message state substate meter := by
  intro e he
  cases he with
  | self => exact hq
  | sub fo hs _ => exact absurd hs (hno _ fo _ _)

/-- A frame that sends no message is clean. -/
theorem cleanFrame_of_no_sent {bound : Nat} {evm : Evm fork Nat}
    (hno : ∀ c m, ¬ Sent (Logic.processRunner fork (Meter := Nat) bound) evm c m) :
    CleanFrame L CODE Q bound evm :=
  fun caller msg hs => absurd hs (hno caller msg)

/-- The events of a run are events of every run that contains it: a clean run has clean
sub-runs. -/
theorem Clean.sub {message : Message fork} {state : TransactionState} {substate : Substate}
    {meter : Nat} (clean : Clean L CODE Q message state substate meter) {evm0 : Evm fork Nat}
    (fo : FrameOf message state substate meter evm0) :
    CleanFrame L CODE Q message.gas evm0 :=
  fun caller msg hs e he => clean e (Occurs.sub fo hs he)

/-! ## The interface of a token, with a hypothesis on the message of the frame -/

/-- `Reenter.FrameKeeps` with the hypothesis `Q message` on the message of the frame: a frame of
`CODE` at `L` whose message satisfies `Q`, that ends with no error, keeps `P`, when each sane
message that its runner ends keeps a good state good. -/
def FrameKeepsQ (fork : Fork) (G : Nat) (L : Address) (CODE : ByteArray)
    (P : State.TransactionState → Prop) (Q : Message fork → Prop) : Prop :=
  ∀ {bound : Nat} {runChild : MessageRunner fork Nat bound} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {evm s : Evm fork Nat}
    (within : GasMeter.gasHeld evm.gas ≤ bound), bound ≤ G →
    message.currentTarget = L → message.code = CODE → message.data.size < 2 ^ 256 →
    Q message → Good L CODE P state →
    Logic.KeepsOn runChild (fun _ msg => Sane L CODE msg) (GoodKept L CODE P) →
    UsdtVerify.At CODE message 0 [] .empty gas state substate evm →
    Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s →
    s.error = none → P s.state

/-- With `Q` for every message, `FrameKeepsQ` is `Reenter.FrameKeeps`. -/
theorem FrameKeepsQ.toFrameKeeps (fk : FrameKeepsQ fork G L CODE P Q)
    (hQ : ∀ m : Message fork, m.currentTarget = L → Q m) : FrameKeeps fork G L CODE P := by
  unfold FrameKeeps
  intro bound runChild message state substate gas evm s within hb hL hcode hsize good keeps
    start hrun hok
  exact fk within hb hL hcode hsize (hQ message hL) good keeps start hrun hok

/-! ## A run of a frame, with knowledge of the messages it sends only -/

/-- What the induction knows of the runner: on the messages that the frame `evm0` sends, it keeps
the code of `L` and a good state. -/
abbrev SentGood (L : Address) (CODE : ByteArray) (P : State.TransactionState → Prop)
    {bound : Nat} (runChild : MessageRunner fork Nat bound) (evm0 : Evm fork Nat) : Prop :=
  ∀ caller message lt ended, Sent runChild evm0 caller message →
    runChild caller message lt = .ok ended →
    (Sane0 L message → HoldsCode L CODE caller.state → HoldsCode L CODE ended.val.state) ∧
    (Sane L CODE message → Good L CODE P caller.state → Good L CODE P ended.val.state)

/-- `Reenter.w_runFrame`, with the assumption on the runner for the sent messages only. -/
theorem w_runFrame_local (so : StorageOnly L P) (hdel : delegatedAddress CODE = none)
    {bound : Nat} {runChild : MessageRunner fork Nat bound}
    {evm after : Evm fork Nat} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (runs : SentGood L CODE P runChild evm)
    (h : runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok after) :
    W L CODE P evm after := by
  fun_induction runFrame (step fork) (step_decreases fork) bound runChild evm within
  case case1 => cases h
  case case2 => cases h; first | exact W.refl _ | exact (qs_exceptionalHalt _ _).w so
  case case3 =>
    rename_i result _ ih
    have hrunning := ‹Evm.running _ = true›
    have r : W L CODE P _ _ := res_step so hdel result
    exact r.trans (ih (fun c m lt e hs => runs c m lt e (Sent.next hrunning result hs)) h)
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; first | exact W.refl _ | exact (qs_exceptionalHalt _ _).w so
  case case7 =>
    rename_i hchild _ _ _ hran _ resumed _ ih
    have hrunning := ‹Evm.running _ = true›
    obtain ⟨c, s, hres⟩ := res_step (L := L) (CODE := CODE) (P := P) so hdel hchild
    obtain ⟨hm, hst⟩ := hres _ _ resumed
    obtain ⟨r1, r2⟩ := runs _ _ _ _ (Sent.here hrunning hchild) hran
    refine W.trans ⟨hm.trans c.message, fun hold => ?_, fun t g => ?_⟩
      (ih (fun c m lt e hs => runs c m lt e (Sent.resumed hrunning hchild hran resumed hs)) h)
    · rw [hst]
      exact r1 (s hold).1 (c.holds hold)
    · rw [hst]
      exact r2 ((s g.1).2 t) (c.good t g)
  case case8 => cases h; first | exact W.refl _ | exact (qs_exceptionalHalt _ _).w so

/-- `Reenter.frame_core`, with the assumption on the runner for the sent messages only, and `Q`
for the message of the frame when it runs at `L`. -/
theorem frame_core_local (so : StorageOnly L P) (fk : FrameKeepsQ fork G L CODE P Q)
    (hdel : delegatedAddress CODE = none) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} (hG : bound ≤ G)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {within : GasMeter.gasHeld (startFrame message state substate meter).gas ≤ bound}
    {after : Evm fork Nat}
    (runs : SentGood L CODE P runChild (startFrame message state substate meter))
    (hq : message.currentTarget = L → Q message)
    (hrun : runFrame (step fork) (step_decreases fork) bound runChild
      (startFrame message state substate meter) within = .ok after) :
    after.message = message ∧ (HoldsCode L CODE state → HoldsCode L CODE after.state) ∧
      (after.error = none → Sane L CODE message → Good L CODE P state →
        Good L CODE P after.state) := by
  have w := w_runFrame_local so hdel runs hrun
  refine ⟨w.message, w.holds, fun herr sane g => ?_⟩
  by_cases ht : message.currentTarget = L
  · obtain ⟨hcode, -, hsize⟩ := sane ht
    refine And.intro (w.holds g.1) ?_
    have hrun' := runFrame_agree
      (r' := only runChild (startFrame message state substate meter))
      (fun c m lt hs => only_eq hs lt) hrun
    unfold FrameKeepsQ at fk
    refine fk (gas := meter) (substate := substate) within hG ht hcode hsize (hq ht) g ?_ ?_
      hrun' herr
    · intro caller msg lt child ran hS _ g'
      obtain ⟨hs, ran'⟩ := only_ok ran
      exact (runs caller msg lt child hs ran').2 hS g'
    · exact ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact w.good ht g

/-! ## Messages -/

/-- `Reenter.holdsCode_setCode` for one deposit: this code does not collide with `CODE`. -/
theorem holdsCode_setCode_local {tx tx' : TransactionState} {address : Address}
    {code : ByteArray}
    (hc : Cryptography.Hash.Keccak.keccak256 code = Cryptography.Hash.Keccak.keccak256 CODE →
      code = CODE)
    (h : tx.setCode fork address code = .ok tx')
    (hne : L ≠ address) (hold : HoldsCode L CODE tx) : HoldsCode L CODE tx' := by
  obtain ⟨h1, h2, h3⟩ := hold
  have ha : tx'.getAccount L = tx.getAccount L :=
    getAccount_congr ((TransactionState.getAccount_setCode h).2 L hne)
  refine And.intro ?_ (And.intro (by rw [ha]; exact h2) (by rw [ha]; exact h3))
  rw [ha]
  by_cases hk : Cryptography.Hash.Keccak.keccak256 code = Cryptography.Hash.Keccak.keccak256 CODE
  · have hcc := hc hk
    rw [h3, ← hk, ← hcc]
    refine TransactionState.getCode_setCode_self h ?_
    rw [hk, ← h3]
    exact h2
  · rw [TransactionState.getCode_setCode_of_ne h (fun e => hk (e.symm.trans h3))]
    exact h1

/-- `Reenter.holds_depositCode` for one deposit: the output of this init code, when it ended with
no error, does not collide with `CODE`. -/
theorem holds_depositCode_local (so : StorageOnly L P)
    {snapshot : TransactionState} {evm after : Evm fork Nat}
    (h : depositCode fork snapshot evm = .ok after)
    (hp : evm.state.parent = snapshot.parent) (hne : L ≠ evm.message.currentTarget)
    (hc : evm.error = none →
      Cryptography.Hash.Keccak.keccak256 evm.output = Cryptography.Hash.Keccak.keccak256 CODE →
      evm.output = CODE) :
    (HoldsCode L CODE snapshot → HoldsCode L CODE evm.state → HoldsCode L CODE after.state) ∧
      (Good L CODE P snapshot → Good L CODE P evm.state → Good L CODE P after.state) := by
  have restored : (HoldsCode L CODE snapshot → HoldsCode L CODE evm.state →
        HoldsCode L CODE (evm.state.restoreTxState snapshot)) ∧
      (Good L CODE P snapshot → Good L CODE P evm.state →
        Good L CODE P (evm.state.restoreTxState snapshot)) :=
    ⟨fun hs _ => holdsCode_restore hp hs, fun gs _ => good_restore so hp gs⟩
  unfold depositCode at h
  dsimp only at h
  split at h
  · cases h
    exact restored
  rename_i hsome
  have hn : evm.error = none := by
    cases he : evm.error with
    | none => rfl
    | some x =>
      rw [he] at hsome
      exact absurd rfl hsome
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
    · exact ⟨fun _ he => he, fun _ ge => ge⟩
  split at h
  · cases h
    exact restored
  obtain ⟨st, hst, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hset := Base.mapError_ok_iff.mp hst
  have hh : HoldsCode L CODE evm.state → HoldsCode L CODE st :=
    fun he => holdsCode_setCode_local (hc hn) hset hne he
  exact ⟨fun _ he => hh he,
    fun _ ge => And.intro (hh ge.1)
      (so evm.state st
        (fun k => (TransactionState.sameOutside_setCode hset L (by simpa using hne)).2.1 k)
        ge.2)⟩

/-- Every call and every creation, by strong induction on the gas of the message, for a clean
run. The statement of `Reenter.processMessage_ind` with `Clean` / `CleanCreate` of the run in
place of the global hypotheses. -/
theorem processMessage_ind_local (so : StorageOnly L P) (fk : FrameKeepsQ fork G L CODE P Q)
    (hdel : delegatedAddress CODE = none) (n : Nat) (hG : n ≤ G) :
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Nat)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        Clean L CODE Q message state substate meter →
        ended.val.message = message ∧
        (HoldsCode L CODE state → HoldsCode L CODE ended.val.state) ∧
        (Sane L CODE message → Good L CODE P state → Good L CODE P ended.val.state)) ∧
    (∀ (message : Message fork) (state : TransactionState) (substate : Substate) (meter : Nat)
      (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
      ∀ ended, processCreateMessage fork message state substate meter held = .ok ended →
        CleanCreate L CODE Q message state substate meter →
        message.currentTarget ≠ L →
        (HoldsCode L CODE state → HoldsCode L CODE ended.val.state) ∧
        (Good L CODE P state → Good L CODE P ended.val.state)) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    have call : ∀ (message : Message fork) (state : TransactionState) (substate : Substate)
        (meter : Nat) (held : GasMeter.gasHeld meter ≤ message.gas), message.gas = n →
        ∀ ended, processMessage fork message state substate meter held = .ok ended →
          Clean L CODE Q message state substate meter →
          ended.val.message = message ∧
          (HoldsCode L CODE state → HoldsCode L CODE ended.val.state) ∧
          (Sane L CODE message → Good L CODE P state → Good L CODE P ended.val.state) := by
      intro message state substate meter held hn ended h clean
      have hpar := parent_processMessage h
      rw [processMessage] at h
      obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
      have hval := congrArg Subtype.val rolled
      simp only at hval
      have hp0 : ended0.val.state.parent = state.parent := by
        rw [← hval, parent_rollbackOnError] at hpar
        exact hpar
      have core : ended0.val.message = message ∧
          (HoldsCode L CODE state → HoldsCode L CODE ended0.val.state) ∧
          (ended0.val.error = none → Sane L CODE message → Good L CODE P state →
            Good L CODE P ended0.val.state) := by
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
          have k1 : Kept L state state1 := by
            first
            | exact (kept_startState message state).trans
                (kept_moveEther (Base.mapError_ok_iff.mp hm))
            | (cases hm; exact kept_startState message state)
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
              have fc : after.message = message ∧
                  (HoldsCode L CODE state1 → HoldsCode L CODE after.state) ∧
                  (after.error = none → Sane L CODE message → Good L CODE P state1 →
                    Good L CODE P after.state) := by
                refine frame_core_local so fk hdel (by omega) ?_
                  (fun ht => clean _ (Occurs.self message state substate meter) ht) hrun'
                rintro caller' message' lt ⟨c, used⟩ hs hrun''
                have cr : CleanRun L CODE Q caller' message' :=
                  fun e he => clean e (Occurs.sub fo hs he)
                dsimp only [Logic.processRunner] at hrun''
                split at hrun''
                · have hsome : message'.target.isSome = true :=
                    Option.isSome_iff_exists.mpr ⟨_, by assumption⟩
                  have r := (ih message'.gas (by omega) (by omega)).1 message' caller'.state _ _ _
                    rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.call hsome he))
                  exact ⟨fun _ => r.2.1, r.2.2⟩
                · have htgt : message'.target = none := by assumption
                  have r := (ih message'.gas (by omega) (by omega)).2 message' caller'.state _ _ _
                    rfl ⟨c, used⟩ hrun'' (fun e he => cr e (OccursRun.create htgt he))
                  refine ⟨fun s0 => (r (s0 htgt)).1, fun sane => (r ?_).2⟩
                  intro e
                  have hsome := (sane e).2.1
                  rw [htgt] at hsome
                  cases hsome
              exact ⟨fc.1, fun hold => fc.2.1 (k1.holdsCode hold),
                fun herr sane g => fc.2.2 herr sane (k1.good so g)⟩
          · simp only [hpa] at hdo
            split at hdo
            · cases hdo
              exact ⟨rfl, k1.holdsCode, fun _ _ g => k1.good so g⟩
            · split at hdo
              · rename_i after hrp
                cases hdo
                have q := qs_runPrecompile hrp
                exact ⟨q.message, fun hold => q.kept.holdsCode (k1.holdsCode hold),
                  fun _ _ g => q.kept.good so (k1.good so g)⟩
              · cases hdo
                exact ⟨rfl, k1.holdsCode, fun _ _ g => k1.good so g⟩
      rw [← hval]
      unfold rollbackOnError
      split
      · exact ⟨core.1, fun hold => holdsCode_restore hp0 hold,
          fun _ g => good_restore so hp0 g⟩
      · rename_i herr
        have hnone : ended0.val.error = none := by
          cases he : ended0.val.error with
          | none => rfl
          | some x =>
            rw [he] at herr
            exact absurd rfl herr
        exact ⟨core.1, core.2.1, fun sane g => core.2.2 hnone sane g⟩
    refine ⟨call, ?_⟩
    intro message state substate meter held hn ended h clean hne
    rw [processCreateMessage] at h
    obtain ⟨prepared, hp, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨⟨evm, used⟩, hrun, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    split at h
    · cases h
    · cases h
      have r := call message prepared substate meter held hn _ hrun
        (fun e he => clean e (OccursCreate.init hp he))
      have rm : evm.message = message := r.1
      have kp : Kept L state prepared := kept_prepareCreation hp hne.symm
      have hpp : evm.state.parent = state.parent :=
        (parent_processMessage hrun).trans (parent_prepareCreation hp)
      have hd := holds_depositCode_local (P := P) so ‹depositCode _ _ _ = .ok _› hpp
        (by rw [rm]; exact hne.symm)
        (fun herr => clean _ (OccursCreate.deposit hp hrun herr))
      exact ⟨fun hold => hd.1 hold (r.2.1 (kp.holdsCode hold)),
        fun g => hd.2 g (r.2.2 (fun e => absurd e hne) (kp.good so g))⟩

/-! ## The main results, run-local -/

/-- A sane call from a good state, whose run is clean, ends in a good state, with or without an
error. Every fork, every code that the call runs, every message that it sends. -/
theorem processMessage_good_local (so : StorageOnly L P) (fk : FrameKeepsQ fork G L CODE P Q)
    (hdel : delegatedAddress CODE = none)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} (hG : message.gas ≤ G)
    (sane : Sane L CODE message) (g : Good L CODE P state)
    (clean : Clean L CODE Q message state substate meter)
    (h : processMessage fork message state substate meter held = .ok ended) :
    Good L CODE P ended.val.state :=
  ((processMessage_ind_local so fk hdel message.gas hG).1 message state substate meter held rfl
    ended h clean).2.2 sane g

/-- A creation at another address than `L`, from a good state, whose run is clean, ends in a good
state. -/
theorem processCreateMessage_good_local (so : StorageOnly L P)
    (fk : FrameKeepsQ fork G L CODE P Q) (hdel : delegatedAddress CODE = none)
    {message : Message fork} {state : TransactionState} {substate : Substate} {meter : Nat}
    {held : GasMeter.gasHeld meter ≤ message.gas} {ended} (hG : message.gas ≤ G)
    (hne : message.currentTarget ≠ L) (g : Good L CODE P state)
    (clean : CleanCreate L CODE Q message state substate meter)
    (h : processCreateMessage fork message state substate meter held = .ok ended) :
    Good L CODE P ended.val.state :=
  ((processMessage_ind_local so fk hdel message.gas hG).2 message state substate meter held rfl
    ended h clean hne).2 g

/-- The real runner, on one message whose run is clean, keeps a good state good. -/
theorem processRunner_good_local (so : StorageOnly L P) (fk : FrameKeepsQ fork G L CODE P Q)
    (hdel : delegatedAddress CODE = none) (bound : Nat)
    (hG : bound ≤ G) (caller : Evm fork Nat) (message : Message fork) (lt : message.gas < bound)
    (ended)
    (ran : Logic.processRunner fork (Meter := Nat) bound caller message lt = .ok ended)
    (sane : Sane L CODE message) (g : Good L CODE P caller.state)
    (clean : CleanRun L CODE Q caller message) :
    Good L CODE P ended.val.state := by
  dsimp only [Logic.processRunner] at ran
  split at ran
  · have hsome : message.target.isSome = true :=
      Option.isSome_iff_exists.mpr ⟨_, by assumption⟩
    exact processMessage_good_local so fk hdel (by omega) sane g
      (fun e he => clean e (OccursRun.call hsome he)) ran
  · have htgt : message.target = none := by assumption
    refine processCreateMessage_good_local so fk hdel (by omega) ?_ g
      (fun e he => clean e (OccursRun.create htgt he)) ran
    intro e
    have hsome := (sane e).2.1
    rw [htgt] at hsome
    cases hsome

/-- A frame of `CODE` at `L` under the real runner keeps `P`, when its message satisfies `Q` and
the runs of the messages that it sends are clean. -/
theorem runFrame_keeps_local (so : StorageOnly L P) (fk : FrameKeepsQ fork G L CODE P Q)
    (hdel : delegatedAddress CODE = none) {bound : Nat}
    {message : Message fork} {state : TransactionState} {substate : Substate} {gas : Nat}
    {evm s : Evm fork Nat} (within : GasMeter.gasHeld evm.gas ≤ bound) (hG : bound ≤ G)
    (ht : message.currentTarget = L) (hcode : message.code = CODE)
    (hsize : message.data.size < 2 ^ 256) (hq : Q message) (g : Good L CODE P state)
    (clean : CleanFrame L CODE Q bound evm)
    (hat : UsdtVerify.At CODE message 0 [] .empty gas state substate evm)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (herr : s.error = none) : P s.state := by
  have hrun' := runFrame_agree
    (r' := only (Logic.processRunner fork (Meter := Nat) bound) evm)
    (fun c m lt hs => only_eq hs lt) hrun
  unfold FrameKeepsQ at fk
  refine fk within hG ht hcode hsize hq g ?_ hat hrun' herr
  intro caller msg lt child ran hS _ g'
  obtain ⟨hs, ran'⟩ := only_ok ran
  exact processRunner_good_local so fk hdel bound hG caller msg lt child ran' hS g'
    (clean caller msg hs)

end WbtcVerify.Trace

import LinkVerify.Link.Any
import LinkVerify.Link.Trace

/-!
# The supply invariant of LINK for every receiver, on RUN-LOCAL keccak hypotheses

Written by hand (not generated). Fix of audit 4, LINK-1. `Any.lean` proves the invariant through
`transferAndCall` with any receiver under the GLOBAL idealizations `SepAll` and
`Reenter.NoCollision CODE`, which are almost certainly false. Here the same results ask only for
what happens during the run at hand (`Trace.lean`):

- of each message `m` that ENTERS the code of LINK at `L` during the run: `SepMsg m`, that is
  `Sep (callKeys m)`, the local hypothesis of upstream, for that one message (three address
  words);
- of each code that a creation DEPOSITS during the run: if it has the keccak hash of the code of
  LINK, it is the code of LINK.

`CleanRunL L caller msg`, `CleanFrameL L bound evm`: these two conditions for the run that the
real runner makes of one message, and for the messages that one frame sends (`Trace.CleanRun`,
`Trace.CleanFrame` with `Q := SepMsg`).

- `frameKeepsQ`: the code of LINK meets `Trace.FrameKeepsQ` with `Q := SepMsg` and the gas cap
  `GAS_CAP`: only the LOCAL `Sep (callKeys message)` of the frame's own message is used.
- `runnerKeeps_processRunner_local`: EthLib's real runner keeps a good state good on every sane
  message whose run is clean (every receiver, reentry included).
- `calleeKeeps_processRunner_local`: the local assumption `CalleeKeeps` of `transferAndCall`
  holds for the real runner restricted to the messages that the frame really sends, when their
  runs are clean.
- `supply_all_real_local`: THE HEADLINE. A frame of the code under the real runner, any
  selector, that ends with no error keeps `Inv`, under `Sep (callKeys message)` and
  `CleanFrameL` for the messages it sends. For a selector other than `transferAndCall` the frame
  sends nothing: `supply_preserved` (Invariant.lean) needs `Sep (callKeys message)` only.
- `cleanRunL_of_sepAll_noCollision`, `cleanFrameL_of_sepAll_noCollision`: the global hypotheses
  imply the run-local ones, and `supply_all_real_of_global` shows that the theorem of `Any.lean`
  is a corollary (nothing is lost).

Hypotheses that stay: Berlin ≤ fork < Glamsterdam, `Reenter.HoldsCode`, the gas bound at most
`GAS_CAP` (`2^60 - 1`), and the run-local conditions above (hypotheses about keccak on finitely
many concrete values of one run; NOT proved in general). That the run-local conditions hold on
real runs is machine-checked in `TraceWit.lean` (as implications from `Sep` of the top message,
and outright when the token is not the target).
-/

set_option autoImplicit false

namespace LinkVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open LinkVerify.Tac LinkVerify.Paths LinkVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The run that the real runner makes of `msg` from `caller` is clean for LINK at `L`: each
message that enters `L` has `Sep (callKeys ·)`, each deposited code with the hash of the code of
LINK is that code. -/
abbrev CleanRunL (L : Address) (caller : Evm fork Nat) (msg : Message fork) : Prop :=
  Trace.CleanRun L CODE (fun m : Message fork => SepMsg m) caller msg

/-- The runs of the messages that the frame `evm` sends under the real runner are clean. -/
abbrev CleanFrameL (L : Address) (bound : Nat) (evm : Evm fork Nat) : Prop :=
  Trace.CleanFrame L CODE (fun m : Message fork => SepMsg m) bound evm

/-- The code of LINK at any address `L` meets `Trace.FrameKeepsQ` for the invariant with the
LOCAL hypothesis `Sep (callKeys message)` on the message of the frame, with the gas cap
`GAS_CAP`. -/
theorem frameKeepsQ (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (L : Address) :
    Trace.FrameKeepsQ fork GAS_CAP L CODE (Inv L) (fun m : Message fork => SepMsg m) := by
  unfold Trace.FrameKeepsQ
  intro bound runChild message state substate gas evm s within hb hL hcode hsize hq good keeps
    start hrun hok
  subst hL
  have hgas : gas < 2 ^ 60 := by
    have h7 : evm.gas = gas := start.2.2.2.2.2.2.1
    have h8 : evm.gas ≤ bound := within
    unfold GAS_CAP at hb
    omega
  exact supply_all hfork hsize hq
    (fun _ => ⟨hglam, hgas, calleeKeeps_of_keepsOn keeps good.1⟩) good.2 start ⟨within, hrun⟩
    hok

/-- RUN-LOCAL: EthLib's real runner keeps a good state good on every sane message whose run is
clean, for EVERY receiver: whatever code the message runs, calls back into LINK included. -/
theorem runnerKeeps_processRunner_local (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) {bound : Nat} (hb : bound ≤ GAS_CAP) (L : Address)
    (caller : Evm fork Nat) (msg : Message fork) (lt : msg.gas < bound)
    (ended : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas })
    (ran : Logic.processRunner fork (Meter := Nat) bound caller msg lt = .ok ended)
    (sane : Reenter.Sane L CODE msg) (g : Reenter.Good L CODE (Inv L) caller.state)
    (clean : CleanRunL L caller msg) :
    Reenter.Good L CODE (Inv L) ended.val.state :=
  Trace.processRunner_good_local (storageOnly_inv L) (frameKeepsQ hfork hglam L)
    code_not_delegated bound hb caller msg lt ended ran sane g clean

/-- RUN-LOCAL: the local assumption `CalleeKeeps` of `transferAndCall` holds for EthLib's real
runner restricted to the messages that the frame `evm` really sends (`Trace.only`), for EVERY
receiver, calls back into the token included, when the runs of these messages are clean. No
global hypothesis on keccak. (`Trace.runFrame_agree`: the run of the frame under the restricted
runner is its run under the real runner.) -/
theorem calleeKeeps_processRunner_local (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {bound : Nat} (hb : bound ≤ GAS_CAP) {evm : Evm fork Nat}
    (clean : CleanFrameL message.currentTarget bound evm)
    (hold : Reenter.HoldsCode message.currentTarget CODE state) :
    CalleeKeeps (Trace.only (Logic.processRunner fork (Meter := Nat) bound) evm) message state :=
  calleeKeeps_of_keepsOn
    (fun caller msg lt child ran hS _ g' => by
      obtain ⟨hs, ran'⟩ := Trace.only_ok ran
      exact runnerKeeps_processRunner_local hfork hglam hb _ caller msg lt child ran' hS g'
        (clean caller msg hs))
    hold

/-- THE SUPPLY INVARIANT under the real runner, RUN-LOCAL keccak hypotheses, all twelve
selectors, every receiver of `transferAndCall`, no assumption on the runner: a frame of the code
of LINK run by EthLib's interpreter loop with `processRunner`, that ends with no error, keeps
the invariant. `hsep` is the local hypothesis of the frame's own message, `clean` the same for
the messages that enter LINK inside the runs of the messages that this frame sends (and "no
code deposited in these runs collides with the code of LINK"). -/
theorem supply_all_real_local (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} (hb : bound ≤ GAS_CAP) {evm s : Evm fork Nat}
    (clean : CleanFrameL message.currentTarget bound evm)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have hgas : gas < 2 ^ 60 := by
    have h7 : evm.gas = gas := start.2.2.2.2.2.2.1
    have h8 : evm.gas ≤ bound := within
    unfold GAS_CAP at hb
    omega
  have hrun' := Trace.runFrame_agree
    (r' := Trace.only (Logic.processRunner fork (Meter := Nat) bound) evm)
    (fun c m lt hs => Trace.only_eq hs lt) hrun
  exact supply_all hfork hsize' hsep
    (fun _ => ⟨hglam, hgas, calleeKeeps_processRunner_local hfork hglam hb clean hold⟩) hinv
    start ⟨within, hrun'⟩ hok

/-! ## The global hypotheses imply the run-local ones -/

theorem cleanRunL_of_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (L : Address) (caller : Evm fork Nat) (msg : Message fork) : CleanRunL L caller msg :=
  Trace.cleanRun_of_global (fun m _ => K.msg m) hcol caller msg

theorem cleanFrameL_of_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (L : Address) (bound : Nat) (evm : Evm fork Nat) : CleanFrameL L bound evm :=
  Trace.cleanFrame_of_global (fun m _ => K.msg m) hcol bound evm

/-- `supply_all_real_sepAll_noCollision` (Any.lean) is a corollary of the run-local theorem. -/
theorem supply_all_real_of_global (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (hsize' : message.data.size < 2 ^ 256)
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} (hb : bound ≤ GAS_CAP) {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_all_real_local hfork hglam hsize' (K.call message) hold hinv hb
    (cleanFrameL_of_sepAll_noCollision K hcol _ bound evm) start within hrun hok

end LinkVerify

import WbtcVerify.Wbtc.Any
import WbtcVerify.Wbtc.Trace

/-!
# The supply invariant of WBTC for every callee, on RUN-LOCAL keccak hypotheses

Written by hand (not generated). `Any.lean` proves the invariant through `reclaimToken` with any
token under the GLOBAL idealizations `SepAll` and `Reenter.NoCollision CODE`. Here the same
results ask only for what happens during the run at hand (`Trace.lean`):

- of each message `m` that ENTERS the code of WBTC at `L` during the run: `SepMsg m`, that is
  `Sep (callKeys m)`, the local hypothesis of upstream, for that one message;
- of each code that a creation DEPOSITS during the run: if it has the keccak hash of the code of
  WBTC, it is the code of WBTC.

`CleanRunW L caller msg`, `CleanFrameW L bound evm`: these two conditions for the run that the
real runner makes of one message, and for the messages that one frame sends (`Trace.CleanRun`,
`Trace.CleanFrame` with `Q := SepMsg`).

- `frameKeepsQ`: the code of WBTC meets `Trace.FrameKeepsQ` with `Q := SepMsg`, for every gas
  cap: only the LOCAL `Sep (callKeys message)` of the frame's own message is used.
- `runnerKeeps_processRunner_local`: the local assumption of `reclaimToken` on its runner is TRUE
  for EthLib's real runner on every message whose run is clean (every callee, reentry included).
- `supply_all_real_local`: a frame of the code under the real runner, any selector, that ends
  with no error keeps `Inv`, under `Sep (callKeys message)` and `CleanFrameW` for the messages
  it sends. For a selector other than `reclaimToken` the frame sends nothing that matters:
  `supply_preserved` (Invariant.lean) needs `Sep (callKeys message)` only.
- `cleanRunW_of_sepAll_noCollision`, `cleanFrameW_of_sepAll_noCollision`: the global hypotheses
  imply the run-local ones, and `supply_all_real_of_global` shows that the theorem of `Any.lean`
  is a corollary (nothing is lost).

Hypotheses that stay: Berlin ≤ fork <
Glamsterdam, `Reenter.HoldsCode`, and the run-local conditions above (hypotheses about keccak on
finitely many concrete values of one run; NOT proved).
That the run-local conditions are satisfiable on real runs is machine-checked in `TraceWit.lean`.
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The run that the real runner makes of `msg` from `caller` is clean for WBTC at `L`: each
message that enters `L` has `Sep (callKeys ·)`, each deposited code with the hash of the code of
WBTC is that code. -/
abbrev CleanRunW (L : Address) (caller : Evm fork Nat) (msg : Message fork) : Prop :=
  Trace.CleanRun L CODE (fun m : Message fork => SepMsg m) caller msg

/-- The runs of the messages that the frame `evm` sends under the real runner are clean. -/
abbrev CleanFrameW (L : Address) (bound : Nat) (evm : Evm fork Nat) : Prop :=
  Trace.CleanFrame L CODE (fun m : Message fork => SepMsg m) bound evm

/-- The code of WBTC at any address `L` meets `Trace.FrameKeepsQ` for the invariant with the
LOCAL hypothesis `Sep (callKeys message)` on the message of the frame, for every gas cap `G`. -/
theorem frameKeepsQ (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) (G : Nat) (L : Address) :
    Trace.FrameKeepsQ fork G L CODE (Inv L) (fun m : Message fork => SepMsg m) := by
  unfold Trace.FrameKeepsQ
  intro bound runChild message state substate gas evm s within hb hL hcode hsize hq good keeps
    start hrun hok
  subst hL
  exact supply_all_runnerKeeps hfork hsize hq (fun _ => ⟨hglam, good.1, keeps⟩) good.2 start
    ⟨within, hrun⟩ hok

/-- RUN-LOCAL: EthLib's real runner keeps a good state good on every sane message whose run is
clean, for EVERY callee: whatever code the message runs, calls back into WBTC included. Every
bound, no gas cap. -/
theorem runnerKeeps_processRunner_local (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) (bound : Nat) (L : Address) (caller : Evm fork Nat)
    (msg : Message fork) (lt : msg.gas < bound)
    (ended : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas })
    (ran : Logic.processRunner fork (Meter := Nat) bound caller msg lt = .ok ended)
    (sane : Reenter.Sane L CODE msg) (g : Reenter.Good L CODE (Inv L) caller.state)
    (clean : CleanRunW L caller msg) :
    Reenter.Good L CODE (Inv L) ended.val.state :=
  Trace.processRunner_good_local (storageOnly_inv L) (frameKeepsQ hfork hglam bound L)
    code_not_delegated bound (Nat.le_refl _) caller msg lt ended ran sane g clean

/-- THE SUPPLY INVARIANT under the real runner, RUN-LOCAL keccak hypotheses, all 24 selectors,
every callee of `reclaimToken`, no assumption on the runner: a frame of the code of WBTC run by
EthLib's interpreter loop with `processRunner`, that ends with no error, keeps the invariant.
`hsep` is the local hypothesis of the frame's own message, `clean` the same for the messages
that enter WBTC inside the runs of the messages that this frame sends. -/
theorem supply_all_real_local (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (clean : CleanFrameW message.currentTarget bound evm)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have hrun' := Trace.runFrame_agree
    (r' := Trace.only (Logic.processRunner fork (Meter := Nat) bound) evm)
    (fun c m lt hs => Trace.only_eq hs lt) hrun
  refine supply_all_runnerKeeps hfork hsize' hsep (fun _ => ⟨hglam, hold, ?_⟩) hinv start
    ⟨within, hrun'⟩ hok
  intro caller msg lt child ran hS _ g'
  obtain ⟨hs, ran'⟩ := Trace.only_ok ran
  exact runnerKeeps_processRunner_local hfork hglam bound _ caller msg lt child ran' hS g'
    (clean caller msg hs)

/-! ## The global hypotheses imply the run-local ones -/

theorem cleanRunW_of_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (L : Address) (caller : Evm fork Nat) (msg : Message fork) : CleanRunW L caller msg :=
  Trace.cleanRun_of_global (fun m _ => K.msg m) hcol caller msg

theorem cleanFrameW_of_sepAll_noCollision (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (L : Address) (bound : Nat) (evm : Evm fork Nat) : CleanFrameW L bound evm :=
  Trace.cleanFrame_of_global (fun m _ => K.msg m) hcol bound evm

/-- `supply_all_real_sepAll_noCollision` (Any.lean) is a corollary of the run-local theorem. -/
theorem supply_all_real_of_global (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) (K : SepAll) (hcol : Reenter.NoCollision CODE)
    (hsize' : message.data.size < 2 ^ 256)
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_all_real_local hfork hglam hsize' (K.call message) hold hinv
    (cleanFrameW_of_sepAll_noCollision K hcol _ bound evm) start within hrun hok

end WbtcVerify

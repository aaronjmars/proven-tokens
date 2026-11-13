import WbtcVerify.Wbtc.Invariant
import WbtcVerify.Wbtc.Hold
import WbtcVerify.Wbtc.Reclaim.Good

/-!
# The supply invariant of WBTC for all 24 selectors, reclaimToken with any token included

Written by hand (not generated).

`reclaimToken(token)` (selector 0x17ffc320) CALLs an arbitrary contract twice
(`token.balanceOf(this)`, then `token.transfer(owner, balance)`). That contract runs any code:
it can call WBTC back (real reentrancy), and `token` can be WBTC itself. `reclaimToken` writes
no storage of its own, so the question is whether the runs of the two messages keep the
invariant `Inv` (the sum of the balances is the word `totalSupply_` of slot 1).

- `reclaim_good` (Reclaim/Good.lean) is used for `reclaimToken`: a successful `reclaimToken`
  frame keeps a good state good when every sane message it sends does.
- `supply_all_calleeKeeps`: THE HEADLINE for one frame (audit 4, WBTC-1). Every successful
  frame of the code, any of the 24 selectors and both fallbacks, keeps `Inv`. Hypothesis on
  keccak: the local `Sep (callKeys message)` only. For `reclaimToken` only the LOCAL assumption
  `ReclaimCalleeKeeps` on the two messages that its CALLs send is asked (Reclaim/Good.lean):
  nothing about any other message, nothing about the code at the address of WBTC.
- `supply_all_runnerKeeps` (named `supply_all` before the fix round of audit 4): the same with
  `RunnerKeeps` in place of `ReclaimCalleeKeeps`. `RunnerKeeps` is a statement about EVERY sane
  message that the runner could be given, so it is a strong assumption on the runner, not a
  local one; it is the form that the reentrancy induction (`Reenter.FrameKeeps`,
  `Trace.FrameKeepsQ`) asks of a token, and it is used only there. It is a corollary of
  `supply_all_calleeKeeps`.
- `frameKeeps_sepAll`: the code of WBTC meets `Reenter.FrameKeeps` for `Inv`, for EVERY gas cap
  `G` (WBTC has no unbounded argument: no gas cap is needed), under the GLOBAL `SepAll`.
- `runnerKeeps_processRunner_sepAll_noCollision`: the assumption on the runner is TRUE for
  EthLib's real runner `processRunner`, for every callee, under the GLOBAL hypotheses.
- `supply_all_real_sepAll_noCollision`: a frame of the code under the real runner keeps `Inv`.

The names say which keccak hypothesis is used. The theorems with `sepAll` / `noCollision` in the
name assume the GLOBAL idealizations `SepAll` and `Reenter.NoCollision CODE` (LINK's form); they
are kept as corollaries. `AnyLocal.lean` has the run-local forms that do not assume them.

Hypotheses that stay: Berlin ≤ fork,
fork < Glamsterdam (for `reclaimToken` only: the CALL rule), `Reenter.HoldsCode L CODE state`
(for `reclaimToken`), the keccak hypotheses named above.
Not covered: the end of a transaction; a frame that ends with an error (its message is rolled
back by `processMessage`, see `Seq.lean`).
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
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The local assumption of `reclaimToken` on its runner: each sane message that the runner ends
with no error keeps a good state good (`L` holds the code of WBTC and `Inv L` holds). It says
"keeps the invariant", not "keeps the storage". -/
def RunnerKeeps (runChild : MessageRunner fork Nat bound) (L : Address) : Prop :=
  Logic.KeepsOn runChild (fun _ msg => Reenter.Sane L CODE msg)
    (Reenter.GoodKept L CODE (Inv L))

/-- A successful call of `reclaimToken` keeps the invariant, under the local assumption on the
runner. No hypothesis on keccak. -/
theorem supply_reclaimToken_runner (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x17ffc320)
    (keeps : RunnerKeeps runChild message.currentTarget)
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  (reclaim_good hfork hglam (storageOnly_inv _) code_not_delegated hsize' hsel keeps ⟨hold, hinv⟩ start
    hrun hok).2

/-- THE SUPPLY INVARIANT, all 24 selectors and the fallbacks, under the LOCAL callee assumption
only. Every frame of the code that ends with no error keeps the invariant: if the sum of all
balances was `totalSupply_` before, it is after. `hsep` is the LOCAL hypothesis on keccak (not
proved). For `reclaimToken`: before Glamsterdam, and the local assumption `ReclaimCalleeKeeps`
on the two messages that its CALLs send. No `HoldsCode`, nothing about the runner on other
messages. -/
theorem supply_all_calleeKeeps (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hrec : selector message.data = 0x17ffc320 →
      fork < .glamsterdam ∧ ReclaimCalleeKeeps runChild message state)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  by_cases hsel : selector message.data = 0x17ffc320
  · obtain ⟨hglam, keeps⟩ := hrec hsel
    exact supply_reclaimToken hfork hglam hsize' hsel keeps hinv start hrun hok
  · exact supply_preserved hfork hsize' hsel hsep hinv start hrun hok

/-- The supply invariant, all 24 selectors and the fallbacks, in the form that the reentrancy
induction uses: for `reclaimToken` it asks `RunnerKeeps`, an assumption on EVERY sane message
that the runner could be given (not a local one), and that the account holds the code. A
corollary of `supply_all_calleeKeeps`. (Named `supply_all` before the fix round of audit 4.) -/
theorem supply_all_runnerKeeps (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hrec : selector message.data = 0x17ffc320 →
      fork < .glamsterdam ∧ Reenter.HoldsCode message.currentTarget CODE state ∧
        RunnerKeeps runChild message.currentTarget)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  refine supply_all_calleeKeeps hfork hsize' hsep (fun hsel => ?_) hinv start hrun hok
  obtain ⟨hglam, hold, keeps⟩ := hrec hsel
  exact ⟨hglam, reclaimCalleeKeeps_of_keepsOn (storageOnly_inv _) code_not_delegated keeps hold⟩

/-! ## Every callee, global keccak hypotheses (LINK's form) -/

/-- Under the GLOBAL `SepAll`: the code of WBTC at any address `L` meets `Reenter.FrameKeeps`
for the invariant, for every gas cap `G`. -/
theorem frameKeeps_sepAll (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam) (K : SepAll) (G : Nat) (L : Address) :
    Reenter.FrameKeeps fork G L CODE (Inv L) := by
  unfold Reenter.FrameKeeps
  intro bound runChild message state substate gas evm s within hb hL hcode hsize good keeps
    start hrun hok
  subst hL
  exact supply_all_runnerKeeps hfork hsize (K.call message) (fun _ => ⟨hglam, good.1, keeps⟩) good.2
    start ⟨within, hrun⟩ hok

/-- Under the GLOBAL `SepAll` and `NoCollision`: the local assumption of `reclaimToken` is TRUE
for EthLib's real runner, for EVERY callee: whatever code the token runs, calls back into WBTC
included, a run of a sane message keeps a good state good. Every bound, no gas cap. -/
theorem runnerKeeps_processRunner_sepAll_noCollision (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (K : SepAll)
    (hcol : Reenter.NoCollision CODE) (bound : Nat) (L : Address) :
    RunnerKeeps (Logic.processRunner fork (Meter := Nat) bound) L :=
  Reenter.processRunner_goodKept (storageOnly_inv L) (frameKeeps_sepAll hfork hglam K bound L)
    hcol code_not_delegated bound (Nat.le_refl _)

/-- THE SUPPLY INVARIANT under the real runner, GLOBAL keccak hypotheses, all 24 selectors, every
callee of `reclaimToken`, with no assumption on the runner: a frame of the code of WBTC run by
EthLib's interpreter loop with `processRunner`, that ends with no error, keeps the invariant. -/
theorem supply_all_real_sepAll_noCollision (hfork : .berlin ≤ fork)
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
  supply_all_runnerKeeps hfork hsize' (K.call message)
    (fun _ => ⟨hglam, hold,
      runnerKeeps_processRunner_sepAll_noCollision hfork hglam K hcol bound _⟩)
    hinv start ⟨within, hrun⟩ hok

end WbtcVerify

import WbtcVerify.Wbtc.ReclaimWit.Tiny
import WbtcVerify.Wbtc.ReclaimWit.Sent

/-!
# The run-local conditions hold for `reclaimToken` against the tiny token

Written by hand (not generated). The reentrancy results (`supply_all_real_local` of
AnyLocal.lean, `process_good_local` of SeqLocal.lean) ask for the run-local conditions
`CleanFrameW` and `CleanW` (from `Trace.lean`). Here it is machine-checked that they HOLD for a
full run of `reclaimToken` against the tiny token `TINY` (ReclaimWit/Tiny.lean) under EthLib's
real runner, so these results are not empty on a run that makes outside calls.

What is proved:

- `cleanFrameW_reclaim_tiny`: for a frame of WBTC, selector `reclaimToken`, that the real
  runner ends with no error, whose token holds `TINY` and is not WBTC itself: `CleanFrameW`.
  The frame sends exactly two messages (`reclaim_sent`), both run `TINY`, none enters WBTC, no
  code is deposited. NO hypothesis on keccak.
- `supply_all_real_local_reclaim_tiny`: `supply_all_real_local` on this run. Its only keccak
  hypothesis is the LOCAL `Sep (callKeys message)` of the top-level message.
- `cleanW_reclaim_tiny`: the same for the top-level message run by `processMessage`: `CleanW`.
  The only message that enters WBTC is the top-level one, so the only keccak hypothesis is
  `Sep (callKeys message)` of that one message.
- `process_good_reclaim_tiny`: `process_good_local` on this run.

Does `reclaimToken` need `Sep (callKeys message)` at all? No: `supply_reclaimToken_tiny`
(ReclaimWit/Tiny.lean) proves the same invariant for this run with no hypothesis on keccak.
`Sep (callKeys message)` stays here only because `CleanW` and `supply_all_real_local` ask it of
every message that enters WBTC, for all 24 selectors at once.

Assumed (each listed at its theorem): Berlin ≤ fork < Glamsterdam; call data below 2^256 bytes;
the selector; the token holds `TINY` (`TinyAt`), is no precompile address, and is not the
address of WBTC; the run ends with no error; for the top-level forms also: the message runs the
code of WBTC, has a target and has value 0.
Not covered: runs of `reclaimToken` that end with an error (their sent messages are not
listed); the self call `reclaimToken(WBTC)`; that such a run exists (the stream "witness"
evaluates concrete runs).
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- THE RUN-LOCAL CONDITION OF A FRAME HOLDS, with no hypothesis on keccak: a frame of the code
of WBTC, selector `reclaimToken`, that EthLib's loop with `processRunner` ends with no error,
whose token holds `TINY`, is no precompile address and is not WBTC itself. Each message that
the frame sends has a clean run: it runs `TINY`, does not enter WBTC, sends nothing, deposits
nothing. -/
theorem cleanFrameW_reclaim_tiny (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message))
    (hne : rcToken message ≠ message.currentTarget)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL (Logic.processRunner fork (Meter := Nat) bound) evm s)
    (hok : s.error = none) :
    CleanFrameW message.currentTarget bound evm := by
  obtain ⟨caller1, msg1, child1, caller2, msg2, hvia1, hran1, herr1, hvia2, hall⟩ :=
    reclaim_sent hfork hglam hsize' hsel start hrun hok
  have t0 : TinyAt (rcSt message state (rcToken message)) (rcToken message) :=
    htiny.of_readsAs (readsAs_rcSt _ _ _)
  have e1 := tiny_runner hpre t0 hvia1 hran1 herr1
  have rc1 : ReadsAs caller1.state (rcSt message state (rcToken message)) := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia1
    exact hr
  have t1 : TinyAt child1.state (rcToken message) := by
    rw [e1]
    exact (t0.of_readsAs rc1).startState msg1
  intro c m hs
  rcases hall c m hs with ⟨hc, hm⟩ | ⟨hc, hm⟩
  · subst hc
    subst hm
    exact cleanRunW_tiny hne t0 hvia1
  · subst hc
    subst hm
    exact cleanRunW_tiny hne (t1.of_readsAs (readsAs_rcSt _ _ _)) hvia2

/-- `supply_all_real_local` ON A REAL RUN WITH OUTSIDE CALLS: a successful `reclaimToken`
against the tiny token keeps the invariant, through the reentrancy theorem, with the local
`Sep (callKeys message)` of the top-level message as the only hypothesis on keccak.
(`supply_reclaimToken_tiny` gives the same conclusion with no `hsep`, `hold`, `hne`.) -/
theorem supply_all_real_local_reclaim_tiny (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message))
    (hne : rcToken message ≠ message.currentTarget)
    (hsep : Sep (callKeys message))
    (hold : Reenter.HoldsCode message.currentTarget CODE state)
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (Logic.processRunner fork (Meter := Nat) bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_all_real_local hfork hglam hsize' hsep hold hinv
    (cleanFrameW_reclaim_tiny hfork hglam hsize' hsel hpre htiny hne start ⟨within, hrun⟩ hok)
    start within hrun hok

/-- THE RUN-LOCAL CONDITION OF A TOP-LEVEL MESSAGE HOLDS: a call `reclaimToken(token)` with no
value to the code of WBTC, that `processMessage` ends with no error, whose token holds `TINY`,
is no precompile address and is not WBTC itself. The only message that enters WBTC during the
run is the top-level one, so `Sep (callKeys message)` of that one message is the only
hypothesis on keccak. -/
theorem cleanW_reclaim_tiny {meter : Nat} (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : message.code = CODE)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (hval : message.value = 0)
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message))
    (hne : rcToken message ≠ message.currentTarget)
    (hsep : Sep (callKeys message))
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (h : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    CleanW message.currentTarget message state substate meter := by
  have nv : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) := fun h => h.2 hval
  intro e he
  cases he with
  | self => exact fun _ => hsep
  | sub fo hs ho =>
    obtain ⟨hnp, state1, hst, rfl⟩ := fo
    have hsub : Trace.startSub message substate = substate := by
      unfold Trace.startSub
      rw [ite_eq_right_of_eq_false _ _ (eq_false nv)]
    have hst1 : state1 = startState fork message state := by
      unfold Trace.startSt at hst
      rw [ite_eq_right_of_eq_false _ _ (eq_false nv)] at hst
      exact (Except.ok.inj hst).symm
    subst hst1
    rw [hsub] at hs
    have key : ∀ result, runFrame (step fork) (step_decreases fork) message.gas
        (Logic.processRunner fork (Meter := Nat) message.gas)
        (startFrame message (startState fork message state) substate meter) held = result →
        (processMessage fork message state substate meter held).map Subtype.val =
          result.map (rollbackOnError state) :=
      fun _ ran => processMessage_map_val nv hnp ran
    cases hrun : runFrame (step fork) (step_decreases fork) message.gas
        (Logic.processRunner fork (Meter := Nat) message.gas)
        (startFrame message (startState fork message state) substate meter) held with
    | error e =>
      have hm := key _ hrun
      rw [h] at hm
      cases hm
    | ok after =>
      have hm := key _ hrun
      rw [h] at hm
      have hv : ended.val = rollbackOnError state after := Except.ok.inj hm
      have herr : after.error = none := by
        rw [hv] at hok
        exact error_none_of_rollback hok
      have start : At CODE message 0 [] .empty meter (startState fork message state) substate
          (startFrame message (startState fork message state) substate meter) :=
        ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      exact cleanFrameW_reclaim_tiny hfork hglam hsize' hsel hpre (htiny.startState message) hne
        start ⟨held, hrun⟩ herr _ _ hs e ho

/-- `process_good_local` ON A REAL RUN WITH OUTSIDE CALLS: a call `reclaimToken(token)` against
the tiny token that `processMessage` ends with no error leaves a good state good, under the
local hypothesis `Sep (callKeys message)` of the top-level message only. -/
theorem process_good_reclaim_tiny {meter : Nat} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hcode : message.code = CODE) (htarget : message.target.isSome = true)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (hval : message.value = 0)
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message))
    (hne : rcToken message ≠ message.currentTarget)
    (hsep : Sep (callKeys message))
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (g : GoodWbtc message.currentTarget state)
    (h : processMessage fork message state substate meter held = .ok ended)
    (hok : ended.val.error = none) :
    GoodWbtc message.currentTarget ended.val.state :=
  process_good_local hfork hglam (fun _ => ⟨hcode, htarget, hsize'⟩) g
    (cleanW_reclaim_tiny hfork hglam hcode hsize' hsel hval hpre htiny hne hsep h hok) h

end WbtcVerify

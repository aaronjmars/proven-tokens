import LinkVerify.Link.Whole
import LinkVerify.Link.Complete.Value

/-!
# The supply invariant through transferAndCall, for every receiver

Written by hand (not generated).

`transferAndCall` moves the tokens, emits both logs, and then, when the recipient has code, CALLs
it (`onTokenTransfer`) with all the gas left but 710. The recipient runs any code: it can call
the token back (real reentrancy). The token has already written both balances at that point, so
the question is whether the run of the recipient keeps the invariant `Inv` (the sum of the
balances is `10^27`).

- `CalleeKeeps runChild message state`: the LOCAL assumption on the one message that the CALL
  sends: from a state that reads as the state right after the token move, a run of that message
  by `runChild` that ends with no error keeps `Inv`. It says "keeps the invariant", not "keeps
  the storage".
- `supply_tac_530`, `supply_transferAndCall`: under that assumption, a successful
  `transferAndCall` keeps `Inv`. For every recipient, a delegated account (EIP-7702) too
  (`callIn_outcome_any`).
- `supply_all`: every successful call of the code, any selector, keeps `Inv` (the assumption is
  asked for `transferAndCall` only).
  These three use the LOCAL hypothesis `Sep (callKeys message)` only.
- `frameKeeps_sepAll`: under the GLOBAL `SepAll`, the code of LINK meets `Reenter.FrameKeeps`: a
  successful frame of the code keeps `Inv` when every sane message it sends keeps a good state
  good.
- `calleeKeeps_processRunner_sepAll_noCollision`: under the GLOBAL hypotheses the local
  assumption holds for EthLib's real runner `processRunner`, for every recipient, by the
  induction of `Reenter` over all messages. `supply_all_real_sepAll_noCollision`: a frame under
  the real runner.

The names say which keccak hypothesis is used. The theorems with `sepAll` / `noCollision` in the
name assume the GLOBAL idealizations `SepAll` and `Reenter.NoCollision CODE`. Both are almost
certainly false as mathematics (audit 4, LINK-1), so these theorems are NOT usable facts; they
are kept as corollaries only. `AnyLocal.lean` has the run-local forms that do not assume them
(`supply_all_real_local`, `calleeKeeps_processRunner_local`): those are the headline theorems.

Hypotheses that stay (listed, none hidden):
- `hsep : Sep (callKeys message)`: the LOCAL hypothesis on keccak for the three address words of
  one call (not proved).
- `K : SepAll` (only in the `sepAll` theorems): the GLOBAL hypothesis on keccak for all address
  words (not proved, almost certainly false).
- `hcol : Reenter.NoCollision CODE` (only in the `noCollision` theorems): no other byte string
  of any length has the keccak hash of the code of LINK (not proved, almost certainly false; it
  is used for contract creations, which store code by hash).
- `Reenter.HoldsCode L CODE state`: the account of the token holds the code of LINK.
- Berlin ≤ fork < Glamsterdam (the CALL rule; the one-counter gas meter).
- the gas of the frame is below `2 ^ 60` (`GAS_CAP`): the gas of the model is an unbounded
  number, and a `bytes` argument of `2 ^ 64` bytes or more is only shown to fail below that.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LinkVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open LinkVerify.Tac LinkVerify.Paths LinkVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {sel : U256} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The cap on the gas of a frame: `2 ^ 60 - 1`. -/
def GAS_CAP : Nat := 2 ^ 60 - 1

/-- The local assumption of `transferAndCall` on the message that its CALL sends: the message
goes to the recipient (not the token), carries the call data of `onTokenTransfer`, and starts
from a state `caller.state` that reads as the state right after the token move. When its run by
`runChild` ends with no error, it keeps the invariant. -/
def CalleeKeeps (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) : Prop :=
  ∀ (caller : Evm fork Nat) (msg : Message fork) (child : Evm fork Nat),
    Ran runChild caller msg child →
    Logic.ReadsAs caller.state (tacCallSt message state) →
    msg.currentTarget = toAddressMasked (tacToW message) →
    msg.currentTarget ≠ message.currentTarget →
    msg.data = tacCallData message →
    child.error = none →
    Inv message.currentTarget caller.state → Inv message.currentTarget child.state

/-- From 530: a successful `transferAndCall` keeps the invariant, under the local assumption. -/
theorem supply_tac_530 (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hN : tacN message < 2 ^ 64) (hsep : Sep (callKeys message))
    (keeps : CalleeKeeps runChild message state)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  obtain ⟨hstat, hacc, h1, h2, h3, h4, c, hcode, hcase⟩ := ok_tac_pre hfork hN start hrun hok
  rcases hcase with ⟨h5, hg, hrn, hout, hgas, hst, hss⟩ | ⟨h5, hg, z, hz, within, hzr⟩
  · rw [hst]
    exact inv_tacDoneSt hsep hacc h3 h4 hinv
  · obtain ⟨hin, hdata, -⟩ := tac_call_range (message := message) hN
    have hz' : At CODE message 3088
        (tacAsked fork message state substate gas :: tacToW message :: 0 ::
          tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132) ::
          tacFpw (tacLen message) :: 0 :: tacRest message sel)
        (tacMem message) (gas - (tacCallGas fork message state substate + 5))
        (tacCallSt message state) (tacCallSs fork message state substate) z := hz
    rcases callIn_outcome_any hfork hglam (by code_fact) (by code_fact) hin hz' within hzr with
      herr | ⟨mem, g, st, ss, after, hat, w', hr'⟩ |
      ⟨caller, msg, child, after, g, hran, hreads, hct, htgt, hd, hat, w', hr'⟩
    · exact absurd hok herr
    · exact (no_ok_after_fail hfork hat ⟨w', hr'⟩ hok).elim
    · cases herr : child.error with
      | some e =>
        rw [herr] at hat
        exact (no_ok_after_fail hfork hat ⟨w', hr'⟩ hok).elim
      | none =>
        rw [herr] at hat
        obtain ⟨-, -, -, -, -, hst, -⟩ := ok_tac_post hfork hN hat ⟨w', hr'⟩ hok
        rw [hst, state_incorporate_ok herr]
        exact keeps caller msg child hran hreads hct (by rw [hct]; exact tac_to_ne h2)
          (by rw [hd, hdata]) herr
          (storageOnly_inv _ _ _ (fun k => (hreads.1 _ (by simp)).2.1 k)
            (inv_tacCallSt hsep hacc h3 h4 hinv))

/-- A successful call of `transferAndCall` keeps the invariant, under the local assumption on the
message of its CALL. The gas is below `2 ^ 60`. -/
theorem supply_transferAndCall (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x4000aea0)
    {gas : Nat} (hgas : gas < 2 ^ 60)
    (hsep : Sep (callKeys message))
    (keeps : CalleeKeeps runChild message state)
    (hinv : Inv message.currentTarget state)
    {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  obtain ⟨-, hcg, z, hz, hzr⟩ := ok_transferAndCall hfork hsize' hsel start hrun hok
  have hN := ok_tac_len hfork (show gas - 207 < 2 ^ 60 by omega) hz hzr hok
  exact supply_tac_530 hfork hglam hN hsep keeps hinv hz hzr hok

/-- THE SUPPLY INVARIANT, all twelve selectors. Every call of the code that ends with no error
keeps the invariant: if the sum of all balances was `10^27` before, it is after. For
`transferAndCall` under the local assumption on the message of its CALL, before Glamsterdam and
with gas below `2 ^ 60`. `hsep` is the hypothesis on keccak (not proved). -/
theorem supply_all (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    {gas : Nat}
    (htac : selector message.data = 0x4000aea0 →
      fork < .glamsterdam ∧ gas < 2 ^ 60 ∧ CalleeKeeps runChild message state)
    (hinv : Inv message.currentTarget state)
    {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  by_cases hsel : selector message.data = 0x4000aea0
  · obtain ⟨hglam, hgas, keeps⟩ := htac hsel
    exact supply_transferAndCall hfork hglam hsize' hsel hgas hsep keeps hinv start hrun hok
  · exact supply_preserved hfork hsize' hsel hsep hinv start hrun hok

/-! ## Every receiver, GLOBAL keccak hypotheses (corollaries, not usable facts) -/

/-- The local assumption follows from the assumption of `Reenter.FrameKeeps` on the runner. -/
theorem calleeKeeps_of_keepsOn
    (keeps : Logic.KeepsOn runChild
      (fun _ msg => Reenter.Sane message.currentTarget CODE msg)
      (Reenter.GoodKept message.currentTarget CODE (Inv message.currentTarget)))
    (hold : Reenter.HoldsCode message.currentTarget CODE state) :
    CalleeKeeps runChild message state := by
  rintro caller msg child ⟨lt, child', hrun, rfl⟩ r hct hne hd herr hinv
  exact (keeps caller msg lt child' hrun (fun e => absurd e hne) herr
    ⟨Reenter.HoldsCode.of_readsAs r (holdsCode_tacCallSt hold), hinv⟩).2

/-- Under the GLOBAL `SepAll` (almost certainly false, see the head of this file): the code of
LINK at any address `L` meets `Reenter.FrameKeeps` for the invariant, with the gas cap
`GAS_CAP`: a frame of the code that ends with no error keeps `Inv L`, when every sane message it
sends keeps a good state good. The run-local form is `frameKeepsQ` (AnyLocal.lean). -/
theorem frameKeeps_sepAll (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (K : SepAll)
    (L : Address) : Reenter.FrameKeeps fork GAS_CAP L CODE (Inv L) := by
  unfold Reenter.FrameKeeps
  intro bound runChild message state substate gas evm s within hb hL hcode hsize good keeps
    start hrun hok
  subst hL
  have hgas : gas < 2 ^ 60 := by
    have h7 : evm.gas = gas := start.2.2.2.2.2.2.1
    have h8 : evm.gas ≤ bound := within
    unfold GAS_CAP at hb
    omega
  exact supply_all hfork hsize (K.call message)
    (fun _ => ⟨hglam, hgas, calleeKeeps_of_keepsOn keeps good.1⟩) good.2 start ⟨within, hrun⟩
    hok

/-! ## The real runner, GLOBAL keccak hypotheses -/

/-- Under the GLOBAL `SepAll` and `NoCollision` (almost certainly false, so NOT a usable fact):
the local assumption of `transferAndCall` holds for EthLib's real runner, for every recipient.
The run-local form is `calleeKeeps_processRunner_local` (AnyLocal.lean). -/
theorem calleeKeeps_processRunner_sepAll_noCollision (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (K : SepAll) (hcol : Reenter.NoCollision CODE) {bound : Nat} (hb : bound ≤ GAS_CAP)
    (hold : Reenter.HoldsCode message.currentTarget CODE state) :
    CalleeKeeps (Logic.processRunner fork (Meter := Nat) bound) message state :=
  calleeKeeps_of_keepsOn
    (Reenter.processRunner_goodKept (storageOnly_inv _) (frameKeeps_sepAll hfork hglam K _) hcol
      code_not_delegated bound hb) hold

/-- The supply invariant under the real runner, GLOBAL keccak hypotheses (almost certainly
false, so NOT a usable fact), all twelve selectors: a frame of the code of LINK run by EthLib's
interpreter loop with `processRunner`, that ends with no error, keeps the invariant. The
run-local form is `supply_all_real_local` (AnyLocal.lean). -/
theorem supply_all_real_sepAll_noCollision (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    Inv message.currentTarget s.state := by
  have hgas : gas < 2 ^ 60 := by
    have h7 : evm.gas = gas := start.2.2.2.2.2.2.1
    have h8 : evm.gas ≤ bound := within
    unfold GAS_CAP at hb
    omega
  exact supply_all hfork hsize' (K.call message)
    (fun _ => ⟨hglam, hgas,
      calleeKeeps_processRunner_sepAll_noCollision hfork hglam K hcol hb hold⟩)
    hinv start ⟨within, hrun⟩ hok

end LinkVerify

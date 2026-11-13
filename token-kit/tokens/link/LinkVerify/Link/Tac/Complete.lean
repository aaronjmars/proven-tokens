import LinkVerify.Link.Tac.Main

/-!
# transferAndCall: every run that ends with no error

Over the loop of the interpreter itself (`EndsL`, TokenKit/Evm/SafeL.lean), with any message
runner.

- `ok_tac_pre`: a run from the entry of the function that ends with no error passed every test,
  the state gave a code for the recipient, and either that code is empty and the run ended with
  the exact frame of `tac_done`, or it is not and the run went through the frame at the CALL of
  `tac_at_call`.
- `ok_tac_post`: a run from the frame after the CALL that ends with no error had a flag that is
  not zero, and ended with the exact frame of `tac_after_ok`.

Every other case ends with an error: the two REVERTs, the two invalid opcodes, the SSTORE that
fails in a static frame or with no account, an EXTCODESIZE whose state cannot give the code
(`extcodesize_outcome`), a GAS opcode with too little gas (`gas_outcome`), the REVERT after a
CALL that failed, and too little gas at any step.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit
open LinkVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {sel : U256} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- D. A run from the entry of the function that ends with no error. -/
theorem ok_tac_pre (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64) {gas : Nat}
    {evm s : Evm fork Nat}
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    TacToSet message ∧ TacToOther message ∧ TacFunded message state ∧ TacFits message state ∧
    ∃ c : ByteArray, TacCode message state c ∧
      ((TacNoCode c ∧ tacDoneGas fork message state substate ≤ gas ∧ s.running = false ∧
          s.output = wordBytes (1 : U256) ∧
          s.gas = gas - tacDoneGas fork message state substate ∧
          s.state = tacDoneSt message state ∧
          s.substate = tacDoneSs fork message state substate) ∨
       (TacHasCode c ∧ tacCallGas fork message state substate + 5 ≤ gas ∧
          ∃ z : Evm fork Nat,
            At CODE message 3088
              (tacCallStack message sel (tacAsked fork message state substate gas))
              (tacMem message) (gas - (tacCallGas fork message state substate + 5))
              (tacCallSt message state) (tacCallSs fork message state substate) z ∧
            EndsL runChild z s)) := by
  by_cases h0 : TacToZero message
  · exact (Complete.no_okLE (B := tac_zeroCost (tacN message))
      (fun g hg => tac_revert_zero hfork hN h0 hg) (fun _ e h => reverted_error e h)
      start hrun hok).elim
  have h1 : TacToSet message := Classical.byContradiction fun h => h0 h
  by_cases h2 : TacToSelf message
  · exact (Complete.no_okLE (B := tac_selfCost (tacN message))
      (fun g hg => tac_revert_self hfork hN h1 h2 hg) (fun _ e h => reverted_error e h)
      start hrun hok).elim
  by_cases h3 : TacLow message state
  · exact (Complete.no_okLE (B := tac_lowCost message substate (tacN message))
      (Q := fun _ => Faulted (.invalidOpcode 0xfe) (tac_lowSt message state)
        (tac_lowSs message substate))
      (fun g hg => tac_invalid_low hfork hN h1 h2 h3 hg) (fun _ e h => UsdtVerify.Complete.faulted_error e h)
      start hrun hok).elim
  by_cases hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget
  · exact (Complete.no_ok_stuckLE (B := tac_stuckCost message substate (tacN message))
      (fun g hg => tac_stuck_static hfork hN h1 h2 h3 hbad hg) start hrun hok).elim
  have hstatic : message.isStatic = false := by
    cases hs : message.isStatic
    · rfl
    · exact absurd (.inl hs) hbad
  have hacc : hasAccount state message.currentTarget :=
    Classical.not_not.mp fun h => hbad (.inr h)
  by_cases h4 : TacOver message state
  · exact (Complete.no_okLE
      (B := tac_overCost fork message state substate (tacN message) + 2301)
      (Q := fun _ => Faulted (.invalidOpcode 0xfe) (tac_overSt message state)
        (tac_overSs fork message state substate))
      (fun g hg => tac_invalid_over hfork hstatic hacc hN h1 h2 h3 h4 (by omega))
      (fun _ e h => UsdtVerify.Complete.faulted_error e h) start hrun hok).elim
  refine ⟨hstatic, hacc, h1, h2, h3, h4, ?_⟩
  -- the EXTCODESIZE of the recipient: the state gives a code, or the run has an error
  obtain ⟨-, z0, hz0, w0, hrun0⟩ := Complete.ok_splitLE
    (B := tac_extCost fork message state substate (tacF message) (tacN message) (tacW message)
      + 2301)
    (c := tac_extCost fork message state substate (tacF message) (tacN message) (tacW message))
    (by omega)
    (fun g hg => tac_ext hfork hstatic hacc hN h1 h2 h3 h4 (by omega)) start hrun hok
  rcases extcodesize_outcome hfork (by code_fact) (by code_fact) hz0 w0 hrun0 with
    herr | ⟨c, z1, hcode', -⟩
  · exact absurd hok herr
  have hcode : TacCode message state c := by
    simpa only [TacCode, tac_extSt, getCode_writeSlot, getAccount_writeSlot,
      getAccount_readSlot, getCode_readSlot, getAccount_rar, getCode_rar, toAddressMasked_mask']
      using hcode'
  refine ⟨c, hcode, ?_⟩
  by_cases h5 : TacHasCode c
  · -- code: to the GAS opcode, then GAS and SUB
    right
    obtain ⟨hc, z3, hz3, w3, hrun3⟩ := Complete.ok_splitLE
      (B := tacCallGas fork message state substate + 2301)
      (c := tacCallGas fork message state substate) (by omega)
      (fun g hg => tac_to_gas hfork hstatic hacc hN hcode h1 h2 h3 h4 h5 (by omega))
      start hrun hok
    rcases gas_outcome (by code_fact) (by code_fact)
        (by simp [tacCallStack, tacRest, STACK_LIMIT]) hz3 w3 hrun3 with
      herr | ⟨z4, hz4, w4, hrun4⟩
    · exact absurd hok herr
    obtain ⟨hc5, z5, hz5, hend5⟩ := Complete.ok_splitLE (B := 3) (c := 3) (Nat.le_refl 3)
      (fun g hg => tac_sub hg) hz4 ⟨w4, hrun4⟩ hok
    have e : gas - tacCallGas fork message state substate - 2 - 3 =
        gas - (tacCallGas fork message state substate + 5) := by omega
    rw [e] at hz5
    have hg2 : 2 ≤ gas - tacCallGas fork message state substate := by
      apply Classical.byContradiction
      intro hlt
      have e0 : gas - tacCallGas fork message state substate - 2 = 0 := by omega
      rw [e0] at hc5
      omega
    exact ⟨h5, by omega, z5, hz5, hend5⟩
  · left
    obtain ⟨hc, hstop, hout, hgas, hst, hss⟩ := Complete.ok_exactLE
      (B := tacDoneGas fork message state substate + 2301)
      (fun g hg => tac_done hfork hstatic hacc hN hcode h1 h2 h3 h4 h5 (by omega))
      start hrun hok
    exact ⟨h5, hc, hstop, hout, hgas, hst, hss⟩

/-- D. A run from the frame after the CALL that ends with no error: the flag is not zero, and the
run ends with RETURN of true and the state and substate it started with. -/
theorem ok_tac_post (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64) {flag : U256}
    {st : State.TransactionState} {ss : Substate} {g : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 3089 (flag :: tacRest message sel) (tacMem message) g st ss evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    flag ≠ 0 ∧ af_okCost ≤ g ∧ s.running = false ∧ s.output = wordBytes (1 : U256) ∧
      s.gas = g - af_okCost ∧ s.state = st ∧ s.substate = ss := by
  by_cases hflag : flag = 0
  · exact (Complete.no_okLE (B := af_failCost)
      (fun g hg => tac_after_fail hfork hflag hg) (fun _ e h => reverted_error e h)
      start hrun hok).elim
  · exact ⟨hflag, Complete.ok_exactLE (B := af_okCost)
      (fun g hg => tac_after_ok hN hflag hg) start hrun hok⟩

end LinkVerify.Tac

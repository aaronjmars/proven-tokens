import TokenKit.Evm.Safe
import TokenKit.Evm.Opt

/-!
# The logic mode: runs of the interpreter loop, and the read-only rules over `Logic.StepG`

A token whose code runs opcodes outside the simulated set of usdt-verify (see
TokenKit/Evm/Opt.lean) cannot state its completeness over the `Ends` of usdt-verify: `Ends` also
holds of a run that stops at a frame outside the simulated set. Its theorems are over the loop
of the interpreter itself.

- `EndsL runChild l s`: the loop of the interpreter (`runFrame`), with the message runner
  `runChild` and its gas bound, runs the frame `l` to the frame `s`. It takes the place of
  `Ends fork l s` in every statement of a token in the logic mode.
- `Complete.ok_exactLE`, `no_okLE`, `no_ok_stuckLE`, `ok_splitLE`: a specification over
  `Logic.StepG`, held for every gas from a bound on, fixes the end of every run that ends with
  no error (EthLib's `halted_of_specG`, `no_ok_of_specG`, `no_ok_stuck`, `reaches_low`).
- `SafeL.stepE`, `SafeL.jumpiE`, `SafeL.haltE`: the rules of TokenKit/Evm/Safe.lean (a rule as a
  fact about a run that ends with no error), for rules over `Logic.StepG` and runs `EndsL`.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The loop of the interpreter, with the message runner `runChild` and its gas bound, runs the
frame `l` to the frame `s`. -/
def EndsL {bound : Nat} (runChild : MessageRunner fork Nat bound) (l s : Evm fork Nat) : Prop :=
  ∃ within : GasMeter.gasHeld l.gas ≤ bound,
    Evm.runFrame (step fork) (step_decreases fork) bound runChild l within = .ok s

variable {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {gas : Nat} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

namespace Complete

variable {evm s : Evm fork Nat}

/-- `ok_exactL` for a run `EndsL`. -/
theorem ok_exactLE {B cost : Nat} {out : ByteArray}
    {st' : State.TransactionState} {ss' : Substate}
    (h : ∀ g, B ≤ g → Logic.SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - cost) st' ss'))
    (start : At code message pc stack memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    cost ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas = gas - cost ∧ s.state = st' ∧
      s.substate = ss' :=
  let ⟨within, hr⟩ := hrun
  ok_exactL h start within hr hok

/-- `no_okL` for a run `EndsL`. -/
theorem no_okLE {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → Logic.SpecG fork (At code message pc stack memory g state substate) (Q g))
    (herr : ∀ g e, Q g e → e.error ≠ none)
    (start : At code message pc stack memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) : False :=
  let ⟨within, hr⟩ := hrun
  no_okL h herr start within hr hok

/-- `no_ok_stuckL` for a run `EndsL`. -/
theorem no_ok_stuckLE {B : Nat}
    (h : ∀ g, B ≤ g →
      Logic.HoareG fork (At code message pc stack memory g state substate) Logic.Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) : False :=
  let ⟨within, hr⟩ := hrun
  no_ok_stuckL h start within hr hok

/-- A run that ends with no error goes through the frame of a triple over `Logic.StepG` that
holds for every gas from `B ≥ c` on: `c ≤ gas`, and the run goes on from that frame with
`gas - c`. -/
theorem ok_splitLE {pc' : Nat} {stack' : List U256} {memory' : ByteArray}
    {state' : State.TransactionState} {substate' : Substate} {B c : Nat} (hB : c ≤ B)
    (h : ∀ g, B ≤ g → Logic.HoareG fork (At code message pc stack memory g state substate)
      (At code message pc' stack' memory' (g - c) state' substate'))
    (start : At code message pc stack memory gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    c ≤ gas ∧ ∃ z : Evm fork Nat, At code message pc' stack' memory' (gas - c) state' substate' z ∧
      EndsL runChild z s := by
  obtain ⟨within, hr⟩ := hrun
  obtain ⟨z, hreach, hz⟩ := h (gas + B) (by omega) _ (Gas.at_addGas start B)
  obtain ⟨m, w, rfl, hm⟩ := reaches_low hreach B evm rfl within hr hok
  obtain ⟨hat, hle⟩ := Safe.at_of_addGas hz
  refine ⟨by omega, m, ?_, w, hm⟩
  have e : gas + B - c - B = gas - c := by omega
  rw [e] at hat
  exact hat

end Complete

namespace SafeL

/-- `Safe.stepE` for a rule over `Logic.StepG` and a run `EndsL`. -/
theorem stepE {c pcr pc' : Nat} {stack' : List U256} {memory' : ByteArray}
    {state' : State.TransactionState} {substate' : Substate} {l s : Evm fork Nat}
    (h0 : At code message pc stack memory gas state substate l) (e0 : EndsL runChild l s)
    (hok : s.error = none)
    (rule : ∀ G, c ≤ G → Logic.HoareG fork (At code message pc stack memory G state substate)
      (At code message pcr stack' memory' (G - c) state' substate'))
    (hpc : pcr = pc') :
    ∃ (g' : Nat) (l' : Evm fork Nat), At code message pc' stack' memory' g' state' substate' l' ∧
      EndsL runChild l' s ∧ g' ≤ gas ∧ g' + c ≤ gas := by
  subst hpc
  obtain ⟨within, hr⟩ := e0
  obtain ⟨z, hreach, hz⟩ := rule (gas + c) (by omega) _ (Gas.at_addGas h0 c)
  obtain ⟨l', w, rfl, e'⟩ := reaches_low hreach c l rfl within hr hok
  obtain ⟨h', hle⟩ := Safe.at_of_addGas hz
  exact ⟨_, l', h', ⟨w, e'⟩, by omega, by omega⟩

/-- JUMPI on an unknown condition: the run goes on at the destination or at the next opcode. -/
theorem jumpiE {dest cond : U256} {rest : List U256} {pcT pcF : Nat} {l s : Evm fork Nat}
    (h0 : At code message pc (dest :: cond :: rest) memory gas state substate l)
    (e0 : EndsL runChild l s) (hok : s.error = none)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57)
    (valid : isValidJumpDest (validJumpDestinations code) dest.toNat = true)
    (hT : dest.toNat = pcT) (hF : pc + 1 = pcF) :
    (∃ (g' : Nat) (l' : Evm fork Nat), At code message pcT rest memory g' state substate l' ∧
      EndsL runChild l' s ∧ g' ≤ gas) ∨
    (∃ (g' : Nat) (l' : Evm fork Nat), At code message pcF rest memory g' state substate l' ∧
      EndsL runChild l' s ∧ g' ≤ gas) := by
  by_cases hc : cond = 0
  · obtain ⟨g', l', h', e', hg, -⟩ := stepE h0 e0 hok
      (fun G hG => hoareL (Gas.jumpi_of_eq_zeroG hlt hbyte hG hc)) hF
    exact .inr ⟨g', l', h', e', hg⟩
  · obtain ⟨g', l', h', e', hg, -⟩ := stepE h0 e0 hok
      (fun G hG => hoareL (Gas.jumpi_takenG hlt hbyte hG hc valid)) hT
    exact .inl ⟨g', l', h', e', hg⟩

/-- A rule to a halt (RETURN or REVERT) that needs `c` gas, as a fact about a run that ends with
no error: the run ends with the state and the substate of the rule. -/
theorem haltE {c : Nat} {rev : Bool} {out : ByteArray} {state' : State.TransactionState}
    {substate' : Substate} {l s : Evm fork Nat}
    (h0 : At code message pc stack memory gas state substate l) (e0 : EndsL runChild l s)
    (hok : s.error = none)
    (rule : ∀ G, c ≤ G → Logic.SpecG fork (At code message pc stack memory G state substate)
      (Halted rev out (G - c) state' substate')) :
    s.state = state' ∧ s.substate = substate' := by
  obtain ⟨within, hr⟩ := e0
  obtain ⟨-, -, -, -, hst, hss⟩ :=
    Logic.SpecG.low (rule (gas + c) (by omega)) (Gas.at_addGas h0 c) within hr hok
  exact ⟨hst, hss⟩

end SafeL

end TokenKit

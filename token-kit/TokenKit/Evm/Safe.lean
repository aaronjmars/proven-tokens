import TokenKit.Evm.Rules
import TokenKit.Evm.Stack
import TokenKit.Evm.Supply

/-!
# A run that only reads: no storage write and no log, whatever the loop does

The path theorems state the exact end of a run. That needs every word of the stack and of the
memory, which a loop over a string of unknown length does not give. The lemmas here prove less
with less: a run that ends with no error and never reaches an SSTORE or a LOG leaves every
storage word and the list of logs as they were. The stack and the memory stay unknown; only the
return addresses on the stack are kept.

- `Ro C S ss S' ss'`: every storage word of every account in `S'` is the one in `S`, the account
  of `C` is there in `S'` iff it is in `S`, the logs of `ss'` are those of `ss`, and every
  account (balance, nonce, code hash) of `S'` is the one of `S`.
- `mid_of_reachesE`: a chain of `StepG` from a frame with `k` more gas, cut anywhere, is a
  chain from the frame itself (upstream's `low_of_reachesE`, for a chain that has not stopped).
- `stepE`, `jumpiE`, `haltE`: the opcode rules (triples that need enough gas) as facts about a
  run that ends with no error (`Ends`): the run goes through the frame the rule states, with any
  gas. No rule needs a bound on a memory offset, so they apply to unknown words.
- `inv_of_ro`: `Ro` keeps the supply invariant.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The state `S'` and substate `ss'` differ from `S` and `ss` by reads only. -/
structure Ro (C : Address) (S : State.TransactionState) (ss : Substate)
    (S' : State.TransactionState) (ss' : Substate) : Prop where
  /-- Every storage word of every account is unchanged. -/
  storage : ∀ (c : Address) (k : U256), storageAt S' c k = storageAt S c k
  /-- The account of `C` is there iff it was. -/
  account : hasAccount S' C ↔ hasAccount S C
  /-- No log is added. -/
  logs : ss'.logs = ss.logs
  /-- Every account (balance, nonce, code hash) is unchanged. -/
  accounts : ∀ a : Address, S'.getAccount a = S.getAccount a

namespace Ro

variable {C : Address} {S S1 S2 : State.TransactionState} {ss ss1 ss2 : Substate}

theorem refl (C : Address) (S : State.TransactionState) (ss : Substate) : Ro C S ss S ss :=
  ⟨fun _ _ => rfl, Iff.rfl, rfl, fun _ => rfl⟩

theorem trans (h1 : Ro C S ss S1 ss1) (h2 : Ro C S1 ss1 S2 ss2) : Ro C S ss S2 ss2 :=
  ⟨fun c k => (h2.storage c k).trans (h1.storage c k), h2.account.trans h1.account,
    h2.logs.trans h1.logs, fun a => (h2.accounts a).trans (h1.accounts a)⟩

/-- A read of a slot (SLOAD) after reads. -/
theorem read (h : Ro C S ss S1 ss1) (c : Address) (n : U256) :
    Ro C S ss (readSlot S1 c n) (accessSlot ss1 c n) :=
  ⟨fun c' k => (storageAt_readSlot S1 c c' n k).trans (h.storage c' k),
    hasAccount_readSlot_iff.trans h.account, h.logs, h.accounts⟩

end Ro

/-- Closes a goal `Ro C S ss S' ss'` where `S'` and `ss'` are `S` and `ss` under reads. -/
macro "ro_reads" : tactic =>
  `(tactic| repeat (first | exact Ro.refl _ _ _ | apply Ro.read))

/-- `Ro` keeps the supply invariant. -/
theorem Supply.inv_of_ro {b t : U256} {C : Address} {S S' : State.TransactionState}
    {ss ss' : Substate} (h : Ro C S ss S' ss') (hinv : Supply.Inv b t C S) :
    Supply.Inv b t C S' := by
  unfold Supply.Inv Supply.D Supply.sumBal at hinv ⊢
  rw [h.storage C t, Supply.sumTo_congr (g := Supply.bal b C S) _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h.storage])]
  exact hinv

namespace Safe

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {gas : Nat} {state : State.TransactionState}
  {substate : Substate}

/-- Along a chain of `StepG` from `addGas k l` to any frame `z`: if the loop from `l` ends in `s`
with no error (`Ends`), then `z` is `addGas k l'` for a frame `l'` from which the loop ends in
`s`. -/
theorem mid_of_reachesE {hi z : Evm fork Nat} (hr : Reaches (Gas.StepG fork) hi z) :
    ∀ (k : Nat) (l : Evm fork Nat), hi = addGas k l → ∀ {s : Evm fork Nat}, Gas.Ends fork l s →
      s.error = none → ∃ l' : Evm fork Nat, z = addGas k l' ∧ Gas.Ends fork l' s := by
  induction hr with
  | refl =>
    rintro k l rfl s hs _
    exact ⟨l, rfl, hs⟩
  | step hs _ ih =>
    rintro k l rfl s hend hok
    obtain ⟨hstep, hsim, hmono⟩ := hs
    have hr : l.running = true := hstep.running
    rcases hmono k l rfl with (⟨e, he⟩ | ⟨b, hb, hbr, hbe⟩) | ⟨b, hb, hh⟩
    · rw [(hend.error hr hsim he).2] at hok
      simp [exceptionalHalt] at hok
    · rw [(hend.next hr hsim hb).stopped hbr] at hok
      exact absurd hok hbe
    · cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih k b rfl (hend.next hr hsim hb) hok
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A frame with `k` more gas that is `At` the gas `G`: the frame is `At` the gas `G - k`. -/
theorem at_of_addGas {G k : Nat} {l : Evm fork Nat}
    (h : At code message pc stack memory G state substate (addGas k l)) :
    At code message pc stack memory (G - k) state substate l ∧ k ≤ G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have h7' : l.gas + k = G := h7
  exact ⟨⟨h1, h2, h3, h4, h5, h6, by omega, h8, h9, h10, h11, h12⟩, by omega⟩

/-- A rule that needs `c` gas, as a fact about a run that ends with no error: the run goes
through the frame the rule states, with gas `g'` where `g' + c` is at most the gas before. -/
theorem stepE {c pcr pc' : Nat} {stack' : List U256} {memory' : ByteArray}
    {state' : State.TransactionState} {substate' : Substate} {l s : Evm fork Nat}
    (h0 : At code message pc stack memory gas state substate l) (e0 : Gas.Ends fork l s)
    (hok : s.error = none)
    (rule : ∀ G, c ≤ G → Gas.HoareG fork (At code message pc stack memory G state substate)
      (At code message pcr stack' memory' (G - c) state' substate'))
    (hpc : pcr = pc') :
    ∃ (g' : Nat) (l' : Evm fork Nat), At code message pc' stack' memory' g' state' substate' l' ∧
      Gas.Ends fork l' s ∧ g' ≤ gas ∧ g' + c ≤ gas := by
  subst hpc
  obtain ⟨z, hr, hz⟩ := rule (gas + c) (by omega) _ (Gas.at_addGas h0 c)
  obtain ⟨l', rfl, e'⟩ := mid_of_reachesE hr c l rfl e0 hok
  obtain ⟨h', hle⟩ := at_of_addGas hz
  exact ⟨_, l', h', e', by omega, by omega⟩

/-- JUMPI on an unknown condition: the run goes on at the destination or at the next opcode. -/
theorem jumpiE {dest cond : U256} {rest : List U256} {pcT pcF : Nat} {l s : Evm fork Nat}
    (h0 : At code message pc (dest :: cond :: rest) memory gas state substate l)
    (e0 : Gas.Ends fork l s) (hok : s.error = none)
    (hlt : pc < code.size) (hbyte : code[pc] = 0x57)
    (valid : isValidJumpDest (validJumpDestinations code) dest.toNat = true)
    (hT : dest.toNat = pcT) (hF : pc + 1 = pcF) :
    (∃ (g' : Nat) (l' : Evm fork Nat), At code message pcT rest memory g' state substate l' ∧
      Gas.Ends fork l' s ∧ g' ≤ gas) ∨
    (∃ (g' : Nat) (l' : Evm fork Nat), At code message pcF rest memory g' state substate l' ∧
      Gas.Ends fork l' s ∧ g' ≤ gas) := by
  by_cases hc : cond = 0
  · obtain ⟨g', l', h', e', hg, -⟩ := stepE h0 e0 hok
      (fun G hG => Gas.jumpi_of_eq_zeroG hlt hbyte hG hc) hF
    exact .inr ⟨g', l', h', e', hg⟩
  · obtain ⟨g', l', h', e', hg, -⟩ := stepE h0 e0 hok
      (fun G hG => Gas.jumpi_takenG hlt hbyte hG hc valid) hT
    exact .inl ⟨g', l', h', e', hg⟩

/-- A rule to a halt (RETURN or REVERT) that needs `c` gas, as a fact about a run that ends with
no error: the run ends with the state and the substate of the rule. -/
theorem haltE {c : Nat} {rev : Bool} {out : ByteArray} {state' : State.TransactionState}
    {substate' : Substate} {l s : Evm fork Nat}
    (h0 : At code message pc stack memory gas state substate l) (e0 : Gas.Ends fork l s)
    (hok : s.error = none)
    (rule : ∀ G, c ≤ G → Gas.SpecG fork (At code message pc stack memory G state substate)
      (Halted rev out (G - c) state' substate')) :
    s.state = state' ∧ s.substate = substate' := by
  obtain ⟨-, -, -, -, hst, hss⟩ :=
    Gas.SpecG.lowE (rule (gas + c) (by omega)) (Gas.at_addGas h0 c) e0 hok
  exact ⟨hst, hss⟩

end Safe

end TokenKit

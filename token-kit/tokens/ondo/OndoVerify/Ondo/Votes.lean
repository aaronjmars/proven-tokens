import OndoVerify.Ondo.Instance
import OndoVerify.Ondo.Readable

/-!
# Votes of ONDO: what `mint` does to them (audit 5, fix ONDO-5)

Written by hand (not generated; the body of `mint_votes_runs` is the generated witness
`Sanity.mint_runs` with one more slot in the start state). The plan of the earlier rounds was a
"votes add up" invariant: for every delegate `d`, the votes of the latest checkpoint of `d`
equal the sum of the balances of the holders whose delegate is `d`. That statement is FALSE for
the real contract, so it is not claimed anywhere. `mint` (Ondo.sol `mint`, no `_moveDelegates`)
adds the amount to the balance of the recipient and writes no checkpoint, so after a mint of a
nonzero amount to an address that has a delegate, that delegate has fewer votes than the
balances that delegate to it. This file proves the true facts and one closed counterexample.

- `mint_keeps_checkpoint`, `mint_keeps_numCheckpoints`: a successful `mint` writes no
  `checkpoints[d][i]` slot and no `numCheckpoints[d]` slot of any delegate `d` (when that slot is
  neither slot 4 nor the balance slot of the recipient: two keccak facts, stated as hypotheses).
  Every message runner, from Berlin. (The audit wrote both in
  audits/audit-5/ondo/lean/MintVotes.lean; they are built here.)
- `mint_votes_gap`: both together with `mint_amounts`: the balance of the recipient grows by
  the amount while the checkpoint count and every checkpoint of every delegate stay as they were.
- `mint_votes_runs`, `mint_votes_counterexample`: THE CLOSED COUNTEREXAMPLE to "votes add up".
  In the state where `Witness.CALLER1` has `MINTER_ROLE`, the address word 2 has the delegate `K`
  (the address word of `Witness.CALLER1`) and every other slot is 0 (so every balance, every
  checkpoint and the total supply are 0: "votes add up" holds there), the call `mint(2, 7)` from
  `Witness.CALLER1` has a run that ends with no error, and after every such run the balance of 2
  is 7, the delegate of 2 is still `K`, and `numCheckpoints[K]` is still 0 (so
  `getCurrentVotes(K)` is 0, not 7). No keccak hypothesis: every slot fact is computed by the
  kernel.

What it means for holders (from the source and the `mvSrc` paths, not run as a witness here):
such a holder who later re-delegates moves its whole balance out of the old delegate
(`sub96`, "vote amount underflows"), and a transfer out moves the amount out of the delegate;
either reverts when the votes of the delegate are short.

What would be true instead, and is NOT proved here: every function but `mint` keeps, for every
delegate `d`, the difference (latest votes of `d`) - (sum of the balances that delegate to `d`),
and `mint` lowers it by the amount when the recipient has a delegate.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace OndoVerify.Instance

open UsdtVerify
open TokenKit TokenKit.Complete
open OndoVerify OndoVerify.Sanity OndoVerify.Paths OndoVerify.Complete UsdtVerify.Complete
  UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A successful `mint` writes no checkpoint of any delegate. -/
theorem mint_keeps_checkpoint (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none)
    (d i : U256)
    (h4 : mapSlot i (mapSlot d 8) ≠ 4)
    (hb : mapSlot i (mapSlot d 8) ≠
      mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32)) 6) :
    storageAt s.state message.currentTarget (mapSlot i (mapSlot d 8)) =
      storageAt state message.currentTarget (mapSlot i (mapSlot d 8)) :=
  (mint_readable hfork hsize' hsel start hrun hok).2.2.2.2.2 _ h4 hb

/-- A successful `mint` writes no `numCheckpoints` slot of any delegate. -/
theorem mint_keeps_numCheckpoints (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none)
    (d : U256)
    (h4 : mapSlot d 9 ≠ 4)
    (hb : mapSlot d 9 ≠
      mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32)) 6) :
    storageAt s.state message.currentTarget (mapSlot d 9) =
      storageAt state message.currentTarget (mapSlot d 9) :=
  (mint_readable hfork hsize' hsel start hrun hok).2.2.2.2.2 _ h4 hb

/-- A successful `mint(dst, amount)`: the low 96 bits of `balances[dst]` grow by the amount,
and `numCheckpoints[d]` and every `checkpoints[d][i]` of a delegate `d` stay as they were (for
the slots that are neither slot 4 nor the balance slot of `dst`). So minted tokens carry no
votes. -/
theorem mint_votes_gap (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    (hne : mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32)) 6 ≠ 4)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none)
    (d : U256)
    (hn4 : mapSlot d 9 ≠ 4)
    (hnb : mapSlot d 9 ≠
      mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32)) 6)
    (hc4 : ∀ i : U256, mapSlot i (mapSlot d 8) ≠ 4)
    (hcb : ∀ i : U256, mapSlot i (mapSlot d 8) ≠
      mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32)) 6) :
    (bitwiseAnd (79228162514264337593543950335 : U256) (storageAt s.state message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          (loadWord message.data 4 32)) 6))).toNat =
      (bitwiseAnd (79228162514264337593543950335 : U256) (storageAt state message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          (loadWord message.data 4 32)) 6))).toNat + (loadWord message.data 36 32).toNat ∧
    storageAt s.state message.currentTarget (mapSlot d 9) =
      storageAt state message.currentTarget (mapSlot d 9) ∧
    ∀ i : U256, storageAt s.state message.currentTarget (mapSlot i (mapSlot d 8)) =
      storageAt state message.currentTarget (mapSlot i (mapSlot d 8)) :=
  ⟨(mint_amounts hfork hsize' hsel hne start hrun hok).2,
    mint_keeps_numCheckpoints hfork hsize' hsel start hrun hok d hn4 hnb,
    fun i => mint_keeps_checkpoint hfork hsize' hsel start hrun hok d i (hc4 i) (hcb i)⟩

/-- The start state of the counterexample: `Witness.CALLER1` has `MINTER_ROLE`, the address
word 2 has the delegate `K`, every other slot is 0. -/
abbrev S_votes (C : Address) : State.TransactionState :=
  sState C [(mapSlot Witness.CALLER1W (mapSlot 71998914331801701415977457805802827292338598818749192222732755537001613711014 0), 1), (mapSlot 2 7, Witness.CALLER1W)]

set_option maxHeartbeats 4000000 in
/-- The call `mint(2, 7)` from `Witness.CALLER1` runs to the end with no error from `S_votes`. -/
theorem mint_votes_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_mint b t C) 0 [] .empty gas (S_votes C) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_mint b t C).data = data2 SEL_mint 2 7 := rfl
  have hsz : (m_mint b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_mint _ _
  have hsl : selector (m_mint b t C).data = selector SEL_mint := by
    rw [hdata]; exact selector_data2 size_SEL_mint _ _
  have hA1 : loadWord (m_mint b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_mint _ _
  have hA2 : loadWord (m_mint b t C).data 36 32 = 7 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_mint _ _
  have hval : (m_mint b t C).value = 0 := rfl
  have hcw : (m_mint b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_mint b t C).currentTarget = C := rfl
  have hacc : hasAccount ((S_votes C)) C := hasAccount_sState C _
  have hspec := mint_p10 (fork := fork) (message := (m_mint b t C))
    (state := (S_votes C)) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    hacc
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (m_mint b t C) (S_votes C) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _,
    fun rc within => Witness.endsL_of_reaches hr hrun rc within, ?_⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- THE CLOSED COUNTEREXAMPLE to "votes add up". From `S_votes` (every balance, checkpoint and
the total supply 0; the delegate of 2 is `K`), the call `mint(2, 7)` from `Witness.CALLER1` has a
run that ends with no error, and after every such run the balance of 2 is 7, its delegate is
still `K`, and `K` still has no checkpoint (`numCheckpoints[K] = 0`, so its current votes are
0, not 7). Every message runner, from Berlin; no keccak hypothesis. -/
theorem mint_votes_counterexample (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (ss : Substate) :
    (∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_mint b t C) 0 [] .empty gas (S_votes C) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none) ∧
    delegOf C (S_votes C) 2 = K ∧ storageAt (S_votes C) C (mapSlot K 9) = 0 ∧
    (∀ {gas : Nat} {evm s : Evm fork Nat} {bound : Nat} (runChild : MessageRunner fork Nat bound),
      At CODE (m_mint b t C) 0 [] .empty gas (S_votes C) ss evm →
      EndsL runChild evm s → s.error = none →
      (bitwiseAnd (79228162514264337593543950335 : U256)
        (storageAt s.state C (mapSlot 2 6))).toNat = 7 ∧
      delegOf C s.state 2 = K ∧ storageAt s.state C (mapSlot K 9) = 0) := by
  have hdata : (m_mint b t C).data = data2 SEL_mint 2 7 := rfl
  have hsz : (m_mint b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_mint _ _
  have hsl : selector (m_mint b t C).data = 0x40c10f19 := by
    rw [hdata, selector_data2 size_SEL_mint]; decide
  have hA1 : loadWord (m_mint b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_mint _ _
  have hA2 : loadWord (m_mint b t C).data 36 32 = 7 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_mint _ _
  have hct : (m_mint b t C).currentTarget = C := rfl
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (2 : U256) =
      2 := by decide
  have k1 : mapSlot (2 : U256) 6 ≠ 4 := by decide +kernel
  have k2 : mapSlot (2 : U256) 7 ≠ 4 := by decide +kernel
  have k3 : mapSlot (2 : U256) 7 ≠ mapSlot (2 : U256) 6 := by decide +kernel
  have k4 : mapSlot K 9 ≠ 4 := by decide +kernel
  have k5 : mapSlot K 9 ≠ mapSlot (2 : U256) 6 := by decide +kernel
  have s1 : storageAt (S_votes C) C (mapSlot 2 6) = 0 := by
    simp only [storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel
  have s2 : storageAt (S_votes C) C (mapSlot 2 7) = Witness.CALLER1W := by
    simp only [storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel
  have s3 : storageAt (S_votes C) C (mapSlot K 9) = 0 := by
    simp only [storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel
  have hd0 : delegOf C (S_votes C) 2 = K := by
    unfold delegOf; rw [s2]; decide
  refine ⟨mint_votes_runs hfork b t C ss, hd0, s3, ?_⟩
  intro gas evm s bound runChild start hrun hok
  have hsz' : (m_mint b t C).data.size < 2 ^ 256 := by rw [hsz]; decide
  have hne : mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord (m_mint b t C).data 4 32)) 6 ≠ 4 := by rw [hA1, hm2]; exact k1
  have hb := (mint_amounts hfork hsz' hsl hne start hrun hok).2
  have hfr := (mint_readable hfork hsz' hsl start hrun hok).2.2.2.2.2
  rw [hA1, hA2, hm2, hct] at hb
  rw [hA1, hm2, hct] at hfr
  rw [s1] at hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hb]; decide
  · unfold delegOf; rw [hfr _ k2 k3, s2]; decide
  · rw [hfr _ k4 k5, s3]

end OndoVerify.Instance

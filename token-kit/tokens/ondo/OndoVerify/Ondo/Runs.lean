import OndoVerify.Ondo.Instance

/-!
# Real runs of `transfer`, `transferFrom` and `delegate` (audit 5, fix ONDO-3)

Written by hand; the theorem bodies are printed by a small script (it writes the same side
condition tactic for every hypothesis of every path theorem). The success paths of these
functions cross several segments of the code (`_transferTokens` checks, the vesting check, the
balance move, `_moveDelegates`), and the witness generator of the kit handles one path theorem
only, so the generated file `Sanity/Zero.lean` has no run for them. Each theorem here joins, for
one concrete call, the path theorem of the function to one path theorem of each segment, and
computes every side condition (storage slots, keccak slots and gas, by the kernel): so each
function has at least one run from pc 0 that ends with no error, for every message runner.

- `transfer_runs`: `transfer(2, 7)` from `Witness.CALLER1` (address word `K`), in the state
  where transfers are on and `K` holds 10. Paths: `transfer_p4`, `tt0_p6`, `vest0_p20`,
  `core0_p3`, `mvSrc2_p5`.
- `transferFrom_runs`: `transferFrom(K, 2, 7)` from `Witness.CALLER1` (the spender is the
  source), the same state. Paths: `transferFrom_p9`, `tt2_p6`, `vest2_p20`, `core8_p3`,
  `mvSrc10_p5`.
- `delegate_runs`: `delegate(2)` from `Witness.CALLER1`, all-zero storage. Paths:
  `delegate_p4`, `mvSrc0_p4`.

What these runs do not show: no checkpoint writing path (`wck*`) has a witness here (both
delegates are 0 in the transfers, the balance of `K` is 0 in `delegate`), no run goes through a
vesting lock (`vest0_p0` to `vest0_p19`), and `delegateBySig` has no run (it needs a real
secp256k1 signature over the EIP-712 digest of ONDO and the forward rule of the STATICCALL to
ECRECOVER; see fix-status ONDO-3). Gas: 200000. Fork: Berlin <= fork < Glamsterdam (the bound of
the SSTORE cost that the gas side conditions use is the one of the one-counter meter).

`writeMax_le`, `writeCost_le22100`, `endsL_join` and the tactics `gas_bound`, `acc_side` are
copies of the ones of `tokens/uni` (`PermitRun.lean`, `Runs.lean`), listed under
`to_merge_into_kit` in status.json.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace OndoVerify.Instance

open UsdtVerify
open TokenKit
open OndoVerify OndoVerify.Sanity OndoVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- Before Glamsterdam an SSTORE costs at most 22100. -/
theorem writeMax_le (hglam : fork < .glamsterdam) : Gas.writeMax fork ≤ 22100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [Gas.writeMax, hng]

/-- Before Glamsterdam, from Berlin, an SSTORE costs at most 22100. -/
theorem writeCost_le22100 (hberlin : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (o c n : U256) (cold : Bool) : Gas.writeCost fork o c n cold ≤ 22100 :=
  Nat.le_trans (Gas.writeCost_le hberlin o c n cold) (writeMax_le hglam)

/-- Gas side conditions: every `slotCost` is at most 2100 and every `writeCost` at most 22100;
the rest is linear arithmetic. -/
macro "gas_bound" : tactic => `(tactic| (
  repeat (generalize hx : slotCost _ = x
          have : x ≤ 2100 := by rw [← hx]; exact UsdtVerify.slotCost_le _
          clear hx)
  repeat (generalize hx : Gas.writeCost _ _ _ _ _ = x
          have : x ≤ 22100 := by
            rw [← hx]; exact writeCost_le22100 (by assumption) (by assumption) _ _ _ _
          clear hx)
  omega))

/-- The contract has its account after reads and writes of its slots. -/
macro "acc_side" : tactic => `(tactic| (repeat' (first
  | with_reducible assumption
  | apply UsdtVerify.hasAccount_writeSlot
  | apply UsdtVerify.hasAccount_readSlot)) <;> done)

/-- The loop of the interpreter, from a frame that reaches `z`, ends where the run from `z`
ends. -/
theorem endsL_join {evm z s : Evm fork Nat}
    (h1 : Reaches (Logic.StepG fork) evm z) (h2 : Reaches (Logic.StepG fork) z s)
    (hrun : s.running = false) {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : EndsL runChild evm s := by
  have w0 : GasMeter.gasHeld z.gas ≤ bound :=
    Nat.le_trans ((h1.mono And.left).gasHeld_le Step.gasHeld_le) within
  obtain ⟨_, e2⟩ := Witness.endsL_of_reaches h2 hrun runChild w0
  exact ⟨within, (runFrame_eq_of_reaches (bound := bound) (runChild := runChild)
    Step.gasHeld_le Step.runFrame_eq (h1.mono And.left) within).trans e2⟩

/-- The four bytes of the selector of `transfer`. -/
def SEL_transfer : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩

theorem size_SEL_transfer : SEL_transfer.size = 4 := by decide

/-- The call `transfer(2, 7)` from `Witness.CALLER1` to `C`. -/
abbrev m_transfer (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data2 SEL_transfer 2 7)

/-- The start state of `transfer_runs`: transfers are on (slot 3, `transferAllowed`, is 1) and `K` holds 10 tokens (slot `balances[K]`); every other slot is 0 (no lock, no delegate, no checkpoint). -/
abbrev S_transfer (C : Address) : State.TransactionState :=
  sState C [(3, 1), (mapSlot Witness.CALLER1W 6, 10)]

set_option maxHeartbeats 8000000 in
/-- `transfer(2, 7)` from `Witness.CALLER1` has a run that ends with no error: the paths `transfer_p4` (checks of the call data), `tt0_p6` (transfers are on), `vest0_p20` (no lock on `K`), `core0_p3` (the balance of `K` goes from 10 to 3, the one of 2 from 0 to 7), `mvSrc2_p5` (both delegates are 0: no vote moves). -/
theorem transfer_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_transfer b t C) 0 [] .empty 200000 (S_transfer C) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_transfer b t C).data = data2 SEL_transfer 2 7 := rfl
  have hsz : (m_transfer b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_transfer _ _
  have hsl : selector (m_transfer b t C).data = selector SEL_transfer := by
    rw [hdata]; exact selector_data2 size_SEL_transfer _ _
  have hA1 : loadWord (m_transfer b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_transfer _ _
  have hA2 : loadWord (m_transfer b t C).data 36 32 = 7 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_transfer _ _
  have hval : (m_transfer b t C).value = 0 := rfl
  have hcw : (m_transfer b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_transfer b t C).currentTarget = C := rfl
  have hacc : hasAccount (S_transfer C) C := hasAccount_sState C _
  have m1 := transfer_p4_mem
  have m3 := vest0_p20_mem (a0 := (loadWord (m_transfer b t C).data 36 32)) (a1 := (loadWord (m_transfer b t C).data 4 32)) (a2 := (m_transfer b t C).caller.toU256) (a3 := (BitVec.ofNat 256 (selector (m_transfer b t C).data))) m1.1 m1.2.1
  have m4 := core0_p3_mem (a0 := (loadWord (m_transfer b t C).data 36 32)) (a1 := (loadWord (m_transfer b t C).data 4 32)) (a2 := (m_transfer b t C).caller.toU256) (a3 := (BitVec.ofNat 256 (selector (m_transfer b t C).data))) m3.1 m3.2.1
  obtain ⟨z1, hr1, hz1⟩ := (transfer_p4 (fork := fork) (message := (m_transfer b t C))
    (state := S_transfer C) (substate := ss) (gas := 200000) hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) (sFrame (m_transfer b t C) (S_transfer C) ss 200000) (at_sFrame _ rfl _ _ _)
  obtain ⟨z2, hr2, hz2⟩ := (tt0_p6 (fork := fork) hfork
    m1.1
    m1.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z1 hz1
  obtain ⟨z3, hr3, hz3⟩ := (vest0_p20 (fork := fork) hfork
    m1.1
    m1.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z2 hz2
  obtain ⟨z4, hr4, hz4⟩ := (core0_p3 (fork := fork) hfork
    m3.1
    m3.2.1
    rfl
    (by (try rw [hct]); acc_side)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z3 hz3
  obtain ⟨s, hr5, hrun, hH⟩ := (mvSrc2_p5 (fork := fork) hfork
    m4.1
    m4.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z4 hz4
  refine ⟨_, s, at_sFrame _ rfl _ _ _,
    fun rc within => endsL_join (((hr1.trans hr2).trans hr3).trans hr4) hr5 hrun rc within, ?_⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- The four bytes of the selector of `transferFrom`. -/
def SEL_transferFrom : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

theorem size_SEL_transferFrom : SEL_transferFrom.size = 4 := by decide

/-- The call `transferFrom(K, 2, 7)` from `Witness.CALLER1` to `C`. -/
abbrev m_transferFrom (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data3 SEL_transferFrom Witness.CALLER1W 2 7)

/-- The start state of `transferFrom_runs`: the same as `S_transfer`. -/
abbrev S_transferFrom (C : Address) : State.TransactionState :=
  sState C [(3, 1), (mapSlot Witness.CALLER1W 6, 10)]

set_option maxHeartbeats 8000000 in
/-- `transferFrom(K, 2, 7)` from `Witness.CALLER1` (the spender is the source, so no allowance is read or written) has a run that ends with no error: the paths `transferFrom_p9`, `tt2_p6`, `vest2_p20`, `core8_p3` (10 to 3 and 0 to 7), `mvSrc10_p5` (no vote moves). -/
theorem transferFrom_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_transferFrom b t C) 0 [] .empty 200000 (S_transferFrom C) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_transferFrom b t C).data = data3 SEL_transferFrom Witness.CALLER1W 2 7 := rfl
  have hsz : (m_transferFrom b t C).data.size = 100 := by
    rw [hdata]; exact size_data3 size_SEL_transferFrom _ _ _
  have hsl : selector (m_transferFrom b t C).data = selector SEL_transferFrom := by
    rw [hdata]; exact selector_data3 size_SEL_transferFrom _ _ _
  have hA1 : loadWord (m_transferFrom b t C).data 4 32 = Witness.CALLER1W := by
    rw [hdata]; exact Witness.arg1_data3 size_SEL_transferFrom _ _ _
  have hA2 : loadWord (m_transferFrom b t C).data 36 32 = 2 := by
    rw [hdata]; exact Witness.arg2_data3 size_SEL_transferFrom _ _ _
  have hA3 : loadWord (m_transferFrom b t C).data 68 32 = 7 := by
    rw [hdata]; exact Witness.arg3_data3 size_SEL_transferFrom _ _ _
  have hval : (m_transferFrom b t C).value = 0 := rfl
  have hcw : (m_transferFrom b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_transferFrom b t C).currentTarget = C := rfl
  have hacc : hasAccount (S_transferFrom C) C := hasAccount_sState C _
  have m1 := transferFrom_p9_mem (message := (m_transferFrom b t C))
  have m3 := vest2_p20_mem (a0 := (loadWord (m_transferFrom b t C).data 68 32)) (a1 := (loadWord (m_transferFrom b t C).data 36 32)) (a2 := (loadWord (m_transferFrom b t C).data 4 32)) (a3 := (bitwiseAnd (storageAt (S_transferFrom C) (m_transferFrom b t C).currentTarget (mapSlot (m_transferFrom b t C).caller.toU256 (mapSlot (bitwiseAnd (loadWord (m_transferFrom b t C).data 4 32) (1461501637330902918203684832716283019655932542975 : U256)) (5 : U256)))) (79228162514264337593543950335 : U256))) (a4 := (m_transferFrom b t C).caller.toU256) (a5 := (BitVec.ofNat 256 (selector (m_transferFrom b t C).data))) m1.1 m1.2.1
  have m4 := core8_p3_mem (a0 := (loadWord (m_transferFrom b t C).data 68 32)) (a1 := (loadWord (m_transferFrom b t C).data 36 32)) (a2 := (loadWord (m_transferFrom b t C).data 4 32)) (a3 := (bitwiseAnd (storageAt (S_transferFrom C) (m_transferFrom b t C).currentTarget (mapSlot (m_transferFrom b t C).caller.toU256 (mapSlot (bitwiseAnd (loadWord (m_transferFrom b t C).data 4 32) (1461501637330902918203684832716283019655932542975 : U256)) (5 : U256)))) (79228162514264337593543950335 : U256))) (a4 := (m_transferFrom b t C).caller.toU256) (a5 := (BitVec.ofNat 256 (selector (m_transferFrom b t C).data))) m3.1 m3.2.1
  obtain ⟨z1, hr1, hz1⟩ := (transferFrom_p9 (fork := fork) (message := (m_transferFrom b t C))
    (state := S_transferFrom C) (substate := ss) (gas := 200000) hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) (sFrame (m_transferFrom b t C) (S_transferFrom C) ss 200000) (at_sFrame _ rfl _ _ _)
  obtain ⟨z2, hr2, hz2⟩ := (tt2_p6 (fork := fork) hfork
    m1.1
    m1.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z1 hz1
  obtain ⟨z3, hr3, hz3⟩ := (vest2_p20 (fork := fork) hfork
    m1.1
    m1.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z2 hz2
  obtain ⟨z4, hr4, hz4⟩ := (core8_p3 (fork := fork) hfork
    m3.1
    m3.2.1
    rfl
    (by (try rw [hct]); acc_side)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z3 hz3
  obtain ⟨s, hr5, hrun, hH⟩ := (mvSrc10_p5 (fork := fork) hfork
    m4.1
    m4.2.1
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z4 hz4
  refine ⟨_, s, at_sFrame _ rfl _ _ _,
    fun rc within => endsL_join (((hr1.trans hr2).trans hr3).trans hr4) hr5 hrun rc within, ?_⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- The four bytes of the selector of `delegate`. -/
def SEL_delegate : ByteArray := ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩

theorem size_SEL_delegate : SEL_delegate.size = 4 := by decide

/-- The call `delegate(2)` from `Witness.CALLER1` to `C`. -/
abbrev m_delegate (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data1 SEL_delegate 2)

/-- The start state of `delegate_runs`: `K` holds 10 tokens; every other slot is 0 (no delegate, no checkpoint). -/
abbrev S_delegate (C : Address) : State.TransactionState :=
  sState C [(mapSlot Witness.CALLER1W 6, 10)]

set_option maxHeartbeats 8000000 in
/-- `delegate(2)` from `Witness.CALLER1` has a run that ends with no error, in a block whose number is below `2^32`: the paths `delegate_p4` (it writes `delegates[K] = 2`), `mvSrc0_p3` (the old delegate is 0: nothing to take votes from), `mvDst0_p0` (2 has no checkpoint yet), `wck2_p7` (it writes the first checkpoint of 2, with 10 votes, and `numCheckpoints[2] = 1`). -/
theorem delegate_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) (hnum : b.number < 4294967296) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_delegate b t C) 0 [] .empty 200000 (S_delegate C) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_delegate b t C).data = data1 SEL_delegate 2 := rfl
  have hsz : (m_delegate b t C).data.size = 36 := by
    rw [hdata]; exact size_data1 size_SEL_delegate _
  have hsl : selector (m_delegate b t C).data = selector SEL_delegate := by
    rw [hdata]; exact selector_data1 size_SEL_delegate _
  have hA1 : loadWord (m_delegate b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data1 size_SEL_delegate _
  have hval : (m_delegate b t C).value = 0 := rfl
  have hcw : (m_delegate b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_delegate b t C).currentTarget = C := rfl
  have hacc : hasAccount (S_delegate C) C := hasAccount_sState C _
  have m3 := mvDst0_p0_mem (a0 := 0) (a1 := loadWord (m_delegate b t C).data 4 32) (a2 := 0) (a3 := 0) (a4 := 0) (a5 := 0)
  obtain ⟨z1, hr1, hz1⟩ := (delegate_p4 (fork := fork) (message := (m_delegate b t C))
    (state := S_delegate C) (substate := ss) (gas := 200000) hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (by (try rw [hct]); acc_side)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) (sFrame (m_delegate b t C) (S_delegate C) ss 200000) (at_sFrame _ rfl _ _ _)
  obtain ⟨z2, hr2, hz2⟩ := (mvSrc0_p3 (fork := fork) hfork
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z1 hz1
  obtain ⟨z3, hr3, hz3⟩ := (mvDst0_p0 (fork := fork) hfork
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z2 hz2
  obtain ⟨s, hr4, hrun, hH⟩ := (wck2_p7 (fork := fork) hfork
    m3.1
    m3.2.1
    rfl
    (by (try rw [hct]); acc_side)
    (by
      show (lessThan (BitVec.ofNat 256 b.number) (4294967296 : U256)) ≠ 0
      simp only [OndoVerify.c_lt_ne, BitVec.toNat_ofNat, BitVec.reduceToNat]
      omega)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hcw, hct, storageAt_readSlot, TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by gas_bound)
    ) z3 hz3
  refine ⟨_, s, at_sFrame _ rfl _ _ _,
    fun rc within => endsL_join ((hr1.trans hr2).trans hr3) hr4 hrun rc within, ?_⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

end OndoVerify.Instance

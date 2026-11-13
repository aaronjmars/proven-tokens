import UniVerify.Uni.PermitRun

/-!
# Real runs of `transfer`, `transferFrom`, `mint` and `delegate` (audit 4, fix 6, UNI-3)

Written by hand (not generated). The success paths of these four functions end at the entry of
the `_moveDelegates` code (pc 6946), and the witness generator of the kit handles one path
theorem only, so the generated file `Sanity/Zero.lean` has no run for them. This file joins, for
one concrete call each, the path theorem of the function to one path theorem of the
`_moveDelegates` segment, and computes every side condition: so each of the four functions has
at least one run from pc 0 that ends with no error.

- `transfer_runs`: `transfer(2, 0)` from `Witness.CALLER1`, all-zero storage.
- `transferFrom_runs`: `transferFrom(CALLER1, 2, 0)` from `Witness.CALLER1` (the spender is the
  source), all-zero storage.
- `mint_runs`: `mint(2, 0)` from `Witness.CALLER1`, in the state where the minter (slot 1) is
  `CALLER1` and every other slot is 0, in a block with time stamp 1. After the run
  `mintingAllowedAfter` (slot 2) is `1 + 31536000`.
- `delegate_runs`: `delegate(2)` from `Witness.CALLER1`, all-zero storage. After the run the
  delegate of `CALLER1` (slot `keccak(CALLER1, 5)`) is 2.

All four move no votes (the amount is 0, or both delegates are the same): the checkpoint
writing paths of `_moveDelegates` have no witness. The runs hold for every message runner (no
call is made). Gas: 200000. Fork: Berlin <= fork < Glamsterdam (the bound of the SSTORE cost
that the gas side conditions use is the one of the one-counter meter).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace UniVerify.Instance

open UsdtVerify
open TokenKit
open UniVerify UniVerify.Sanity UniVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

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

/-- The call of the witness of `transfer`, from `Witness.CALLER1` to `C`. -/
abbrev m_transfer (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data2 SEL_transfer 2 0)

set_option maxHeartbeats 4000000 in
/-- `transfer` has a run that ends with no error: the path `transfer_p9`, then the path `mvSrc0_p11` of
the `_moveDelegates` code. -/
theorem transfer_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_transfer b t C) 0 [] .empty 200000 (sState C []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_transfer b t C).data = data2 SEL_transfer 2 0 := rfl
  have hsz : (m_transfer b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_transfer _ _
  have hsl : selector (m_transfer b t C).data = selector SEL_transfer := by
    rw [hdata]; exact selector_data2 size_SEL_transfer _ _
  have hA1 : loadWord (m_transfer b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_transfer _ _
  have hA2 : loadWord (m_transfer b t C).data 36 32 = 0 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_transfer _ _
  have hval : (m_transfer b t C).value = 0 := rfl
  have hcw : (m_transfer b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_transfer b t C).currentTarget = C := rfl
  have hbe : (m_transfer b t C).blockEnv = b := rfl
  have hacc : hasAccount (sState C []) C := hasAccount_sState C _
  have hpre := transfer_p9 (fork := fork) (message := (m_transfer b t C))
    (state := (sState C [])) (substate := ss) (gas := 200000) hfork
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m_transfer b t C) (sState C []) ss 200000)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨s, hr2, hrun, hH⟩ := (mvSrc0_p11 (fork := fork) hfork
    transfer_p9_mem.1
    transfer_p9_mem.2.1
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)) z hz
  refine ⟨_, s, at_sFrame _ rfl _ _ _, fun rc within => endsL_join hrz hr2 hrun rc within,
    ?_⟩
  · obtain ⟨-, he, -⟩ := hH
    simpa using he

/-- The four bytes of the selector of `transferFrom`. -/
def SEL_transferFrom : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

theorem size_SEL_transferFrom : SEL_transferFrom.size = 4 := by decide

/-- The call of the witness of `transferFrom`, from `Witness.CALLER1` to `C`. -/
abbrev m_transferFrom (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data3 SEL_transferFrom Witness.CALLER1W 2 0)

set_option maxHeartbeats 4000000 in
/-- `transferFrom` has a run that ends with no error: the path `transferFrom_p23`, then the path `mvSrc2_p11` of
the `_moveDelegates` code. -/
theorem transferFrom_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_transferFrom b t C) 0 [] .empty 200000 (sState C []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none := by
  have hdata : (m_transferFrom b t C).data = data3 SEL_transferFrom Witness.CALLER1W 2 0 := rfl
  have hsz : (m_transferFrom b t C).data.size = 100 := by
    rw [hdata]; exact size_data3 size_SEL_transferFrom _ _ _
  have hsl : selector (m_transferFrom b t C).data = selector SEL_transferFrom := by
    rw [hdata]; exact selector_data3 size_SEL_transferFrom _ _ _
  have hA1 : loadWord (m_transferFrom b t C).data 4 32 = Witness.CALLER1W := by
    rw [hdata]; exact Witness.arg1_data3 size_SEL_transferFrom _ _ _
  have hA2 : loadWord (m_transferFrom b t C).data 36 32 = 2 := by
    rw [hdata]; exact Witness.arg2_data3 size_SEL_transferFrom _ _ _
  have hA3 : loadWord (m_transferFrom b t C).data 68 32 = 0 := by
    rw [hdata]; exact Witness.arg3_data3 size_SEL_transferFrom _ _ _
  have hval : (m_transferFrom b t C).value = 0 := rfl
  have hcw : (m_transferFrom b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_transferFrom b t C).currentTarget = C := rfl
  have hbe : (m_transferFrom b t C).blockEnv = b := rfl
  have hacc : hasAccount (sState C []) C := hasAccount_sState C _
  have hpre := transferFrom_p23 (fork := fork) (message := (m_transferFrom b t C))
    (state := (sState C [])) (substate := ss) (gas := 200000) hfork
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m_transferFrom b t C) (sState C []) ss 200000)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨s, hr2, hrun, hH⟩ := (mvSrc2_p11 (fork := fork) hfork
    transferFrom_p23_mem.1
    transferFrom_p23_mem.2.1
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hA3, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)) z hz
  refine ⟨_, s, at_sFrame _ rfl _ _ _, fun rc within => endsL_join hrz hr2 hrun rc within,
    ?_⟩
  · obtain ⟨-, he, -⟩ := hH
    simpa using he

/-- The four bytes of the selector of `mint`. -/
def SEL_mint : ByteArray := ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩

theorem size_SEL_mint : SEL_mint.size = 4 := by decide

/-- The call of the witness of `mint`, from `Witness.CALLER1` to `C`. -/
abbrev m_mint (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data2 SEL_mint 2 0)

set_option maxHeartbeats 4000000 in
/-- `mint` has a run that ends with no error: the path `mint_p13`, then the path `mvSrc3_p2` of
the `_moveDelegates` code. After it slot 2 (`mintingAllowedAfter`) is
`1 + 31536000`. -/
theorem mint_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (hts : b.timestamp = 1) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_mint b t C) 0 [] .empty 200000 (sState C [(1, Witness.CALLER1W)]) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      storageAt s.state C 2 = (31536001 : U256) := by
  have hdata : (m_mint b t C).data = data2 SEL_mint 2 0 := rfl
  have hsz : (m_mint b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_mint _ _
  have hsl : selector (m_mint b t C).data = selector SEL_mint := by
    rw [hdata]; exact selector_data2 size_SEL_mint _ _
  have hA1 : loadWord (m_mint b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_mint _ _
  have hA2 : loadWord (m_mint b t C).data 36 32 = 0 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_mint _ _
  have hval : (m_mint b t C).value = 0 := rfl
  have hcw : (m_mint b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_mint b t C).currentTarget = C := rfl
  have hbe : (m_mint b t C).blockEnv = b := rfl
  have hacc : hasAccount (sState C [(1, Witness.CALLER1W)]) C := hasAccount_sState C _
  have hpre := mint_p13 (fork := fork) (message := (m_mint b t C))
    (state := (sState C [(1, Witness.CALLER1W)])) (substate := ss) (gas := 200000) hfork
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m_mint b t C) (sState C [(1, Witness.CALLER1W)]) ss 200000)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨s, hr2, hrun, hH⟩ := (mvSrc3_p2 (fork := fork) hfork
    mint_p13_mem.1
    mint_p13_mem.2.1
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)) z hz
  refine ⟨_, s, at_sFrame _ rfl _ _ _, fun rc within => endsL_join hrz hr2 hrun rc within,
    ?_, ?_⟩
  · obtain ⟨-, he, -⟩ := hH
    simpa using he
  · obtain ⟨-, -, -, -, hst, -⟩ := hH
    rw [hst]
    simp (disch := supply_side) only
          [hval, hsz, hA1, hA2, hcw, hct, hbe, hts, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel

/-- The four bytes of the selector of `delegate`. -/
def SEL_delegate : ByteArray := ⟨#[0x5c, 0x19, 0xa9, 0x5c]⟩

theorem size_SEL_delegate : SEL_delegate.size = 4 := by decide

/-- The call of the witness of `delegate`, from `Witness.CALLER1` to `C`. -/
abbrev m_delegate (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data1 SEL_delegate 2)

set_option maxHeartbeats 4000000 in
/-- `delegate` has a run that ends with no error: the path `delegate_p4`, then the path `mvSrc4_p10` of
the `_moveDelegates` code. After it the delegate of the caller
is 2. -/
theorem delegate_runs (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (m_delegate b t C) 0 [] .empty 200000 (sState C []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      storageAt s.state C (mapSlot Witness.CALLER1W 5) = (2 : U256) := by
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
  have hbe : (m_delegate b t C).blockEnv = b := rfl
  have hacc : hasAccount (sState C []) C := hasAccount_sState C _
  have hpre := delegate_p4 (fork := fork) (message := (m_delegate b t C))
    (state := (sState C [])) (substate := ss) (gas := 200000) hfork
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
  obtain ⟨z, hrz, hz⟩ := hpre (sFrame (m_delegate b t C) (sState C []) ss 200000)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨s, hr2, hrun, hH⟩ := (mvSrc4_p10 (fork := fork) hfork
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)
    (by first
      | exact hacc
      | exact (rfl : _ = false)
      | (rw [hsz]; decide)
      | (rw [hsl]; decide)
      | gas_bound
      | (simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel)
      | decide +kernel)) z hz
  refine ⟨_, s, at_sFrame _ rfl _ _ _, fun rc within => endsL_join hrz hr2 hrun rc within,
    ?_, ?_⟩
  · obtain ⟨-, he, -⟩ := hH
    simpa using he
  · obtain ⟨-, -, -, -, hst, -⟩ := hH
    rw [hst]
    simp (disch := supply_side) only
          [hval, hsz, hA1, hcw, hct, storageAt_readSlot,
          TokenKit.Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil] <;> decide +kernel

end UniVerify.Instance

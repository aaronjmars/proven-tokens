import EnaVerify.Ena.Gen
import TokenKit.Evm.Witness
import TokenKit.Evm.WitnessOpt

/-!
# Sanity: the success path of `mint` has a concrete run

Written by hand (the generator of `Sanity/Zero.lean` takes every block as it is, and `mint`
needs a block time): `mint_runs`.

The call `mint(2, 1)` from `Witness.CALLER1`, in a block whose time is 31536000 (365 days after
time 0), to a contract `C` whose state holds the caller as the owner (slot 0), a total supply of
10 (slot 4) and a last mint time of 0 (slot 11 is 0). The cap is `10 * 10 / 100 = 1`, so the
amount 1 passes. The call meets every hypothesis of the success path theorem `mint_p11`, so the
loop of the interpreter runs it from pc 0 to the end with no error, for every message runner and
every gas bound that holds its gas. Every condition is computed by the kernel.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace EnaVerify.Sanity

open UsdtVerify
open TokenKit
open EnaVerify EnaVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The four bytes of the selector of `mint(address,uint256)`. -/
def SEL_mint : ByteArray := ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩

theorem size_SEL_mint : SEL_mint.size = 4 := by decide

/-- The block `b` with the time 31536000 (365 days, in seconds). -/
abbrev atYear (b : BlockEnvironment fork) : BlockEnvironment fork :=
  { b with timestamp := (31536000 : U256) }

/-- The call `mint(2, 1)` from `Witness.CALLER1` to `C`, in the block `b` at time 31536000. -/
abbrev m_mint (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : Message fork :=
  sMsg (atYear b) t C Witness.CALLER1 CODE (data2 SEL_mint 2 1)

set_option maxHeartbeats 2000000 in
/-- The success path `mint_p11` is not empty: with the caller as the owner, a total supply of 10,
no mint before and a block time of 365 days, `mint(2, 1)` runs to the end with no error. -/
theorem mint_runs (hfork : .shapella ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_mint b t C) 0 [] .empty gas (sState C [(0, Witness.CALLER1W), (4, 10)]) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧ s.error = none ∧
      s.output = ByteArray.empty := by
  have hdata : (m_mint b t C).data = data2 SEL_mint 2 1 := rfl
  have hsz : (m_mint b t C).data.size = 68 := by
    rw [hdata]; exact size_data2 size_SEL_mint _ _
  have hsl : selector (m_mint b t C).data = selector SEL_mint := by
    rw [hdata]; exact selector_data2 size_SEL_mint _ _
  have hA1 : loadWord (m_mint b t C).data 4 32 = 2 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_mint _ _
  have hA2 : loadWord (m_mint b t C).data 36 32 = 1 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_mint _ _
  have hval : (m_mint b t C).value = 0 := rfl
  have hcw : (m_mint b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256
  have hct : (m_mint b t C).currentTarget = C := rfl
  have hts : (m_mint b t C).blockEnv.timestamp = (31536000 : U256) := rfl
  have hacc : hasAccount (sState C [(0, Witness.CALLER1W), (4, 10)]) C := hasAccount_sState C _
  have hspec := mint_p11 (fork := fork) (message := (m_mint b t C))
    (state := sState C [(0, Witness.CALLER1W), (4, 10)]) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    hacc
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hval, hsz, hA1, hA2, hcw, hct, hts, storageAt_readSlot, Readable.storageAt_writeSlot_ite, storageAt_sState_cons, storageAt_sState_nil]
      <;> decide +kernel)
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (m_mint b t C) (sState C [(0, Witness.CALLER1W), (4, 10)]) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, fun rc within => Witness.endsL_of_reaches hr hrun rc within, ?_,
    hH.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

end EnaVerify.Sanity

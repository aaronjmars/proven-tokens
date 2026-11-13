import WethVerify.Weth.Sanity.Zero
import WethVerify.Weth.TotalSupply
import WethVerify.Weth.Sep

/-!
# Sanity: the success paths that the generated witnesses do not cover

Written by hand, with the tools of Evm/Witness.lean. Each theorem gives one concrete call on one
concrete state where every hypothesis of a success path theorem holds, and the run that the
theorem gives. No fact about keccak is used.

- `transferFrom_p4_runs`: the path with the allowance check (the source is not the caller and
  the allowance is not 2^256 - 1): `transferFrom(1, 2, 0)`, every slot 0.
- `transferFrom_p6_runs`: the path of the unlimited allowance: `transferFrom(1, 2, 0)` in a
  state where `allowance[1][caller]` is 2^256 - 1.
- `transferFrom_p8_runs`: the path where the source is the caller:
  `transferFrom(caller, 2, 0)`.
- `deposit_moves`: `deposit()` with a value of 5 wei: the run ends with no error and
  `balanceOf[caller]` is 5 at the end (it was 0).
- `totalSupply_runs`: `totalSupply()`: the run ends with no error and returns the ether
  balance of the contract.

The caller is any address whose address word is `Witness.CALLER1W`; `Witness.caller1_word`
gives one (`Witness.CALLER1`).

There is no witness for `withdraw` here: see `not_proved` in status.json.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace WethVerify.Sanity

open UsdtVerify
open TokenKit
open WethVerify WethVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The four bytes of the selector of `transferFrom(address,address,uint256)`. -/
def SEL_transferFrom : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

theorem size_SEL_transferFrom : SEL_transferFrom.size = 4 := by decide

/-- The call `transferFrom(1, 2, 0)` from `caller` to `C`. -/
abbrev mF4 (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE (data3 SEL_transferFrom 1 2 0)

/-- The success path `transferFrom_p4` (allowance checked and lowered) is not empty. -/
theorem transferFrom_p4_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate)
    (hcal : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 = Witness.CALLER1W) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (mF4 b t C caller) 0 [] .empty gas (sState C []) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) := by
  have hdata : (mF4 b t C caller).data = data3 SEL_transferFrom 1 2 0 := rfl
  have hsz : (mF4 b t C caller).data.size = 100 := by
    rw [hdata]; exact size_data3 size_SEL_transferFrom _ _ _
  have hsl : selector (mF4 b t C caller).data = selector SEL_transferFrom := by
    rw [hdata]; exact selector_data3 size_SEL_transferFrom _ _ _
  have hA1 : loadWord (mF4 b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data3 size_SEL_transferFrom _ _ _
  have hA3 : loadWord (mF4 b t C caller).data 68 32 = 0 := by
    rw [hdata]; exact Witness.arg3_data3 size_SEL_transferFrom _ _ _
  have hval : (mF4 b t C caller).value = 0 := rfl
  have hspec := transferFrom_p4 (fork := fork) (message := (mF4 b t C caller))
    (state := (sState C [])) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (hasAccount_sState C _)
    (by rw [hval]; decide)
    (by rw [hA3]; exact Witness.nolt0 _)
    (by
      rw [hA1]
      refine Witness.eq2_ne ?_
      show _ ≠ bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256
      rw [hcal]
      decide)
    (by
      refine Witness.eq2_ne ?_
      rw [storageAt_readSlot]
      show storageAt (sState C []) C _ ≠ _
      rw [storageAt_sState_nil]
      decide)
    (by rw [hA3]; exact Witness.nolt0 _)
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mF4 b t C caller) (sState C []) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- A state where `allowance[1][caller]` is 2^256 - 1 and every other slot is 0. -/
abbrev sF6 (C caller : Address) : State.TransactionState :=
  sState C [(mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)
    (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) 1) 4),
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256))]

/-- The call `transferFrom(1, 2, 0)` from `caller` to `C`. -/
abbrev mF6 (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE (data3 SEL_transferFrom 1 2 0)

/-- The success path `transferFrom_p6` (unlimited allowance, not lowered) is not empty. -/
theorem transferFrom_p6_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate)
    (hcal : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 = Witness.CALLER1W) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (mF6 b t C caller) 0 [] .empty gas (sF6 C caller) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) := by
  have hdata : (mF6 b t C caller).data = data3 SEL_transferFrom 1 2 0 := rfl
  have hsz : (mF6 b t C caller).data.size = 100 := by
    rw [hdata]; exact size_data3 size_SEL_transferFrom _ _ _
  have hsl : selector (mF6 b t C caller).data = selector SEL_transferFrom := by
    rw [hdata]; exact selector_data3 size_SEL_transferFrom _ _ _
  have hA1 : loadWord (mF6 b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data3 size_SEL_transferFrom _ _ _
  have hA3 : loadWord (mF6 b t C caller).data 68 32 = 0 := by
    rw [hdata]; exact Witness.arg3_data3 size_SEL_transferFrom _ _ _
  have hval : (mF6 b t C caller).value = 0 := rfl
  have hspec := transferFrom_p6 (fork := fork) (message := (mF6 b t C caller))
    (state := (sF6 C caller)) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (hasAccount_sState C _)
    (by rw [hval]; decide)
    (by rw [hA3]; exact Witness.nolt0 _)
    (by
      rw [hA1]
      refine Witness.eq2_ne ?_
      show _ ≠ bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256
      rw [hcal]
      decide)
    (by
      refine Witness.eq2_eq ?_
      rw [hA1, storageAt_readSlot]
      simp only [mask_idem]
      show storageAt (sState C _) C _ = _
      rw [storageAt_sState_cons]
      exact if_pos rfl)
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mF6 b t C caller) (sF6 C caller) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- The call `transferFrom(Witness.CALLER1W, 2, 0)` from `caller` to `C`. -/
abbrev mF8 (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE (data3 SEL_transferFrom Witness.CALLER1W 2 0)

/-- The success path `transferFrom_p8` (the source is the caller: no allowance is read) is not empty. -/
theorem transferFrom_p8_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate)
    (hcal : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 = Witness.CALLER1W) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (mF8 b t C caller) 0 [] .empty gas (sState C []) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) := by
  have hdata : (mF8 b t C caller).data = data3 SEL_transferFrom Witness.CALLER1W 2 0 := rfl
  have hsz : (mF8 b t C caller).data.size = 100 := by
    rw [hdata]; exact size_data3 size_SEL_transferFrom _ _ _
  have hsl : selector (mF8 b t C caller).data = selector SEL_transferFrom := by
    rw [hdata]; exact selector_data3 size_SEL_transferFrom _ _ _
  have hA1 : loadWord (mF8 b t C caller).data 4 32 = Witness.CALLER1W := by
    rw [hdata]; exact Witness.arg1_data3 size_SEL_transferFrom _ _ _
  have hA3 : loadWord (mF8 b t C caller).data 68 32 = 0 := by
    rw [hdata]; exact Witness.arg3_data3 size_SEL_transferFrom _ _ _
  have hval : (mF8 b t C caller).value = 0 := rfl
  have hspec := transferFrom_p8 (fork := fork) (message := (mF8 b t C caller))
    (state := (sState C [])) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (hasAccount_sState C _)
    (by rw [hval]; decide)
    (by rw [hA3]; exact Witness.nolt0 _)
    (by
      rw [hA1]
      refine Witness.eq2_eq ?_
      show _ = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256
      rw [hcal]
      decide)
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mF8 b t C caller) (sState C []) ss _)
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-- The call `deposit()` with a value of 5 wei from `caller` to `C`. -/
abbrev mD5 (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  { sMsg b t C caller CODE SEL_deposit with value := 5 }

/-- `deposit()` with 5 wei, in the state where every slot is 0: the run ends with no error and
`balanceOf[caller]` is 5 at the end. -/
theorem deposit_moves (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (mD5 b t C caller) 0 [] .empty gas (sState C []) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = ByteArray.empty ∧
      storageAt (sState C []) C (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3) = 0 ∧
      storageAt s.state C (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3) = 5 := by
  have hsz : (mD5 b t C caller).data.size = 4 := size_SEL_deposit
  have hsl : selector (mD5 b t C caller).data = selector SEL_deposit := rfl
  have hspec := deposit_p1 (fork := fork) (message := mD5 b t C caller)
    (state := sState C []) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    rfl
    (hasAccount_sState C [])
    (Nat.lt_succ_self _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mD5 b t C caller) (sState C []) ss _)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨-, he, ho, -, hs, -⟩ := hH
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, by simpa using he,
    ho, storageAt_sState_nil C _, ?_⟩
  rw [hs]
  simp only [mask_idem]
  show storageAt (writeSlot (readSlot (sState C []) C (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3)) C
    (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3)
    (add (storageAt (sState C []) C (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3)) 5)) C
    (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256) 3) = 5
  rw [storageAt_writeSlot_self (hasAccount_readSlot (hasAccount_sState C [])),
    storageAt_sState_nil]
  decide

/-- The four bytes of the selector of `totalSupply()`. -/
def SEL_totalSupply : ByteArray := ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩

theorem size_SEL_totalSupply : SEL_totalSupply.size = 4 := by decide

/-- The call `totalSupply()` from `caller` to `C`. -/
abbrev mTS (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE SEL_totalSupply

/-- `totalSupply()` in the state where every slot is 0: the run (over the steps of EthLib's
`Logic.StepG`) ends with no error and returns the ether balance of the contract. -/
theorem totalSupply_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (mTS b t C caller) 0 [] .empty gas (sState C []) ss evm ∧
      Reaches (Logic.StepG fork) evm s ∧ s.running = false ∧ s.error = none ∧
      s.output = wordBytes (etherOf (sState C []) C) := by
  have hsz : (mTS b t C caller).data.size = 4 := size_SEL_totalSupply
  have hsl : selector (mTS b t C caller).data = selector SEL_totalSupply := rfl
  have hval : (mTS b t C caller).value = 0 := rfl
  have hspec := totalSupply_path (fork := fork) (message := mTS b t C caller)
    (state := sState C []) (substate := ss)
    hfork
    (by rw [hsz]; decide)
    (by rw [hsz]; decide)
    (by rw [hsl]; decide)
    (by rw [hval]; decide)
    (Nat.le_refl _)
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mTS b t C caller) (sState C []) ss _)
    (at_sFrame _ rfl _ _ _)
  obtain ⟨-, he, ho, -⟩ := hH
  exact ⟨_, _, s, at_sFrame _ rfl _ _ _, hr, hrun, by simpa using he, ho⟩

end WethVerify.Sanity

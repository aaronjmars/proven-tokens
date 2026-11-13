import QntVerify.Qnt.Sanity.Zero
import QntVerify.Qnt.Sep
import TokenKit.Evm.Readable

/-!
# Sanity: witnesses that need a state that is not all 0

Hand-written. The witnesses of Zero.lean run in the state where every slot is 0, so they move the
amount 0 and cannot reach `mint` (slot 3 would have to hold the caller) or the first success path
of `decreaseApproval` (the allowance would have to be below the subtracted value). Here:

* `transfer_moves`: transfer(to = 1, amount = 1) from a caller whose balance slot holds 5; every
  hypothesis of `transfer_p5` holds, with a real debit and credit.
* `mint_runs`: mint(to = 1, amount = 7) from the caller whose address word slot 3 holds; every
  hypothesis of `mint_p4` holds. So the success path of `mint` is not empty.
* `decreaseApproval_p2_runs`: decreaseApproval(spender = 1, 7) where the allowance slot holds 5;
  every hypothesis of `decreaseApproval_p2` (the allowance is set to 0) holds.

No fact about keccak is used: the mapping slots are the terms `kC caller`, `kA caller`, whatever
their numbers are.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace QntVerify.Sanity.Moves

open TokenKit
open UsdtVerify QntVerify QntVerify.Paths QntVerify.Sanity UsdtVerify.Gas
open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The mask of an address word. -/
abbrev MASK : U256 := 1461501637330902918203684832716283019655932542975

/-! ## transfer with a real amount -/

abbrev mT (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address) :
    Message fork :=
  sMsg b t C caller CODE (data2 SEL_transfer 1 1)

/-- The balance slot of the caller. -/
abbrev kC (caller : Address) : U256 :=
  mapSlot (bitwiseAnd MASK (bitwiseAnd MASK caller.toU256)) 0

abbrev sT (C caller : Address) : State.TransactionState := sState C [(kC caller, 5)]

abbrev gT (fork : Fork) : Nat :=
  3113 + 2100 + 2100 + writeMax fork + 2100 + writeMax fork + 2300 + 1

theorem noov1 (x : U256) (h : x.toNat ≤ 5) :
    isZero (isZero (isZero (lessThan (add x 1) x))) ≠ 0 := by
  refine Witness.noov _ _ ?_
  have h1 : (1 : U256).toNat = 1 := rfl
  rw [h1]
  omega

theorem transfer_moves (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (mT b t C caller) 0 [] .empty (gT fork) (sT C caller) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt (sT C caller) C (kC caller) = 5 := by
  have hdata : (mT b t C caller).data = data2 SEL_transfer 1 1 := rfl
  have hA1 : loadWord (mT b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_transfer _ _
  have hA2 : loadWord (mT b t C caller).data 36 32 = 1 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_transfer _ _
  have hval : (mT b t C caller).value = 0 := rfl
  have hacc : hasAccount (sT C caller) C := hasAccount_sState C _
  have h5 : storageAt (sT C caller) C (kC caller) = 5 := by
    simp only [storageAt_sState_cons, ↓reduceIte]
  have hle : ∀ n, (storageAt (sT C caller) C n).toNat ≤ 5 := by
    intro n
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split <;> decide
  have hspec := transfer_p5 (fork := fork) (message := mT b t C caller)
    (state := sT C caller) (substate := ss) hfork
    (by rw [hdata, size_data2 size_SEL_transfer]; decide)
    (by rw [hdata, size_data2 size_SEL_transfer]; decide)
    (by rw [hdata, selector_data2 size_SEL_transfer]; decide)
    rfl
    hacc
    (by rw [hval]; decide)
    (by rw [hA1]; decide)
    (by rw [hA2]; show isZero (isZero (isZero (greaterThan 1
          (storageAt (sT C caller) C (kC caller))))) ≠ 0; rw [h5]; decide)
    (by
      rw [hA2]
      refine noov1 _ (le_writeSlot (hasAccount_readSlot (hasAccount_readSlot hacc))
        (fun n => ?_) ?_ _)
      · simp only [storageAt_readSlot]; exact hle n
      · simp only [storageAt_readSlot]
        show (sub (storageAt (sT C caller) C (kC caller)) 1).toNat ≤ 5
        rw [h5]; decide)
    (gas := gT fork)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.le_refl 3113) (slotCost_le _)) (slotCost_le _)) (writeCost_le hfork _ _ _ _))
          (slotCost_le _)) (writeCost_le hfork _ _ _ _)) 2300)
      (Nat.lt_succ_self _))
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mT b t C caller) (sT C caller) ss (gT fork))
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1, h5⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-! ## mint from the crowdsale address -/

/-- The four bytes of the selector of `mint(address,uint256)`. -/
def SEL_mint : ByteArray := ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩

theorem size_SEL_mint : SEL_mint.size = 4 := by decide

/-- The call `mint(1, 7)` from `caller` to `C`. -/
abbrev mM (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address) :
    Message fork :=
  sMsg b t C caller CODE (data2 SEL_mint 1 7)

/-- The state where slot 3 (crowdsale) holds the address word of the caller, every other slot 0. -/
abbrev sM (C caller : Address) : State.TransactionState :=
  sState C [(3, bitwiseAnd MASK caller.toU256)]

abbrev gM (fork : Fork) : Nat := 2516 + 2100 + 2100 + writeMax fork + 2300 + 1

theorem noov7 (x : U256) (h : x.toNat < 2 ^ 160) :
    isZero (isZero (isZero (lessThan (add x 7) x))) ≠ 0 := by
  refine Witness.noov _ _ ?_
  have h1 : (7 : U256).toNat = 7 := rfl
  rw [h1]
  omega

/-- The success path of `mint` is not empty: the call `mint(1, 7)` from the address that slot 3
holds runs to the end with no error and no return data. -/
theorem mint_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (mM b t C caller) 0 [] .empty (gM fork) (sM C caller) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = ByteArray.empty ∧
      storageAt (sM C caller) C 3 = bitwiseAnd MASK caller.toU256 := by
  have hdata : (mM b t C caller).data = data2 SEL_mint 1 7 := rfl
  have hA1 : loadWord (mM b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_mint _ _
  have hA2 : loadWord (mM b t C caller).data 36 32 = 7 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_mint _ _
  have hval : (mM b t C caller).value = 0 := rfl
  have hacc : hasAccount (sM C caller) C := hasAccount_sState C _
  have h3 : storageAt (sM C caller) C 3 = bitwiseAnd MASK caller.toU256 := by
    simp only [storageAt_sState_cons, ↓reduceIte]
  have hlt : ∀ n, (storageAt (sM C caller) C n).toNat < 2 ^ 160 := by
    intro n
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split
    · exact mask_lt _
    · decide
  have hspec := mint_p4 (fork := fork) (message := mM b t C caller)
    (state := sM C caller) (substate := ss) hfork
    (by rw [hdata, size_data2 size_SEL_mint]; decide)
    (by rw [hdata, size_data2 size_SEL_mint]; decide)
    (by rw [hdata, selector_data2 size_SEL_mint]; decide)
    rfl
    hacc
    (by rw [hval]; decide)
    (by
      show isZero (isZero (equal (bitwiseAnd MASK caller.toU256) (bitwiseAnd MASK (bitwiseAnd MASK
        (div (storageAt (sM C caller) C 3) 1))))) ≠ 0
      rw [h3, Readable.div_one, mask_idem, mask_idem]
      exact Witness.eq2 _)
    (by
      rw [hA2]
      refine noov7 _ ?_
      simp only [storageAt_readSlot]
      exact hlt _)
    (gas := gM fork)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.le_refl 2516) (slotCost_le _)) (slotCost_le _)) (writeCost_le hfork _ _ _ _)) 2300)
      (Nat.lt_succ_self _))
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mM b t C caller) (sM C caller) ss (gM fork))
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1, h3⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

/-! ## decreaseApproval by more than the allowance -/

/-- The call `decreaseApproval(1, 7)` from `caller` to `C`. -/
abbrev mD (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address) :
    Message fork :=
  sMsg b t C caller CODE (data2 SEL_decreaseApproval 1 7)

/-- The allowance slot of the caller for the spender 1. -/
abbrev kA (caller : Address) : U256 :=
  mapSlot (bitwiseAnd MASK (bitwiseAnd MASK (bitwiseAnd MASK (1 : U256))))
    (mapSlot (bitwiseAnd MASK (bitwiseAnd MASK caller.toU256)) 2)

abbrev sD (C caller : Address) : State.TransactionState := sState C [(kA caller, 5)]

abbrev gD (fork : Fork) : Nat := 2860 + 2100 + writeMax fork + 2100 + 2300 + 1

/-- The first success path of `decreaseApproval` is not empty: with an allowance of 5, the call
`decreaseApproval(1, 7)` runs to the end with no error and returns the word 1. -/
theorem decreaseApproval_p2_runs (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (evm s : Evm fork Nat),
      At CODE (mD b t C caller) 0 [] .empty (gD fork) (sD C caller) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt (sD C caller) C (kA caller) = 5 := by
  have hdata : (mD b t C caller).data = data2 SEL_decreaseApproval 1 7 := rfl
  have hA1 : loadWord (mD b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data2 size_SEL_decreaseApproval _ _
  have hA2 : loadWord (mD b t C caller).data 36 32 = 7 := by
    rw [hdata]; exact Witness.arg2_data2 size_SEL_decreaseApproval _ _
  have hval : (mD b t C caller).value = 0 := rfl
  have hacc : hasAccount (sD C caller) C := hasAccount_sState C _
  have h5 : storageAt (sD C caller) C (kA caller) = 5 := by
    simp only [storageAt_sState_cons, ↓reduceIte]
  have hspec := decreaseApproval_p2 (fork := fork) (message := mD b t C caller)
    (state := sD C caller) (substate := ss) hfork
    (by rw [hdata, size_data2 size_SEL_decreaseApproval]; decide)
    (by rw [hdata, size_data2 size_SEL_decreaseApproval]; decide)
    (by rw [hdata, selector_data2 size_SEL_decreaseApproval]; decide)
    rfl
    hacc
    (by rw [hval]; decide)
    (by
      rw [hA1, hA2]
      show isZero (greaterThan 7 (storageAt (sD C caller) C (kA caller))) = 0
      rw [h5]; decide)
    (gas := gD fork)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.le_refl 2860) (slotCost_le _)) (writeCost_le hfork _ _ _ _)) (slotCost_le _)) 2300)
      (Nat.lt_succ_self _))
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mD b t C caller) (sD C caller) ss (gD fork))
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1, h5⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

end QntVerify.Sanity.Moves

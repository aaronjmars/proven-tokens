import ShibVerify.Shib.Sanity.Zero

/-!
# Sanity: a transfer that moves a token

Hand-written, after the witness of the audit (shib-audit/Witness2.lean). The call is
transfer(to = 1, amount = 1) from `caller`, in a state where the balance slot of the caller holds
5 and every other slot 0. Every hypothesis of `transfer_p7` holds and the run ends with no error,
with a real debit and credit (the witnesses of Zero.lean all move the amount 0). No fact about
keccak is used: the slot of the caller is the term `kC caller`, whatever its number is.
-/

set_option autoImplicit false

namespace ShibVerify.Sanity.Moves

open TokenKit
open UsdtVerify ShibVerify ShibVerify.Paths UsdtVerify.Gas
open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The selector of `transfer(address,uint256)`. -/
abbrev SEL_T : ByteArray := SEL_transfer

theorem size_SEL_T : SEL_T.size = 4 := size_SEL_transfer

abbrev mT (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address) :
    Message fork :=
  sMsg b t C caller CODE (data2 SEL_T 1 1)

abbrev kC (caller : Address) : U256 :=
  mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)) 0

abbrev sT (C caller : Address) : State.TransactionState := sState C [(kC caller, 5)]

abbrev gT (fork : Fork) : Nat :=
  3127 + 2100 + writeMax fork + 2100 + writeMax fork + 2300 + 1

theorem noov (x : U256) (h : x.toNat ≤ 5) :
    isZero (isZero (isZero (lessThan (add x 1) x))) ≠ 0 := by
  have e : lessThan (add x 1) x = 0 := by
    refine if_neg ?_
    have h1 : (1 : U256).toNat = 1 := rfl
    simp only [add, BitVec.toNat_add, h1]
    omega
  rw [e]; decide

theorem transfer_moves (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate)
    (hcal : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      caller.toU256 ≠ 0) :
    ∃ (evm s : Evm fork Nat),
      At CODE (mT b t C caller) 0 [] .empty (gT fork) (sT C caller) ss evm ∧
      Ends fork evm s ∧ s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt (sT C caller) C (kC caller) = 5 := by
  have hdata : (mT b t C caller).data = data2 SEL_T 1 1 := rfl
  have hA1 : loadWord (mT b t C caller).data 4 32 = 1 := by
    rw [hdata]
    have := loadWord_append_wordBytes_append SEL_T (wordBytes 1) 1
    rw [size_SEL_T] at this
    exact this
  have hA2 : loadWord (mT b t C caller).data 36 32 = 1 := by
    rw [hdata]
    exact wordArg_data2_1 size_SEL_T 1 1
  have hval : (mT b t C caller).value = 0 := rfl
  have hacc : hasAccount (sT C caller) C := hasAccount_sState C _
  have h5 : storageAt (sT C caller) C (kC caller) = 5 := by
    simp only [storageAt_sState_cons, ↓reduceIte]
  have hle : ∀ n, (storageAt (sT C caller) C n).toNat ≤ 5 := by
    intro n
    simp only [storageAt_sState_cons, storageAt_sState_nil]
    split <;> decide
  have hspec := transfer_p7 (fork := fork) (message := mT b t C caller)
    (state := sT C caller) (substate := ss) hfork
    (by rw [hdata, size_data2 size_SEL_T]; decide)
    (by rw [hdata, size_data2 size_SEL_T]; decide)
    (by rw [hdata, selector_data2 size_SEL_T]; decide)
    rfl
    hacc
    (by rw [hval]; decide)
    (by rw [hdata, size_data2 size_SEL_T]; decide)
    (Witness.ne3 _ hcal)
    (by rw [hA1]; decide)
    (by rw [hA2]; show isZero (isZero (isZero (greaterThan 1
          (storageAt (sT C caller) C (kC caller))))) ≠ 0; rw [h5]; decide)
    (by
      rw [hA2]
      refine noov _ (le_writeSlot (hasAccount_readSlot hacc) (fun n => ?_) ?_ _)
      · simp only [storageAt_readSlot]; exact hle n
      · show (sub (storageAt (sT C caller) C (kC caller)) 1).toNat ≤ 5
        rw [h5]; decide)
    (gas := gT fork)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl 3127)
          (slotCost_le _)) (writeCost_le hfork _ _ _ _)) (slotCost_le _))
          (writeCost_le hfork _ _ _ _)) 2300)
      (Nat.lt_succ_self _))
  obtain ⟨s, hr, hrun, hH⟩ := hspec (sFrame (mT b t C caller) (sT C caller) ss (gT fork))
    (at_sFrame _ rfl _ _ _)
  refine ⟨_, s, at_sFrame _ rfl _ _ _, Or.inl ⟨reaches_toStep hr, hrun⟩, ?_, hH.2.2.1, h5⟩
  obtain ⟨-, he, -⟩ := hH
  simpa using he

end ShibVerify.Sanity.Moves

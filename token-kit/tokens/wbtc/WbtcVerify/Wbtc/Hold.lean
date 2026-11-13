import WbtcVerify.Wbtc.Sep
import WbtcVerify.Wbtc.Code
import WbtcVerify.Wbtc.Reenter

/-!
# Closed facts and keccak hypotheses that the reentrancy theorems ask of WBTC

Written by hand (not generated).

Proved, no hypothesis:
- `storageOnly_inv`: the invariant `Inv L` (the sum of the balances is the word of slot 1) reads
  the storage words of `L` only.
- `code_not_delegated`: the code of WBTC (4,582 bytes) is no EIP-7702 delegation indicator (an
  indicator has 23 bytes).

Defined, NOT proved (hypotheses on keccak, in two strengths):
- `SepAll`: the GLOBAL form that LINK used: the separation of slots `Sep A` for EVERY list `A`
  of address words. As mathematics it is almost certainly false (2^160 balance slots and 2^320
  allowance slots in 2^256 words); it is kept only so that the old shape of the theorems can be
  stated as a corollary (`Any.lean`, `Seq.lean`). `SepAll.call` gives the hypothesis of one call.
- `SepMsg m`: the LOCAL form, `Sep (callKeys m)` for one message `m`, as upstream assumes it.
  The run-local theorems (`AnyLocal.lean`, `SeqLocal.lean`) ask it only of the messages that
  enter the code of WBTC during the run.

Not covered here: nothing is said about which lists `A` satisfy `Sep A`.
-/

namespace WbtcVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The sum of the balances depends on the storage words of `C` only. -/
theorem sumBal_congr {C : Address} {S S' : State.TransactionState}
    (h : ∀ k : U256, storageAt S' C k = storageAt S C k) :
    Supply.sumBal 0 C S' = Supply.sumBal 0 C S := by
  unfold Supply.sumBal
  exact Supply.sumTo_congr _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h])

/-- The invariant reads the storage words of `L` only. -/
theorem storageOnly_inv (L : Address) : Reenter.StorageOnly L (Inv L) := by
  intro S S' h hI
  have hk : ∀ k : U256, storageAt S' L k = storageAt S L k := fun k => h _
  unfold Inv Supply.Inv Supply.D at hI ⊢
  rw [sumBal_congr hk, hk]
  exact hI

/-- The code of WBTC is no EIP-7702 delegation indicator. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  have h : isValidDelegation CODE = false := by
    simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]
  simp [delegatedAddress, h]

/-- GLOBAL hypothesis on keccak (NOT proved, almost certainly false as mathematics): the
separation of slots for every list of address words. -/
def SepAll : Prop := ∀ A : List U256, (∀ x ∈ A, x.toNat < 2 ^ 160) → Sep A

/-- `SepAll` gives the hypothesis of each call. -/
theorem SepAll.call (K : SepAll) {fork : Fork} (message : Message fork) :
    Sep (callKeys message) := by
  refine K _ (fun x hx => ?_)
  simp only [callKeys, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact TokenKit.toNat_toU256_lt _
  · exact mask_lt _
  · exact mask_lt _

/-- LOCAL hypothesis on keccak (NOT proved) for one message: the separation of slots for the
three address words that the message can use as mapping keys. -/
def SepMsg {fork : Fork} (message : Message fork) : Prop := Sep (callKeys message)

/-- The global hypothesis gives the local one for every message. -/
theorem SepAll.msg (K : SepAll) {fork : Fork} (message : Message fork) : SepMsg message :=
  K.call message

end WbtcVerify

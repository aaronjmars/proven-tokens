import LinkVerify.Link.Sep
import LinkVerify.Link.Code
import LinkVerify.Link.Reenter

/-!
# Closed facts and keccak hypotheses that the reentrancy theorems ask of LINK

Written by hand (not generated).

Proved, no hypothesis:
- `storageOnly_inv`: the invariant `Inv L` reads the storage words of `L` only.
- `code_not_delegated`: the code of LINK (3,153 bytes) is no EIP-7702 delegation indicator
  (an indicator has 23 bytes).

Defined, NOT proved (hypotheses on keccak, in two strengths):
- `SepMsg m`: the LOCAL form, `Sep (callKeys m)` for one message `m` (three address words), as
  upstream assumes it. The run-local theorems (`AnyLocal.lean`, `SeqLocal.lean`) ask it only of
  the messages that really enter the code of LINK during the run at hand. These are the
  headline theorems.
- `SepAll`: the GLOBAL form: `Sep A` for EVERY list `A` of address words. As mathematics it is
  almost certainly false (2^160 balance slots and 2^320 allowance slots in 2^256 words; audit 4,
  LINK-1), so a theorem that assumes it is NOT a usable fact. It is kept only so that the old
  shape of the theorems can be stated as a corollary; every theorem that assumes it has `sepAll`
  in its name (`Any.lean`, `Seq.lean`). `SepAll.call` gives the hypothesis of one call.

Not covered here: nothing is said about which lists `A` satisfy `Sep A`.
-/

namespace LinkVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant reads the storage words of `L` only. -/
theorem storageOnly_inv (L : Address) : Reenter.StorageOnly L (Inv L) := by
  intro S S' h hI
  unfold Inv at hI ⊢
  rw [sumBal_congr (C := L) (S := S) (S' := S') (fun k => h _)]
  exact hI

/-- The code of LINK is no EIP-7702 delegation indicator. -/
theorem code_not_delegated : delegatedAddress CODE = none := by
  have h : isValidDelegation CODE = false := by
    simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]
  simp [delegatedAddress, h]

/-- GLOBAL hypothesis on keccak (NOT proved, almost certainly false as mathematics): the
separation of slots for every list of address words. The balance slot of an address is the
balance slot of no other address, and an allowance slot keyed by two addresses is no balance
slot, for all 2^160 address words at once. -/
def SepAll : Prop := ∀ A : List U256, (∀ x ∈ A, x.toNat < 2 ^ 160) → Sep A

/-- `SepAll` gives the hypothesis of each call. -/
theorem SepAll.call (K : SepAll) {fork : Fork} (message : Message fork) :
    Sep (callKeys message) := by
  refine K _ (fun x hx => ?_)
  simp only [callKeys, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> exact mask_lt _

/-- LOCAL hypothesis on keccak (NOT proved) for one message: the separation of slots for the
three address words that the message can use as mapping keys. -/
def SepMsg {fork : Fork} (message : Message fork) : Prop := Sep (callKeys message)

/-- The global hypothesis gives the local one for every message. -/
theorem SepAll.msg (K : SepAll) {fork : Fork} (message : Message fork) : SepMsg message :=
  K.call message

end LinkVerify

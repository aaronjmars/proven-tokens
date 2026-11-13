import SkyVerify.Sky.Readable

/-!
# The unchecked sums of SKY are exact under the supply invariant

The code of SKY adds to a balance and subtracts from `totalSupply` with no check (Solidity
`unchecked`). The readable corollaries (`Sky/Readable.lean`) state these results as 256-bit words.
Here: when the sum of all balances is `totalSupply` at the start (`Inv`), none of them wraps, so
the results are the exact sums of natural numbers. `hsep` is the hypothesis on keccak of
`Sky/Sep.lean` (assumed, not proved).

- `add_exact_move`: a transfer of `v` out of the balance of `x` (which holds at least `v`) into
  the balance of another address `y` does not wrap.
- `bal_le_tot`: one balance is at most `totalSupply`.
- `transfer_exact`, `transferFrom_exact`: after a successful `transfer` or `transferFrom` to an
  address other than the source, the balance of the receiver is the old one plus the amount.
- `mint_exact`: after a successful `mint`, the balance of the receiver is the old one plus the
  amount (and `totalSupply` is the old one plus the amount: `mint_readable`).
- `burn_exact`: a successful `burn` needs the amount to be at most `totalSupply`, and
  `totalSupply` is then the old one minus the amount.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace SkyVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Complete TokenKit.Readable
open SkyVerify SkyVerify.Paths SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Under the invariant, one balance is at most `totalSupply`. -/
theorem bal_le_tot {C : Address} {S : State.TransactionState} {x : U256}
    (hx : x.toNat < 2 ^ 160) (hinv : Inv C S) :
    (storageAt S C (mapSlot x 2)).toNat ≤ (storageAt S C 1).toNat := by
  have h := Supply.bal_le_D (b := 2) (t := 1) (C := C) (S := S) hx
  unfold Inv Supply.Inv at hinv
  omega

/-- Under the invariant, moving `v` out of the balance of `x` (which holds at least `v`) into the
balance of another address `y` does not wrap: the unchecked sum `v + balance[y]` is exact. -/
theorem add_exact_move {C : Address} {S : State.TransactionState} {A : List U256}
    (hsep : Sep A) {x y v : U256} (hx : x ∈ A) (hxl : x.toNat < 2 ^ 160)
    (hyl : y.toNat < 2 ^ 160) (hne : y ≠ x) (hacc : hasAccount S C) (hinv : Inv C S)
    (hv : v.toNat ≤ (storageAt S C (mapSlot x 2)).toNat) :
    (add v (storageAt S C (mapSlot y 2))).toNat =
      v.toNat + (storageAt S C (mapSlot y 2)).toNat := by
  have hslot : mapSlot y 2 ≠ mapSlot x 2 := fun e => hne (hsep.uniq x hx y hyl e)
  have hb : Supply.D 2 1 C (writeSlot S C (mapSlot x 2) (sub (storageAt S C (mapSlot x 2)) v)) +
      (storageAt (writeSlot S C (mapSlot x 2) (sub (storageAt S C (mapSlot x 2)) v)) C 1).toNat +
      v.toNat < 2 ^ 256 := by
    have htot := (storageAt S C 1).isLt
    have hs := Supply.sub_toNat_le hv
    unfold Inv Supply.Inv at hinv
    rw [D_bal hsep hx hxl hacc, tot_bal hsep hxl hacc]
    omega
  have h := add_bal (C := C) (x := y) (v := v) hyl hb
  rw [storageAt_writeSlot_of_ne hacc hslot] at h
  exact h

/-- transfer(to, value) to an address other than the caller, under the invariant: the balance of
`to` is the old one plus `value`, as natural numbers. -/
theorem transfer_exact (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (hsep : Sep (callKeys message))
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none)
    (hne : addrArg1 message ≠ callerW message) :
    (balance message s.state (addrArg1 message)).toNat =
      (balance message state (addrArg1 message)).toNat + (arg2 message).toNat := by
  obtain ⟨⟨-, -, -, -, hacc, -, -, hle⟩, -, hmove, -⟩ :=
    transfer_readable hfork hsize' hsel hsep start hrun hok
  rw [(hmove hne).2, Nat.add_comm]
  exact add_exact_move hsep (x := callerW message) (by simp [callKeys])
    (toNat_toU256_lt _) (mask_lt _) hne hacc hinv hle

/-- transferFrom(from, to, value) with `to` other than `from`, under the invariant: the balance
of `to` is the old one plus `value`, as natural numbers. -/
theorem transferFrom_exact (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (hsep : Sep (callKeys message))
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none)
    (hne : addrArg2 message ≠ addrArg1 message) :
    (balance message s.state (addrArg2 message)).toNat =
      (balance message state (addrArg2 message)).toNat + (arg3 message).toNat := by
  obtain ⟨⟨-, -, -, -, -, hacc, -, -, hle, -⟩, -, hmove, -⟩ :=
    transferFrom_readable hfork hsize' hsel hsep start hrun hok
  rw [(hmove hne).2, Nat.add_comm]
  exact add_exact_move hsep (x := addrArg1 message) (by simp [callKeys, addrArg1])
    (mask_lt _) (mask_lt _) hne hacc hinv hle

/-- mint(to, value) under the invariant: the balance of `to` is the old one plus `value`, as
natural numbers. -/
theorem mint_exact (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    (hsep : Sep (callKeys message))
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (balance message s.state (addrArg1 message)).toNat =
      (balance message state (addrArg1 message)).toNat + (arg2 message).toNat := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, hb⟩, -, hbal, -⟩ :=
    mint_readable hfork hsize' hsel hsep start hrun hok
  have hle := bal_le_tot (x := addrArg1 message) (mask_lt _) hinv
  have hv := (arg2 message).isLt
  rw [hbal]
  simp only [add, BitVec.toNat_add]
  simp only [balance, totalSupply] at hb ⊢
  omega

/-- burn(from, value) under the invariant: `value` is at most `totalSupply`, and `totalSupply`
is the old one minus `value`, as natural numbers. -/
theorem burn_exact (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x9dc29fac)
    (hsep : Sep (callKeys message))
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (arg2 message).toNat ≤ (totalSupply message state).toNat ∧
      (totalSupply message s.state).toNat =
        (totalSupply message state).toNat - (arg2 message).toNat := by
  obtain ⟨⟨-, -, -, -, -, hle, -⟩, -, -, htot, -⟩ :=
    burn_readable hfork hsize' hsel hsep start hrun hok
  have hb := bal_le_tot (x := addrArg1 message) (mask_lt _) hinv
  have hle' : (arg2 message).toNat ≤ (totalSupply message state).toNat :=
    Nat.le_trans hle hb
  exact ⟨hle', by rw [htot]; exact Supply.sub_toNat_le hle'⟩

end SkyVerify.Readable

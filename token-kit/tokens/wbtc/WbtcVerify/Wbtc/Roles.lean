import WbtcVerify.Wbtc.Readable
import WbtcVerify.Wbtc.Gen.Loops

/-!
# Who can do what in WBTC: the roles, in plain words

Every theorem is about a run of the deployed code `CODE` from pc 0, from Berlin on, that ends
with no error (or, where said, about the fact that such a run cannot end with no error). They
are corollaries of the readable theorems of Readable.lean, of the raw `ok_<fn>` theorems of
Gen/ and of `Loops.ro_name`, `Loops.ro_symbol`. Words: `sender` is the caller, `ownerOf`,
`pausedOf`, `mintingFinishedOf`, `decimalsOf` the four fields of slot 5, `pendingOwnerOf` the low
160 bits of slot 6, `totalSupply` the word of slot 1, `balance a` the word of `balances[a]`.

What it proves:

- `mint_only_owner`: a mint that succeeds comes from the owner, with `mintingFinished` 0. The
  pause is not checked (witness `Sanity.mint_paused_runs`).
- `burn_only_owner`: a burn that succeeds comes from the owner (it burns the caller's own
  tokens: see `totalSupply_change`). The pause is not checked (`Sanity.burn_paused_runs`).
- `pause_role`, `unpause_role`: only the owner pauses (when not paused) and unpauses (when
  paused); after it the byte of `paused` is 1, or 0.
- `paused_blocks`: while the token is paused, transfer, transferFrom, approve, increaseApproval
  and decreaseApproval never end with no error.
- `transferOwnership_role`, `claimOwnership_role`: ownership moves in two steps. Only the owner
  sets `pendingOwner` (the owner does not change, no log); only the pending owner claims, and
  then it is the owner and `pendingOwner` is 0.
- `renounceOwnership_fails`: renounceOwnership never ends with no error.
- `finishMinting_does_nothing`: finishMinting, from the owner, returns 0 (false), writes no
  slot and adds no log; `mintingFinished_fixed`: no call (but for reclaimToken, not covered
  here) changes the byte of `mintingFinished`. So minting can not be finished.
- `name_reads_only`, `symbol_reads_only`: name() and symbol() write no storage word of any
  account, change no account and add no log.
- `every_call`: what a call that succeeds can change, by cases: a mint, a burn, a pause, an
  unpause, a transferOwnership, a claimOwnership, a call that writes at most two balance slots
  and one allowance slot of its keys (only when not paused), or a call that writes no slot.
- `totalSupply_change`: only mint and burn change `totalSupply_`: a mint by the owner adds the
  amount to it and to the balance of the receiver; a burn by the owner takes the amount from it
  and from the balance of the caller; every other call keeps it.
- `slot5_change`, `owner_change`, `paused_change`, `decimals_fixed`, `mintingFinished_fixed`:
  slot 5 changes only by pause, unpause (the owner) and claimOwnership (the pending owner).
- `pendingOwner_change`: slot 6 changes only by transferOwnership (the owner) and
  claimOwnership (the pending owner).

What is assumed (hypotheses on keccak, local to each theorem, NOT proved):

- `Sep (callKeys message)` (Sep.lean) in `every_call`, `totalSupply_change` and the theorems
  after them: the balance and allowance slots of the keys of the call are not the same slot,
  are not slot 1, and no balance slot is slot 5 or 6.
- `AllowFixed (callKeys message)` (defined here) in `slot5_change` and the theorems after it:
  an allowance slot keyed by two keys of the call is neither slot 5 nor slot 6. `Sep` does not
  say it.
The other theorems take no hypothesis on keccak.

What is not covered: reclaimToken(address) (selector 0x17ffc320, it makes outside calls: the
theorems over every selector take `selector message.data ≠ 0x17ffc320`); what the code does
inside a call it makes (there is none outside reclaimToken); anything about several calls in a
row.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace WbtcVerify.Roles

open UsdtVerify
open TokenKit TokenKit.Complete TokenKit.Readable
open WbtcVerify WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas
open WbtcVerify.Readable

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- A hypothesis about keccak (NOT proved): an allowance slot keyed by two words of `A` is
neither slot 5 (decimals, owner, mintingFinished, paused) nor slot 6 (pendingOwner). -/
def AllowFixed (A : List U256) : Prop :=
  ∀ o ∈ A, ∀ sp ∈ A, mapSlot sp (mapSlot o 2) ≠ 5 ∧ mapSlot sp (mapSlot o 2) ≠ 6

theorem caller_key (m : Message fork) : sender m ∈ callKeys m := by
  simp [callKeys, sender]

theorem arg1_key (m : Message fork) : addrArg1 m ∈ callKeys m := by
  simp [callKeys, addrArg1]

theorem arg2_key (m : Message fork) : addrArg2 m ∈ callKeys m := by
  simp [callKeys, addrArg2]

/-! ## Who mints and who burns -/

/-- Who can mint: a mint(to, amount) that ends with no error comes from the owner, and
`mintingFinished` is 0. Nothing else about the caller or the state is checked: not the pause.
No hypothesis on keccak. -/
theorem mint_only_owner (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state ∧ mintingFinishedOf message state = 0 := by
  obtain ⟨-, hc2, hc3, -⟩ := ok_mint hfork hsize' hsel start hrun hok
  simp only [storageAt_readSlot] at hc3
  exact ⟨TokenKit.Readable.eq_of_equal hc2, TokenKit.Readable.value_of_cond hc3⟩

/-- Who can burn: a burn(value) that ends with no error comes from the owner. The pause is not
checked. No hypothesis on keccak. -/
theorem burn_only_owner (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x42966c68)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state :=
  TokenKit.Readable.eq_of_equal (ok_burn hfork hsize' hsel start hrun hok).2.1

/-! ## The pause -/

/-- Who can pause: a pause() that ends with no error comes from the owner, the token was not
paused, and after it the byte of `paused` is 1. -/
theorem pause_role (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8456cb59)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state ∧ pausedOf message state = 0 ∧
      pausedOf message s.state = 1 := by
  have r := Readable.pause_readable hfork hsize' hsel start hrun hok
  exact ⟨r.1.2.2.2.1, r.1.2.2.2.2, r.2.2.1⟩

/-- Who can unpause: an unpause() that ends with no error comes from the owner, the token was
paused, and after it the byte of `paused` is 0. -/
theorem unpause_role (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3f4ba83a)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state ∧ pausedOf message state ≠ 0 ∧
      pausedOf message s.state = 0 := by
  have r := Readable.unpause_readable hfork hsize' hsel start hrun hok
  exact ⟨r.1.2.2.2.1, r.1.2.2.2.2, r.2.2.1⟩

/-- What the pause blocks: while the byte of `paused` is not 0, a call of transfer,
transferFrom, approve, increaseApproval or decreaseApproval does not end with no error.
(mint and burn are not blocked: `Sanity.mint_paused_runs`, `Sanity.burn_paused_runs`.) -/
theorem paused_blocks (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb ∨ selector message.data = 0x23b872dd ∨
      selector message.data = 0x095ea7b3 ∨ selector message.data = 0xd73dd623 ∨
      selector message.data = 0x66188463)
    (hp : pausedOf message state ≠ 0)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) :
    s.error ≠ none := by
  intro hok
  apply hp
  rcases hsel with h | h | h | h | h
  · exact TokenKit.Readable.value_of_cond (ok_transfer hfork hsize' h start hrun hok).2.1
  · exact TokenKit.Readable.value_of_cond (ok_transferFrom hfork hsize' h start hrun hok).2.1
  · exact TokenKit.Readable.value_of_cond (ok_approve hfork hsize' h start hrun hok).2.1
  · exact TokenKit.Readable.value_of_cond (ok_increaseApproval hfork hsize' h start hrun hok).2.1
  · rcases ok_decreaseApproval hfork hsize' h start hrun hok with r | r
    · exact TokenKit.Readable.value_of_cond r.2.1
    · exact TokenKit.Readable.value_of_cond r.2.1

/-! ## Ownership -/

/-- Step one of a change of owner: a transferOwnership(newOwner) that ends with no error comes
from the owner; after it `pendingOwner` is `newOwner` (any address word, 0 included), the owner
is the same, and no log is added. -/
theorem transferOwnership_role (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf2fde38b)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state ∧
      pendingOwnerOf message s.state = addrArg1 message ∧
      ownerOf message s.state = ownerOf message state ∧
      s.substate.logs = substate.logs := by
  have r := Readable.transferOwnership_readable hfork hsize' hsel start hrun hok
  exact ⟨r.1.2.2.2, r.2.2.1, r.2.2.2.1, r.2.2.2.2.2.2⟩

/-- Step two of a change of owner: a claimOwnership() that ends with no error comes from the
pending owner; after it the caller is the owner and `pendingOwner` is 0. -/
theorem claimOwnership_role (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x4e71e0c8)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = pendingOwnerOf message state ∧
      ownerOf message s.state = sender message ∧
      pendingOwnerOf message s.state = 0 := by
  have r := Readable.claimOwnership_readable hfork hsize' hsel start hrun hok
  exact ⟨r.1.2.2.2, (r.2.2.1).trans (r.1.2.2.2).symm, r.2.2.2.1⟩

/-- renounceOwnership() does not end with no error, whoever calls it and whatever the state:
the owner can not give up ownership with it. -/
theorem renounceOwnership_fails (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x715018a6)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) :
    s.error ≠ none :=
  fun hok => ok_renounceOwnership hfork hsize' hsel start hrun hok

/-! ## finishMinting, name, symbol -/

/-- What finishMinting() does: a call that ends with no error comes from the owner, returns the
word 0 (false), changes no slot and adds no log. -/
theorem finishMinting_does_nothing (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x7d64bcb4)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    sender message = ownerOf message state ∧
      s.output = wordBytes (0 : U256) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      s.substate.logs = substate.logs := by
  have r := Readable.finishMinting_readable hfork hsize' hsel start hrun hok
  exact ⟨r.1.2, r.2.1, r.2.2.1, r.2.2.2⟩

/-- name() that ends with no error writes no storage word of any account, adds no log and
changes no account. -/
theorem name_reads_only (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x06fdde03)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ (c : Address) (k : U256), storageAt s.state c k = storageAt state c k) ∧
      s.substate.logs = substate.logs ∧
      (∀ a : Address, s.state.getAccount a = state.getAccount a) := by
  have r := Loops.ro_name hfork hsize' hsel start hrun hok
  exact ⟨r.storage, r.logs, r.accounts⟩

/-- symbol() that ends with no error writes no storage word of any account, adds no log and
changes no account. -/
theorem symbol_reads_only (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x95d89b41)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ (c : Address) (k : U256), storageAt s.state c k = storageAt state c k) ∧
      s.substate.logs = substate.logs ∧
      (∀ a : Address, s.state.getAccount a = state.getAccount a) := by
  have r := Loops.ro_symbol hfork hsize' hsel start hrun hok
  exact ⟨r.storage, r.logs, r.accounts⟩

/-! ## Every call, by cases -/

/-- What a call that ends with no error can change (any selector but reclaimToken's). One of:
a mint by the owner; a burn by the owner; a pause or an unpause by the owner; a
transferOwnership by the owner; a claimOwnership by the pending owner; a call made while not
paused that writes at most the balance slots of two address words and one allowance slot keyed
by keys of the call (transfer, transferFrom, approve, increaseApproval, decreaseApproval); a
call that writes no slot. `hsep` is the hypothesis on keccak (not proved). -/
theorem every_call (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (selector message.data = 0x40c10f19 ∧ sender message = ownerOf message state ∧
        mintingFinishedOf message state = 0 ∧
        (totalSupply message s.state).toNat =
          (totalSupply message state).toNat + (arg2 message).toNat ∧
        (balance message s.state (addrArg1 message)).toNat =
          (balance message state (addrArg1 message)).toNat + (arg2 message).toNat ∧
        (∀ k, k ≠ 1 → k ≠ mapSlot (addrArg1 message) 0 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (selector message.data = 0x42966c68 ∧ sender message = ownerOf message state ∧
        (arg1 message).toNat ≤ (balance message state (sender message)).toNat ∧
        (balance message s.state (sender message)).toNat =
          (balance message state (sender message)).toNat - (arg1 message).toNat ∧
        (totalSupply message s.state).toNat =
          (totalSupply message state).toNat - (arg1 message).toNat ∧
        (∀ k, k ≠ mapSlot (sender message) 0 → k ≠ 1 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (selector message.data = 0x8456cb59 ∧ sender message = ownerOf message state ∧
        pausedOf message state = 0 ∧ pausedOf message s.state = 1 ∧
        ownerOf message s.state = ownerOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state ∧
        (∀ k, k ≠ 5 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (selector message.data = 0x3f4ba83a ∧ sender message = ownerOf message state ∧
        pausedOf message state ≠ 0 ∧ pausedOf message s.state = 0 ∧
        ownerOf message s.state = ownerOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state ∧
        (∀ k, k ≠ 5 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (selector message.data = 0xf2fde38b ∧ sender message = ownerOf message state ∧
        pendingOwnerOf message s.state = addrArg1 message ∧
        (∀ k, k ≠ 6 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (selector message.data = 0x4e71e0c8 ∧ sender message = pendingOwnerOf message state ∧
        ownerOf message s.state = pendingOwnerOf message state ∧
        pendingOwnerOf message s.state = 0 ∧
        pausedOf message s.state = pausedOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state ∧
        (∀ k, k ≠ 5 → k ≠ 6 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k)) ∨
      (pausedOf message state = 0 ∧ ∃ a b o sp : U256, a.toNat < 2 ^ 160 ∧ b.toNat < 2 ^ 160 ∧
        o ∈ callKeys message ∧ sp ∈ callKeys message ∧
        ∀ k, k ≠ mapSlot a 0 → k ≠ mapSlot b 0 → k ≠ mapSlot sp (mapSlot o 2) →
          storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∨
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  obtain ⟨_, i, hi⟩ := ends_ok_dispatch hfork hsize' start hrun hok
  match i, hi with
  | ⟨0, _⟩, hi =>
    have h : selector message.data = 0x05d2035b := hi
    have r := Readable.mintingFinished_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨1, _⟩, hi =>
    have h : selector message.data = 0x06fdde03 := hi
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((fun k => (Loops.ro_name hfork hsize' h start hrun hok).storage _ k))))))))
  | ⟨2, _⟩, hi =>
    have h : selector message.data = 0x095ea7b3 := hi
    have r := Readable.approve_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r.1.2.2.2, sender message, sender message, sender message, addrArg1 message, toNat_toU256_lt _, toNat_toU256_lt _,
      caller_key message, arg1_key message, fun k _ _ h3 => r.2.2.2.1 k h3⟩))))))
  | ⟨3, _⟩, hi =>
    have h : selector message.data = 0x17ffc320 := hi
    exact absurd h hsel3
  | ⟨4, _⟩, hi =>
    have h : selector message.data = 0x18160ddd := hi
    have r := Readable.totalSupply_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨5, _⟩, hi =>
    have h : selector message.data = 0x23b872dd := hi
    have r := Readable.transferFrom_readable hfork hsize' h hsep start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r.1.2.2.2.1, addrArg1 message, addrArg2 message, addrArg1 message, sender message, mask_lt _, mask_lt _,
      arg1_key message, caller_key message, fun k h1 h2 h3 => r.2.2.2.2.2.1 k h1 h2 h3⟩))))))
  | ⟨6, _⟩, hi =>
    have h : selector message.data = 0x313ce567 := hi
    have r := Readable.decimals_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨7, _⟩, hi =>
    have h : selector message.data = 0x3f4ba83a := hi
    have r := Readable.unpause_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, r.1.2.2.2.1, r.1.2.2.2.2, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1⟩)))
  | ⟨8, _⟩, hi =>
    have h : selector message.data = 0x40c10f19 := hi
    have r := Readable.mint_readable hfork hsize' h hsep start hrun hok
    exact Or.inl ⟨h, r.1.2.2.2.1, r.1.2.2.2.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1⟩
  | ⟨9, _⟩, hi =>
    have h : selector message.data = 0x42966c68 := hi
    have r := Readable.burn_readable hfork hsize' h hsep start hrun hok
    exact Or.inr (Or.inl ⟨h, r.1.2.2.2.1, r.1.2.2.2.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1⟩)
  | ⟨10, _⟩, hi =>
    have h : selector message.data = 0x4e71e0c8 := hi
    have r := Readable.claimOwnership_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, r.1.2.2.2, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2.2.2.1⟩)))))
  | ⟨11, _⟩, hi =>
    have h : selector message.data = 0x5c975abb := hi
    have r := Readable.paused_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨12, _⟩, hi =>
    have h : selector message.data = 0x66188463 := hi
    have r := Readable.decreaseApproval_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r.1.2.2.2, sender message, sender message, sender message, addrArg1 message, toNat_toU256_lt _, toNat_toU256_lt _,
      caller_key message, arg1_key message, fun k _ _ h3 => r.2.2.2.2.1 k h3⟩))))))
  | ⟨13, _⟩, hi =>
    have h : selector message.data = 0x70a08231 := hi
    have r := Readable.balanceOf_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨14, _⟩, hi =>
    have h : selector message.data = 0x715018a6 := hi
    exact (ok_renounceOwnership hfork hsize' h start hrun hok).elim
  | ⟨15, _⟩, hi =>
    have h : selector message.data = 0x7d64bcb4 := hi
    have r := Readable.finishMinting_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨16, _⟩, hi =>
    have h : selector message.data = 0x8456cb59 := hi
    have r := Readable.pause_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inl ⟨h, r.1.2.2.2.1, r.1.2.2.2.2, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2.1, r.2.2.2.2.2.2.2.1⟩))
  | ⟨17, _⟩, hi =>
    have h : selector message.data = 0x8da5cb5b := hi
    have r := Readable.owner_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨18, _⟩, hi =>
    have h : selector message.data = 0x95d89b41 := hi
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((fun k => (Loops.ro_symbol hfork hsize' h start hrun hok).storage _ k))))))))
  | ⟨19, _⟩, hi =>
    have h : selector message.data = 0xa9059cbb := hi
    have r := Readable.transfer_readable hfork hsize' h hsep start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r.1.2.2.2.1, sender message, addrArg1 message, sender message, sender message, toNat_toU256_lt _, mask_lt _,
      caller_key message, caller_key message, fun k h1 h2 _ => r.2.2.2.2.1 k h1 h2⟩))))))
  | ⟨20, _⟩, hi =>
    have h : selector message.data = 0xd73dd623 := hi
    have r := Readable.increaseApproval_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r.1.2.2.2.1, sender message, sender message, sender message, addrArg1 message, toNat_toU256_lt _, toNat_toU256_lt _,
      caller_key message, arg1_key message, fun k _ _ h3 => r.2.2.2.1 k h3⟩))))))
  | ⟨21, _⟩, hi =>
    have h : selector message.data = 0xdd62ed3e := hi
    have r := Readable.allowance_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨22, _⟩, hi =>
    have h : selector message.data = 0xe30c3978 := hi
    have r := Readable.pendingOwner_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (r.2.2.1)))))))
  | ⟨23, _⟩, hi =>
    have h : selector message.data = 0xf2fde38b := hi
    have r := Readable.transferOwnership_readable hfork hsize' h start hrun hok
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, r.1.2.2.2, r.2.2.1, r.2.2.2.2.2.1⟩))))
  | ⟨n + 24, hn⟩, _ => exact absurd hn (by omega)

/-! ## The total supply -/

/-- Only mint and burn change `totalSupply_` (any selector but reclaimToken's). A call that ends
with no error is a mint by the owner with `mintingFinished` 0, and then `totalSupply_` and the
balance of the receiver each grow by the amount; or a burn by the owner, and then the balance
of the caller and `totalSupply_` each go down by the amount (at most the balance); or
`totalSupply_` is the same word after it. `hsep` is the hypothesis on keccak (not proved). -/
theorem totalSupply_change (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (selector message.data = 0x40c10f19 ∧ sender message = ownerOf message state ∧
        mintingFinishedOf message state = 0 ∧
        (totalSupply message s.state).toNat =
          (totalSupply message state).toNat + (arg2 message).toNat ∧
        (balance message s.state (addrArg1 message)).toNat =
          (balance message state (addrArg1 message)).toNat + (arg2 message).toNat) ∨
      (selector message.data = 0x42966c68 ∧ sender message = ownerOf message state ∧
        (arg1 message).toNat ≤ (balance message state (sender message)).toNat ∧
        (balance message s.state (sender message)).toNat =
          (balance message state (sender message)).toNat - (arg1 message).toNat ∧
        (totalSupply message s.state).toNat =
          (totalSupply message state).toNat - (arg1 message).toNat) ∨
      totalSupply message s.state = totalSupply message state := by
  rcases every_call hfork hsize' hsel3 hsep start hrun hok with
    ⟨h, ho, hm, ht, hb, -⟩ | ⟨h, ho, hl, hb, ht, -⟩ | ⟨-, -, -, -, -, -, -, hk⟩ |
    ⟨-, -, -, -, -, -, -, hk⟩ | ⟨-, -, -, hk⟩ | ⟨-, -, -, -, -, -, -, hk⟩ |
    ⟨-, a, b, o, sp, ha, hb, ho, hsp, hk⟩ | hk
  · exact Or.inl ⟨h, ho, hm, ht, hb⟩
  · exact Or.inr (Or.inl ⟨h, ho, hl, hb, ht⟩)
  · exact Or.inr (Or.inr (hk 1 (by decide)))
  · exact Or.inr (Or.inr (hk 1 (by decide)))
  · exact Or.inr (Or.inr (hk 1 (by decide)))
  · exact Or.inr (Or.inr (hk 1 (by decide) (by decide)))
  · exact Or.inr (Or.inr (hk 1 (hsep.total a ha) (hsep.total b hb)
      (fun e => (hsep.allow o ho sp hsp).2 e.symm)))
  · exact Or.inr (Or.inr (hk 1))

/-! ## Slot 5 (decimals, owner, mintingFinished, paused) and slot 6 (pendingOwner) -/

/-- Slot 5 changes only by pause, unpause and claimOwnership (any selector but reclaimToken's).
A call that ends with no error is a pause by the owner (then `paused` is 1), an unpause by the
owner (then `paused` is 0), both with the other fields kept, or a claimOwnership by the pending
owner (then the owner is the old pending owner, the other fields kept); or the word of slot 5 is
the same after it. `hsep` and `hfix` are the hypotheses on keccak (not proved). -/
theorem slot5_change (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (selector message.data = 0x8456cb59 ∧ sender message = ownerOf message state ∧
        pausedOf message state = 0 ∧ pausedOf message s.state = 1 ∧
        ownerOf message s.state = ownerOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state) ∨
      (selector message.data = 0x3f4ba83a ∧ sender message = ownerOf message state ∧
        pausedOf message state ≠ 0 ∧ pausedOf message s.state = 0 ∧
        ownerOf message s.state = ownerOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state) ∨
      (selector message.data = 0x4e71e0c8 ∧ sender message = pendingOwnerOf message state ∧
        ownerOf message s.state = pendingOwnerOf message state ∧
        pausedOf message s.state = pausedOf message state ∧
        mintingFinishedOf message s.state = mintingFinishedOf message state ∧
        decimalsOf message s.state = decimalsOf message state) ∨
      storageAt s.state message.currentTarget 5 = storageAt state message.currentTarget 5 := by
  rcases every_call hfork hsize' hsel3 hsep start hrun hok with
    ⟨-, -, -, -, -, hk⟩ | ⟨-, -, -, -, -, hk⟩ | ⟨h, a1, a2, a3, a4, a5, a6, -⟩ |
    ⟨h, a1, a2, a3, a4, a5, a6, -⟩ | ⟨-, -, -, hk⟩ | ⟨h, c1, c2, -, c4, c5, c6, -⟩ |
    ⟨-, a, b, o, sp, ha, hb, ho, hsp, hk⟩ | hk
  · exact Or.inr (Or.inr (Or.inr (hk 5 (by decide) (hsep.fixed.1 _ (mask_lt _)))))
  · exact Or.inr (Or.inr (Or.inr (hk 5 (hsep.fixed.1 _ (toNat_toU256_lt _)) (by decide))))
  · exact Or.inl ⟨h, a1, a2, a3, a4, a5, a6⟩
  · exact Or.inr (Or.inl ⟨h, a1, a2, a3, a4, a5, a6⟩)
  · exact Or.inr (Or.inr (Or.inr (hk 5 (by decide))))
  · exact Or.inr (Or.inr (Or.inl ⟨h, c1, c2, c4, c5, c6⟩))
  · exact Or.inr (Or.inr (Or.inr (hk 5 (hsep.fixed.1 a ha) (hsep.fixed.1 b hb)
      (fun e => (hfix o ho sp hsp).1 e.symm))))
  · exact Or.inr (Or.inr (Or.inr (hk 5)))

/-- The byte of `mintingFinished` never changes (any selector but reclaimToken's): after a call
that ends with no error it is what it was. With `finishMinting_does_nothing`: no function sets
it. `hsep` and `hfix` are the hypotheses on keccak (not proved). -/
theorem mintingFinished_fixed (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    mintingFinishedOf message s.state = mintingFinishedOf message state := by
  rcases slot5_change hfork hsize' hsel3 hsep hfix start hrun hok with
    ⟨-, -, -, -, -, hm, -⟩ | ⟨-, -, -, -, -, hm, -⟩ | ⟨-, -, -, -, hm, -⟩ | h5
  · exact hm
  · exact hm
  · exact hm
  · exact congrArg (fun w => bitwiseAnd (255 : U256) (div w (374144419156711147060143317175368453031918731001856 : U256))) h5

/-- `decimals` never changes (any selector but reclaimToken's). `hsep` and `hfix` are the
hypotheses on keccak (not proved). -/
theorem decimals_fixed (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    decimalsOf message s.state = decimalsOf message state := by
  rcases slot5_change hfork hsize' hsel3 hsep hfix start hrun hok with
    ⟨-, -, -, -, -, -, hd⟩ | ⟨-, -, -, -, -, -, hd⟩ | ⟨-, -, -, -, -, hd⟩ | h5
  · exact hd
  · exact hd
  · exact hd
  · exact congrArg (fun w => bitwiseAnd (255 : U256) w) h5

/-- The owner changes only by claimOwnership (any selector but reclaimToken's): after a call
that ends with no error the owner is the same, or the call is a claimOwnership from the pending
owner, who is the owner after it. `hsep` and `hfix` are the hypotheses on keccak (not proved). -/
theorem owner_change (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ownerOf message s.state = ownerOf message state ∨
      (selector message.data = 0x4e71e0c8 ∧ sender message = pendingOwnerOf message state ∧
        ownerOf message s.state = sender message) := by
  rcases slot5_change hfork hsize' hsel3 hsep hfix start hrun hok with
    ⟨-, -, -, -, ho, -, -⟩ | ⟨-, -, -, -, ho, -, -⟩ | ⟨h, c1, c2, -, -, -⟩ | h5
  · exact Or.inl ho
  · exact Or.inl ho
  · exact Or.inr ⟨h, c1, c2.trans c1.symm⟩
  · exact Or.inl (congrArg (fun w => bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div w (256 : U256))) h5)

/-- The pause changes only by pause and unpause, both from the owner (any selector but
reclaimToken's). `hsep` and `hfix` are the hypotheses on keccak (not proved). -/
theorem paused_change (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    pausedOf message s.state = pausedOf message state ∨
      (selector message.data = 0x8456cb59 ∧ sender message = ownerOf message state ∧
        pausedOf message state = 0 ∧ pausedOf message s.state = 1) ∨
      (selector message.data = 0x3f4ba83a ∧ sender message = ownerOf message state ∧
        pausedOf message state ≠ 0 ∧ pausedOf message s.state = 0) := by
  rcases slot5_change hfork hsize' hsel3 hsep hfix start hrun hok with
    ⟨h, a1, a2, a3, -⟩ | ⟨h, a1, a2, a3, -⟩ | ⟨-, -, -, hp, -, -⟩ | h5
  · exact Or.inr (Or.inl ⟨h, a1, a2, a3⟩)
  · exact Or.inr (Or.inr ⟨h, a1, a2, a3⟩)
  · exact Or.inl hp
  · exact Or.inl (congrArg (fun w => bitwiseAnd (255 : U256) (div w (95780971304118053647396689196894323976171195136475136 : U256))) h5)

/-- Slot 6 (`pendingOwner`) changes only by transferOwnership from the owner and by
claimOwnership from the pending owner (any selector but reclaimToken's). `hsep` and `hfix` are
the hypotheses on keccak (not proved). -/
theorem pendingOwner_change (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel3 : selector message.data ≠ 0x17ffc320)
    (hsep : Sep (callKeys message))
    (hfix : AllowFixed (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (selector message.data = 0xf2fde38b ∧ sender message = ownerOf message state ∧
        pendingOwnerOf message s.state = addrArg1 message) ∨
      (selector message.data = 0x4e71e0c8 ∧ sender message = pendingOwnerOf message state ∧
        pendingOwnerOf message s.state = 0) ∨
      storageAt s.state message.currentTarget 6 = storageAt state message.currentTarget 6 := by
  rcases every_call hfork hsize' hsel3 hsep start hrun hok with
    ⟨-, -, -, -, -, hk⟩ | ⟨-, -, -, -, -, hk⟩ | ⟨-, -, -, -, -, -, -, hk⟩ |
    ⟨-, -, -, -, -, -, -, hk⟩ | ⟨h, o1, o2, -⟩ | ⟨h, c1, -, c3, -, -, -, -⟩ |
    ⟨-, a, b, o, sp, ha, hb, ho, hsp, hk⟩ | hk
  · exact Or.inr (Or.inr (hk 6 (by decide) (hsep.fixed.2 _ (mask_lt _))))
  · exact Or.inr (Or.inr (hk 6 (hsep.fixed.2 _ (toNat_toU256_lt _)) (by decide)))
  · exact Or.inr (Or.inr (hk 6 (by decide)))
  · exact Or.inr (Or.inr (hk 6 (by decide)))
  · exact Or.inl ⟨h, o1, o2⟩
  · exact Or.inr (Or.inl ⟨h, c1, c3⟩)
  · exact Or.inr (Or.inr (hk 6 (hsep.fixed.2 a ha) (hsep.fixed.2 b hb)
      (fun e => (hfix o ho sp hsp).2 e.symm)))
  · exact Or.inr (Or.inr (hk 6))

end WbtcVerify.Roles

import OndoVerify.Ondo.SigSupply
import TokenKit.Evm.ReadableOpt

/-!
# What the writers of ONDO do, in the words of the contract

The generated completeness theorems (`Paths.ok_<fn>`) give the end state of each success path
as a term of reads and writes, and for the functions that move tokens or votes, up to the entry
of the next segment of code. This file reads the checks and the slots that can change out of
them, for the 12 functions that write storage.

- Who may call: `updateCliffTimestamp_readable` and `enableTransfer_readable` (the caller has
  `DEFAULT_ADMIN_ROLE`), `updateTrancheBalance_readable` (`TIMELOCK_UPDATE_ROLE`),
  `mint_readable` (`MINTER_ROLE`), `grantRole_readable` and `revokeRole_readable` (the admin
  role of the role), `renounceRole_readable` (the account is the caller),
  `transfer_readable` and `transferFrom_readable` (`transferAllowed` is set, or the caller has
  `TRANSFER_ROLE`).
- What can change: each theorem names the slots that the call can write; every other storage
  word of the contract is as before. For `delegate` the checkpoint slots of the old and the new
  delegate can change too (`CkSlot`).
- `mint_readable` also gives the only cap of `mint`: the amount and the new `totalSupply` fit
  `uint96`. There is no other cap and no waiting time in the bytecode.
- `mint_amounts`: the exact change of `mint`: `totalSupply` and the balance of the recipient
  both grow by the amount.
- `delegateBySig_readable` (EthLib's real runner): the recovered signer is not 0, the nonce of
  the call data is the stored nonce of the signer, and the time stamp is not after `expiry`.

Not here: the exact new balances of `transfer` and `transferFrom`, and the vesting rule they
check. They are in the generated theorems (`Paths.tt<i>_ends`, `Paths.vest<i>_ends`,
`Paths.core<i>_ends`), not restated in words.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace OndoVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open OndoVerify.Paths OndoVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- `keccak256("MINTER_ROLE")`. -/
abbrev MINTER_ROLE : U256 :=
  71998914331801701415977457805802827292338598818749192222732755537001613711014

/-- `keccak256("TRANSFER_ROLE")`. -/
abbrev TRANSFER_ROLE : U256 :=
  60161385426789692149059917683466708061875606619057841735915967165702158708588

/-- `keccak256("TIMELOCK_UPDATE_ROLE")`. -/
abbrev TIMELOCK_UPDATE_ROLE : U256 :=
  105792966476986369818188973763942834817227259111886716069005259966222125283040

/-- `DEFAULT_ADMIN_ROLE`. -/
abbrev DEFAULT_ADMIN_ROLE : U256 := 0

/-- `hasRole(role, account)` in the state `S` of the contract `C`: the low byte of the member
slot is not 0. -/
abbrev hasRoleOf (C : Address) (S : State.TransactionState) (role account : U256) : Prop :=
  bitwiseAnd (255 : U256) (storageAt S C (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) account) (mapSlot role 0))) ≠ 0

/-- `getRoleAdmin(role)`. -/
abbrev roleAdminOf (C : Address) (S : State.TransactionState) (role : U256) : U256 :=
  storageAt S C (add (1 : U256) (mapSlot role 0))

/-- The check of `_transferTokens` on the caller: `transferAllowed` (the low byte of slot 3) is
set, or the caller has `TRANSFER_ROLE`. -/
abbrev TransferGate (C : Address) (S : State.TransactionState) (caller : U256) : Prop :=
  bitwiseAnd (255 : U256) (storageAt S C 3) ≠ 0 ∨ hasRoleOf C S TRANSFER_ROLE caller

/-- Every storage word that the term of reads and writes leaves alone. -/
macro "frame_words" : tactic =>
  `(tactic| (simp (disch := first | assumption | supply_side) only
      [and_mask_comm, mask_idem, storageAt_readSlot, storageAt_writeSlot_of_ne]))

/-- `updateCliffTimestamp(newTimestamp)`: the caller has `DEFAULT_ADMIN_ROLE`; after the call
`cliffTimestamp` (slot 1) is the argument, and no other slot has changed. -/
theorem updateCliffTimestamp_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x04c981ba)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state DEFAULT_ADMIN_ROLE message.caller.toU256 ∧
    storageAt s.state message.currentTarget 1 = (loadWord message.data 4 32) ∧
    (∀ k : U256, k ≠ 1 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  obtain ⟨hc1, hc2, hc3, hstat, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_updateCliffTimestamp hfork hsize' hsel start hrun hok
  rw [hst]
  refine ⟨by simpa only [storageAt_readSlot] using hc3, ?_, ?_⟩
  · rw [storageAt_writeSlot_self (by supply_side)]
  · intro k hk
    frame_words

/-- `enableTransfer()`: the caller has `DEFAULT_ADMIN_ROLE`; only `transferAllowed` (slot 3)
can change. -/
theorem enableTransfer_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xf1b50c1d)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state DEFAULT_ADMIN_ROLE message.caller.toU256 ∧
    (∀ k : U256, k ≠ 3 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  obtain ⟨hc1, hc2, hstat, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_enableTransfer hfork hsize' hsel start hrun hok
  rw [hst]
  refine ⟨by simpa only [storageAt_readSlot] using hc2, ?_⟩
  intro k hk
  frame_words

/-- `approve(spender, rawAmount)`: only `allowances[caller][spender]` can change. -/
theorem approve_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) (mapSlot message.caller.toU256 5) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  rcases ok_approve hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hstat, hacc, hgas, hout, hg, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hstat, hacc, hgas, hout, hg, hst, hsub⟩
  all_goals
    rw [hst]
    intro k hk
    frame_words

/-- `updateTrancheBalance(investor, amount, tranche)`: the caller has `TIMELOCK_UPDATE_ROLE`;
only `investorBalances[investor]` can change. -/
theorem updateTrancheBalance_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xe17ddf87)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state TIMELOCK_UPDATE_ROLE message.caller.toU256 ∧
    (∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 2 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hstat, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_updateTrancheBalance hfork hsize' hsel start hrun hok
  rw [hst]
  refine ⟨by simpa only [storageAt_readSlot] using hc5, ?_⟩
  intro k hk
  frame_words

/-- `grantRole(role, account)`: the caller has the admin role of `role`; only the member slot of
`account` for `role` can change. -/
theorem grantRole_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2f2ff15d)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state (roleAdminOf message.currentTarget state (loadWord message.data 4 32)) message.caller.toU256 ∧
    (∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)) (mapSlot (loadWord message.data 4 32) 0) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  rcases ok_grantRole hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hstat, hacc, hgas, hout, hg, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hgas, hout, hg, hst, hsub⟩
  all_goals
    rw [hst]
    refine ⟨by simpa only [storageAt_readSlot] using hc4, ?_⟩
    intro k hk
    frame_words

/-- `revokeRole(role, account)`: the caller has the admin role of `role`; only the member slot
of `account` for `role` can change. -/
theorem revokeRole_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xd547741f)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state (roleAdminOf message.currentTarget state (loadWord message.data 4 32)) message.caller.toU256 ∧
    (∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)) (mapSlot (loadWord message.data 4 32) 0) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  rcases ok_revokeRole hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hstat, hacc, hgas, hout, hg, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hgas, hout, hg, hst, hsub⟩
  all_goals
    rw [hst]
    refine ⟨by simpa only [storageAt_readSlot] using hc4, ?_⟩
    intro k hk
    frame_words

/-- `renounceRole(role, account)`: the account is the caller; only the member slot of the
account for `role` can change. -/
theorem renounceRole_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x36568abe)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.caller.toU256 = bitwiseAnd (loadWord message.data 36 32) (1461501637330902918203684832716283019655932542975 : U256) ∧
    (∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)) (mapSlot (loadWord message.data 4 32) 0) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  rcases ok_renounceRole hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hstat, hacc, hgas, hout, hg, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hgas, hout, hg, hst, hsub⟩
  all_goals
    rw [hst]
    refine ⟨Readable.eq_of_equal hc4, ?_⟩
    intro k hk
    frame_words

/-- `mint(dst, rawAmount)`: the caller has `MINTER_ROLE`, the recipient is not 0, the amount and
the old `totalSupply` are below `2^96`, and their sum fits `uint96` (the only cap). Only
`totalSupply` (slot 4) and `balances[dst]` can change. -/
theorem mint_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    hasRoleOf message.currentTarget state MINTER_ROLE message.caller.toU256 ∧
    bitwiseAnd (loadWord message.data 4 32) (1461501637330902918203684832716283019655932542975 : U256) ≠ 0 ∧
    (loadWord message.data 36 32).toNat < 2 ^ 96 ∧
    (storageAt state message.currentTarget 4).toNat < 2 ^ 96 ∧
    (storageAt state message.currentTarget 4).toNat + (loadWord message.data 36 32).toNat < 2 ^ 96 ∧
    (∀ k : U256, k ≠ 4 → k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 6 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hstat, hacc, hgas, hout, hg, hst,
    hsub⟩ := ok_mint hfork hsize' hsel start hrun hok
  rw [hst]
  have h6 : (loadWord message.data 36 32).toNat < 2 ^ 96 := by word_omega hc6
  have h7 : (storageAt state message.currentTarget 4).toNat < 2 ^ 96 := by word_omega hc7
  refine ⟨by simpa only [storageAt_readSlot] using hc4, hc5, h6, h7, ?_, ?_⟩
  · clear hst hsub hg hgas hout hc9
    word_omega hc8 h6 h7
  · intro k hk hk'
    frame_words

/-- `mint(dst, rawAmount)`, the exact change: `totalSupply` (slot 4) grows by the amount, and the
low 96 bits of `balances[dst]` grow by the amount. The hypothesis `hne` is one keccak fact: the
balance slot of `dst` is not slot 4. -/
theorem mint_amounts (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    (hne : mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 6 ≠ 4)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (storageAt s.state message.currentTarget 4).toNat =
      (storageAt state message.currentTarget 4).toNat + (loadWord message.data 36 32).toNat ∧
    (bitwiseAnd (79228162514264337593543950335 : U256) (storageAt s.state message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 6))).toNat =
      (bitwiseAnd (79228162514264337593543950335 : U256) (storageAt state message.currentTarget
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 6))).toNat +
        (loadWord message.data 36 32).toNat := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hstat, hacc, hgas, hout, hg, hst,
    hsub⟩ := ok_mint hfork hsize' hsel start hrun hok
  rw [hst]
  clear hst hsub hg hgas hout
  have h6 : (loadWord message.data 36 32).toNat < 2 ^ 96 := by word_omega hc6
  have h7 : (storageAt state message.currentTarget 4).toNat < 2 ^ 96 := by word_omega hc7
  have h8 : (storageAt state message.currentTarget 4).toNat +
      (loadWord message.data 36 32).toNat < 2 ^ 96 := by word_omega hc8 h6 h7
  have hne' := Ne.symm hne
  simp (disch := first | assumption | supply_side) only [and_mask_comm, and_m96_comm, m96_idem,
    m96_or, storageAt_readSlot, storageAt_writeSlot_of_ne, storageAt_writeSlot_self] at hc9 ⊢
  constructor
  · word_omega h6 h7 h8
  · word_omega hc9 h6 h7 h8

/-- The check on the caller, read out of the code of the transfer (`tt0`, the entry of
`transfer`). -/
theorem tt0_gate {S : State.TransactionState} {sub : Substate} {gas : Nat} {s : Evm fork Nat}
    {a0 a1 a2 a3 : U256} {mem : ByteArray}
    (hch : tt0_ends fork message S sub gas s a0 a1 a2 a3 mem) :
    TransferGate message.currentTarget S message.caller.toU256 := by
  unfold tt0_ends at hch
  rcases hch with ⟨h1, h2, -⟩ | ⟨h1, -⟩
  · exact Or.inr (by simpa only [storageAt_readSlot] using h2)
  · exact Or.inl h1

/-- The same for `tt1` (the entry of `transferFrom` after a write of the allowance). -/
theorem tt1_gate {S : State.TransactionState} {sub : Substate} {gas : Nat} {s : Evm fork Nat}
    {a0 a1 a2 a3 a4 a5 : U256} {mem : ByteArray}
    (hch : tt1_ends fork message S sub gas s a0 a1 a2 a3 a4 a5 mem) :
    TransferGate message.currentTarget S message.caller.toU256 := by
  unfold tt1_ends at hch
  rcases hch with ⟨h1, h2, -⟩ | ⟨h1, -⟩
  · exact Or.inr (by simpa only [storageAt_readSlot] using h2)
  · exact Or.inl h1

/-- The same for `tt2` (the entry of `transferFrom` with no write of the allowance). -/
theorem tt2_gate {S : State.TransactionState} {sub : Substate} {gas : Nat} {s : Evm fork Nat}
    {a0 a1 a2 a3 a4 a5 : U256} {mem : ByteArray}
    (hch : tt2_ends fork message S sub gas s a0 a1 a2 a3 a4 a5 mem) :
    TransferGate message.currentTarget S message.caller.toU256 := by
  unfold tt2_ends at hch
  rcases hch with ⟨h1, h2, -⟩ | ⟨h1, -⟩
  · exact Or.inr (by simpa only [storageAt_readSlot] using h2)
  · exact Or.inl h1

/-- Names the start state of a `tt1` segment in a statement about its storage words. -/
theorem tt1_start_words {S : State.TransactionState} {sub : Substate} {gas : Nat}
    {s : Evm fork Nat} {a0 a1 a2 a3 a4 a5 : U256} {mem : ByteArray}
    (_ : tt1_ends fork message S sub gas s a0 a1 a2 a3 a4 a5 mem) {S0 : State.TransactionState}
    (k : U256) (h : storageAt S message.currentTarget k = storageAt S0 message.currentTarget k) :
    storageAt S message.currentTarget k = storageAt S0 message.currentTarget k := h

/-- Names the start state of a `tt2` segment in a statement about its storage words. -/
theorem tt2_start_words {S : State.TransactionState} {sub : Substate} {gas : Nat}
    {s : Evm fork Nat} {a0 a1 a2 a3 a4 a5 : U256} {mem : ByteArray}
    (_ : tt2_ends fork message S sub gas s a0 a1 a2 a3 a4 a5 mem) {S0 : State.TransactionState}
    (k : U256) (h : storageAt S message.currentTarget k = storageAt S0 message.currentTarget k) :
    storageAt S message.currentTarget k = storageAt S0 message.currentTarget k := h

/-- `transfer(dst, rawAmount)`: the amount is below `2^96`, and `transferAllowed` is set or the
caller has `TRANSFER_ROLE`. -/
theorem transfer_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (loadWord message.data 36 32).toNat < 2 ^ 96 ∧ TransferGate message.currentTarget state message.caller.toU256 := by
  obtain ⟨hc1, hc2, hc3, hc4, hgas, hch⟩ := ok_transfer hfork hsize' hsel start hrun hok
  exact ⟨by word_omega hc4, tt0_gate hch⟩

/-- `transferFrom(src, dst, rawAmount)`: the amount is below `2^96`, and in the state `S1` in
which the code of the transfer starts, `transferAllowed` is set or the caller has
`TRANSFER_ROLE`. `S1` is the start state but for `allowances[src][caller]`. -/
theorem transferFrom_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (loadWord message.data 68 32).toNat < 2 ^ 96 ∧
    ∃ S1 : State.TransactionState,
      (∀ k : U256, k ≠ mapSlot message.caller.toU256 (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5) →
        storageAt S1 message.currentTarget k = storageAt state message.currentTarget k) ∧
      TransferGate message.currentTarget S1 message.caller.toU256 := by
  rcases ok_transferFrom hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hstat, hacc, hgas, hch⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hgas, hch⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hgas, hch⟩
  · refine ⟨by word_omega hc5, ?_⟩
    have hfr : ∀ k : U256, k ≠ mapSlot message.caller.toU256 (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5) →
        storageAt _ message.currentTarget k = storageAt state message.currentTarget k :=
      fun k hk => (tt1_start_words hch k (by
        have hk' : k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 5) := by
          rw [mask_toU256']; exact hk
        frame_words))
    exact ⟨_, hfr, tt1_gate hch⟩
  all_goals
    refine ⟨by word_omega hc5, ?_⟩
    exact ⟨_, fun k hk => tt2_start_words hch k (by frame_words), tt2_gate hch⟩

/-- `delegate(delegatee)`: only `delegates[caller]` and the checkpoint slots of the old and the
new delegate (the words of `D`) can change. -/
theorem delegate_readable {D : List U256} (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x5c19a95c)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ D →
    delegOf message.currentTarget state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) ∈ D →
    ∀ k : U256, ¬ CkSlot D k → k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) 7 →
      storageAt s.state message.currentTarget k = storageAt state message.currentTarget k := by
  obtain ⟨hc1, hc2, hc3, hstat, hacc, hgas, hch⟩ :=
    ok_delegate hfork hsize' hsel start hrun hok
  intro hk1 hk2 k hk hk7
  rw [mvSrc0_frame hch (by key_mem)
    (by
      have h' := hk2
      simp only [delegOf, and_mask_comm, mask_idem, mask_toU256', storageAt_readSlot] at h' ⊢
      exact h') k hk]
  frame_words

/-- `delegateBySig(delegatee, nonce, expiry, v, r, s)` under EthLib's real runner: the signer
that ECRECOVER returned is not 0, the nonce of the call data is the stored nonce of the signer,
and the time stamp of the block is not after `expiry`. -/
theorem delegateBySig_readable (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc3cda520)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    sigSigner message ≠ 0 ∧
    (loadWord message.data 36 32) = storageAt state message.currentTarget (mapSlot (sigSigner message) 10) ∧
    message.blockEnv.timestamp.toNat ≤ (loadWord message.data 68 32).toNat := by
  obtain ⟨-, -, -, -, -, -, hend⟩ :=
    ok_delegateBySig_real hparis hglam hsize' hsel hdel start within hrun hok
  unfold delegateBySigTail_ends at hend
  obtain ⟨h1, h2, h3, h4, -⟩ := hend
  have e3 := Readable.eq_of_equal h3
  simp only [and_mask_comm] at h1 e3
  refine ⟨h1, e3, ?_⟩
  clear h1 h2 h3 e3
  word_omega h4

end OndoVerify

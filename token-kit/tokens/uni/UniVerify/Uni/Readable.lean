import UniVerify.Uni.Invariant
import TokenKit.Evm.ReadableOpt

/-!
# What the writers of UNI do, in the words of the contract

The generated completeness theorems (`Paths.ok_<fn>`) give the end state of each success path
as a term of reads and writes, and for the functions that move votes, up to the entry of
`_moveDelegates` (the rest is the generated `Paths.mvSrc<i>_ends`). This file reads single
storage words out of them.

- `mint_readable`: who (the caller is `minter`), wait (the time stamp is not before
  `mintingAllowedAfter`), cap (the amount is below `2^96` and at most 2 percent of
  `totalSupply`, rounded down), and the exact change: `totalSupply` and the balance of the
  recipient grow by the amount, and `mintingAllowedAfter` becomes the time stamp plus 365 days.
- `setMinter_readable`: the caller is `minter`; `minter` becomes the argument; no other slot
  changes.
- `approve_readable`: `allowances[caller][spender]` becomes the amount (the largest `uint96`
  for the largest word); no other slot changes.
- `transfer_readable`: the amount is at most the balance of the caller; the balance of the
  caller falls and the balance of the recipient grows by the amount (both unchanged when they
  are the same address).

The functions that move votes (`mint`, `transfer`) write checkpoints after the balances. The
storage words read here are no checkpoint slots: `mvSrc<i>_frame` (Frame.lean) carries them
to the end state. For slot 2 (`mintingAllowedAfter`) that needs one more fact about keccak,
`hck2 : ¬ CkSlot (ckKeys message state) 2`, a hypothesis of `mint_readable` (assumed, not
proved): slot 2 is no checkpoint slot of the keys of the call and their delegates.

Not here: `transferFrom`, `delegate`, `delegateBySig`, `permit`. Their exact writes are in the
generated theorems (`Paths.ok_transferFrom`, `Paths.ok_delegate`, `ok_delegateBySig_real`,
`ok_permit_real`), not restated in words.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace UniVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open UniVerify.Paths UniVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- `balances[a]` (a `uint96`) in the state `S` of the contract `C`. -/
abbrev balanceOf (C : Address) (S : State.TransactionState) (a : U256) : U256 :=
  bitwiseAnd (79228162514264337593543950335 : U256) (storageAt S C (mapSlot a 4))

/-- `allowances[o][sp]` (a `uint96`). -/
abbrev allowanceOf (C : Address) (S : State.TransactionState) (o sp : U256) : U256 :=
  bitwiseAnd (79228162514264337593543950335 : U256) (storageAt S C (mapSlot sp (mapSlot o 3)))

/-- `minter` (the low 160 bits of slot 1). -/
abbrev minterOf (C : Address) (S : State.TransactionState) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (storageAt S C 1)

theorem toNat_div100 (w : U256) : (div w (100 : U256)).toNat = w.toNat / 100 := by
  unfold div
  rw [if_neg (by decide)]
  have h : (100 : U256).toNat = 100 := by decide
  rw [BitVec.toNat_ofNat, h]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt)

theorem toNat_mul2 {w : U256} (h : w.toNat < 2 ^ 96) :
    (mul (2 : U256) w).toNat = 2 * w.toNat := by
  unfold mul
  rw [BitVec.toNat_mul]
  have h2 : (2 : U256).toNat = 2 := by decide
  rw [h2]
  exact Nat.mod_eq_of_lt (by omega)

theorem high96_eq_not_mask :
    (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) =
      ~~~(1461501637330902918203684832716283019655932542975 : U256) := by
  decide

/-- The low 160 bits of "160 bits of `x`, and the 96 high bits of `y`" are those of `x`. -/
theorem mask_or (x y : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseOr (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) x)
          (bitwiseAnd (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) y)) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) x := by
  unfold bitwiseAnd bitwiseOr
  rw [high96_eq_not_mask]
  exact and_or_not256 _ _ _

/-- The low 96 bits of "all 96 bits set, and the 160 high bits of `y`" are all set. -/
theorem m96_or_max (y : U256) :
    bitwiseAnd (79228162514264337593543950335 : U256)
        (bitwiseOr (79228162514264337593543950335 : U256)
          (bitwiseAnd (115792089237316195423570985008687907853269984665561335876943319670319585689600 : U256) y)) =
      (79228162514264337593543950335 : U256) := by
  have h := m96_or (79228162514264337593543950335 : U256) y
  have e : bitwiseAnd (79228162514264337593543950335 : U256)
      (79228162514264337593543950335 : U256) = (79228162514264337593543950335 : U256) := by
    decide
  rw [e] at h
  exact h

/-- `setMinter(minter_)`: a call that ends with no error came from `minter`; after it `minter`
is the argument, and no other slot has changed. -/
theorem setMinter_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xfca3b5aa)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.caller.toU256 = minterOf message.currentTarget state ∧
    minterOf message.currentTarget s.state = (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) ∧
    ∀ k : U256, k ≠ 1 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k := by
  obtain ⟨hc1, hc2, hc3, hc4, hstat, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_setMinter hfork hsize' hsel start hrun hok
  have e4 := Readable.eq_of_equal hc4
  unfold minterOf
  rw [hst]
  refine ⟨e4, ?_, ?_⟩
  · rw [storageAt_writeSlot_self (by supply_side)]
    simp only [storageAt_readSlot]
    exact mask_or _ _
  · intro k hk
    rw [storageAt_writeSlot_of_ne (by supply_side) hk]
    first
      | done
      | simp only [storageAt_readSlot]

/-- `approve(spender, rawAmount)`: after a call that ends with no error,
`allowances[caller][spender]` is the largest `uint96` when the amount is the largest word, and
else the amount, which is below `2^96`. No other slot has changed. -/
theorem approve_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    (((loadWord message.data 36 32) = (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) ∧
        allowanceOf message.currentTarget s.state message.caller.toU256 (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) = (79228162514264337593543950335 : U256)) ∨
      ((loadWord message.data 36 32).toNat < 2 ^ 96 ∧
        allowanceOf message.currentTarget s.state message.caller.toU256 (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) = (loadWord message.data 36 32))) ∧
    ∀ k : U256, k ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) (mapSlot message.caller.toU256 3) →
      storageAt s.state message.currentTarget k = storageAt state message.currentTarget k := by
  unfold allowanceOf
  rcases ok_approve hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hstat, hacc, hgas, hout, hg, hst, hsub⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hstat, hacc, hgas, hout, hg, hst, hsub⟩
  · rw [hst]
    have e := Readable.eq_of_isZero_equal hc4
    simp only [and_mask_comm, and_m96_comm, storageAt_readSlot]
    refine ⟨Or.inl ⟨e, ?_⟩, ?_⟩
    · rw [storageAt_writeSlot_self (by supply_side)]
      exact m96_or_max _
    · intro k hk
      rw [storageAt_writeSlot_of_ne (by supply_side) hk]
      first
        | done
        | simp only [storageAt_readSlot]
  · rw [hst]
    have f5 := lt_of_cond hc5
    simp only [toNat_2p96] at f5
    simp only [and_mask_comm, and_m96_comm, storageAt_readSlot]
    refine ⟨Or.inr ⟨f5, ?_⟩, ?_⟩
    · rw [storageAt_writeSlot_self (by supply_side), m96_or, m96_small f5]
    · intro k hk
      rw [storageAt_writeSlot_of_ne (by supply_side) hk]
      first
        | done
        | simp only [storageAt_readSlot]

/-- `mint(dst, rawAmount)`: a call that ends with no error came from `minter`, at a time stamp
not before `mintingAllowedAfter`, for a recipient that is not the zero address and an amount
below `2^96` that is at most 2 percent of `totalSupply` (rounded down). After it `totalSupply`
is the old one plus the amount, `mintingAllowedAfter` is the time stamp plus 31536000 seconds,
and the balance of the recipient is the old one plus the amount.

`hsep` and `hck2` (slot 2 is no checkpoint slot) are facts about keccak, assumed. -/
theorem mint_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    (hsep : Sep (callKeys message) (ckKeys message state))
    (hck2 : ¬ CkSlot (ckKeys message state) 2)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.caller.toU256 = minterOf message.currentTarget state ∧
    (storageAt state message.currentTarget 2).toNat ≤ message.blockEnv.timestamp.toNat ∧
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) ≠ 0 ∧
    (loadWord message.data 36 32).toNat < 2 ^ 96 ∧
    (loadWord message.data 36 32).toNat ≤ 2 * (storageAt state message.currentTarget 0).toNat / 100 ∧
    (storageAt s.state message.currentTarget 0).toNat = (storageAt state message.currentTarget 0).toNat + (loadWord message.data 36 32).toNat ∧
    storageAt s.state message.currentTarget 2 = add (31536000 : U256) message.blockEnv.timestamp ∧
    (balanceOf message.currentTarget s.state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32))).toNat =
      (balanceOf message.currentTarget state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32))).toNat + (loadWord message.data 36 32).toNat := by
  have hlt := mask_lt (loadWord message.data 4 32)
  have n0b := hsep.total _ hlt
  have n2b := hsep.fixed.2 _ hlt
  have nb0 := Ne.symm n0b
  have nb2 := Ne.symm n2b
  have n02 : (0 : U256) ≠ 2 := by decide
  have n20 : (2 : U256) ≠ 0 := by decide
  unfold minterOf balanceOf
  rcases ok_mint hfork hsize' hsel start hrun hok with
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hstat, hacc, hgas, hch⟩ |
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hstat, hacc, hgas, hch⟩
  · have hm1 : message.caller.toU256 ∈ callKeys message := by simp [callKeys]
    have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
    have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
    have hfr := mvSrc3_frame (D := ckKeys message state) hch (by key_mem_sep hsep)
    clear hm1 hm2 hm3
    rw [hfr 0 (not_ck_zero hsep), hfr 2 hck2, hfr _ (not_ck_bal hsep hlt)]
    clear hfr
    have e4 := Readable.eq_of_equal hc4
    have f5 := Supply.le_of_cond_lt1 hc5
    have f8 := lt_of_cond hc8
    have f10 := Supply.le_of_cond_gt1 hc10
    have f11 := Supply.le_of_cond_lt1 hc11
    have f12 := lt_of_cond hc12
    have f13 := Supply.le_of_cond_lt1 hc13
    clear hgas hch start hrun hok hc1 hc2 hc3 hc4 hc5 hc7 hc8 hc9 hc10 hc11 hc12 hc13
    simp only [and_mask_comm, mask_idem, and_m96_comm, m96_idem, storageAt_readSlot] at *
    simp (disch := slot_side) only
      [storageAt_readSlot, storageAt_writeSlot_self, storageAt_writeSlot_of_ne, m96_or, toNat_2p96, toNat_zeroW] at *
    have ea := m96_small f8
    simp only [ea] at *
    refine ⟨e4, f5, hc6, f8, by omega, ?_, trivial, ?_⟩
    · rw [m96_small f12, add_nat f11]
      omega
    · rw [add96_nat f13 f8]
      omega
  · have hm1 : message.caller.toU256 ∈ callKeys message := by simp [callKeys]
    have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
    have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
    have hfr := mvSrc3_frame (D := ckKeys message state) hch (by key_mem_sep hsep)
    clear hm1 hm2 hm3
    rw [hfr 0 (not_ck_zero hsep), hfr 2 hck2, hfr _ (not_ck_bal hsep hlt)]
    clear hfr
    have e4 := Readable.eq_of_equal hc4
    have f5 := Supply.le_of_cond_lt1 hc5
    have f8 := lt_of_cond hc8
    have f11 := Supply.le_of_cond_gt1 hc11
    have f12 := Supply.le_of_cond_lt1 hc12
    have f13 := lt_of_cond hc13
    have f14 := Supply.le_of_cond_lt1 hc14
    clear hgas hch start hrun hok hc1 hc2 hc3 hc4 hc5 hc7 hc8 hc9 hc10 hc11 hc12 hc13 hc14
    simp only [and_mask_comm, mask_idem, and_m96_comm, m96_idem, storageAt_readSlot] at *
    simp (disch := slot_side) only
      [storageAt_readSlot, storageAt_writeSlot_self, storageAt_writeSlot_of_ne, m96_or, toNat_2p96, toNat_zeroW] at *
    have ea := m96_small f8
    simp only [ea] at *
    have hT : (storageAt state message.currentTarget 0).toNat < 2 ^ 96 := by omega
    rw [toNat_div100, toNat_mul2 hT] at f11
    refine ⟨e4, f5, hc6, f8, f11, ?_, trivial, ?_⟩
    · rw [m96_small f13, add_nat f12]
      omega
    · rw [add96_nat f14 f8]
      omega

/-- `transfer(dst, rawAmount)`: a call that ends with no error came from a caller that is not
the zero address, for a recipient that is not the zero address and an amount below `2^96`
that is at most the balance of the caller. When the recipient is not the caller, the balance
of the caller is the old one minus the amount and the balance of the recipient is the old one
plus the amount. (For a transfer to oneself the end state is the one of `Paths.ok_transfer`;
it is not restated here.) `hsep` is the hypothesis on keccak, assumed. -/
theorem transfer_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (hsep : Sep (callKeys message) (ckKeys message state))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.caller.toU256 ≠ 0 ∧
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) ≠ 0 ∧
    (loadWord message.data 36 32).toNat < 2 ^ 96 ∧
    (loadWord message.data 36 32).toNat ≤ (balanceOf message.currentTarget state message.caller.toU256).toNat ∧
    (message.caller.toU256 ≠ (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) →
      (balanceOf message.currentTarget s.state message.caller.toU256).toNat =
          (balanceOf message.currentTarget state message.caller.toU256).toNat - (loadWord message.data 36 32).toNat ∧
        (balanceOf message.currentTarget s.state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32))).toNat =
          (balanceOf message.currentTarget state (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32))).toNat + (loadWord message.data 36 32).toNat) := by
  have hls : message.caller.toU256.toNat < 2 ^ 160 := toNat_toU256_lt _
  have hld := mask_lt (loadWord message.data 4 32)
  have hm2 : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) ∈ callKeys message := by simp [callKeys]
  unfold balanceOf
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hstat, hacc, hgas, hch⟩ :=
    ok_transfer hfork hsize' hsel start hrun hok
  have hm1 : message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  have hfr := mvSrc0_frame (D := ckKeys message state) hch (by key_mem_sep hsep)
    (by key_mem_sep hsep)
  clear hm1 hm3
  rw [hfr _ (not_ck_bal hsep hls), hfr _ (not_ck_bal hsep hld)]
  clear hfr
  have f4 := lt_of_cond hc4
  have f7 := Supply.le_of_cond_gt1 hc7
  have f8 := Supply.le_of_cond_lt1 hc8
  clear hgas hch start hrun hok hc1 hc2 hc3 hc4 hc7 hc8
  simp only [and_mask_comm, mask_idem, mask_toU256', and_m96_comm, m96_idem, storageAt_readSlot,
    toNat_2p96] at *
  have ea := m96_small f4
  simp only [ea] at *
  refine ⟨hc5, hc6, f4, f7, ?_⟩
  intro h
  have hne : mapSlot message.caller.toU256 4 ≠ mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) 4 :=
    fun e => h (hsep.uniq _ hm2 _ hls e)
  have hne' := Ne.symm hne
  simp (disch := slot_side) only
    [storageAt_readSlot, storageAt_writeSlot_self, storageAt_writeSlot_of_ne, m96_or] at f8 ⊢
  refine ⟨sub96_nat f7 f4, ?_⟩
  rw [add96_nat f8 f4]
  omega

end UniVerify

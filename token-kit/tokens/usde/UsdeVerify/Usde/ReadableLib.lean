import UsdeVerify.Usde.Sep

/-!
# Word lemmas for the readable corollaries of USDe

- `add_sub_same`: `v + (b - v) = b` on 256-bit words (a transfer to oneself).
- `and_high_comm`, `mask_or_high`, `mask_or_high_addr`, `mask_and_high`: the address in the low
  160 bits of a slot that also keeps its 96 high bits (`_owner`, `_pendingOwner`, `minter`).
- `transfer_no_wrap`, `mint_no_wrap`, `burn_no_wrap`: the three places where the bytecode of
  OpenZeppelin 4.9 does arithmetic with no check (`unchecked`): under the supply invariant
  `Inv` the result does not wrap.
-/

namespace UsdeVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- `v + (b - v) = b` on words. -/
theorem add_sub_same (v b : U256) : add v (sub b v) = b := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  have hb := b.isLt
  simp only [add, sub, BitVec.toNat_add, BitVec.toNat_sub]
  omega

/-- The mask of the 96 high bits is the complement of the mask of an address. -/
theorem high_eq_not_mask :
    (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) =
      ~~~(1461501637330902918203684832716283019655932542975 : U256) := by
  decide

theorem and_high_comm (w : U256) :
    bitwiseAnd w (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) =
      bitwiseAnd (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

theorem and_or_not (M w x : BitVec 256) : M &&& ((M &&& w) ||| (~~~M &&& x)) = M &&& w := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases M[i] <;> cases w[i] <;> cases x[i] <;> rfl

theorem and_and_not (M x : BitVec 256) : M &&& (~~~M &&& x) = 0 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not]
  cases M[i] <;> cases x[i] <;> simp

/-- The low 160 bits of "an address word, and the 96 high bits of `x`" are the address word. -/
theorem mask_or_high (w x : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseOr (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w)
          (bitwiseAnd (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) x)) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w := by
  unfold bitwiseAnd bitwiseOr
  rw [high_eq_not_mask]
  exact and_or_not _ _ _

/-- The same for the word of an address. -/
theorem mask_or_high_addr (a : Address) (x : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseOr a.toU256
          (bitwiseAnd (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) x)) =
      a.toU256 := by
  have h := mask_or_high a.toU256 x
  rw [mask_toU256'] at h
  exact h

/-- The low 160 bits of the 96 high bits of a word are 0. -/
theorem mask_and_high (x : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseAnd (115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256) x) =
      0 := by
  unfold bitwiseAnd
  rw [high_eq_not_mask]
  exact and_and_not _ _

variable {C : Address} {S : State.TransactionState}

/-- transfer and transferFrom: under the invariant, when `v ≤ _balances[x]` and `y` is another
address, the unchecked `_balances[y] + v` does not wrap. -/
theorem transfer_no_wrap {x y v : U256} (hx : x.toNat < 2 ^ 160) (hy : y.toNat < 2 ^ 160)
    (hne : x ≠ y) (h : Inv C S) (hle : v.toNat ≤ (storageAt S C (mapSlot x 2)).toNat) :
    (add v (storageAt S C (mapSlot y 2))).toNat =
      v.toNat + (storageAt S C (mapSlot y 2)).toNat := by
  have h2 := inv_two_balances_le hx hy hne h
  have ht := (storageAt S C 4).isLt
  simp only [add, BitVec.toNat_add]
  omega

/-- mint: under the invariant, when `_totalSupply + v` does not overflow (the bytecode checks
it), the unchecked `_balances[x] + v` does not wrap. -/
theorem mint_no_wrap {x v : U256} (hx : x.toNat < 2 ^ 160) (h : Inv C S)
    (hb : (storageAt S C 4).toNat + v.toNat < 2 ^ 256) :
    (add v (storageAt S C (mapSlot x 2))).toNat =
      v.toNat + (storageAt S C (mapSlot x 2)).toNat := by
  have h1 := inv_balance_le hx h
  simp only [add, BitVec.toNat_add]
  omega

/-- burn and burnFrom: under the invariant, when `v ≤ _balances[x]` (the bytecode checks it),
the unchecked `_totalSupply - v` does not wrap. -/
theorem burn_no_wrap {x v : U256} (hx : x.toNat < 2 ^ 160) (h : Inv C S)
    (hle : v.toNat ≤ (storageAt S C (mapSlot x 2)).toNat) :
    (sub (storageAt S C 4) v).toNat = (storageAt S C 4).toNat - v.toNat := by
  have h1 := inv_balance_le hx h
  have ht := (storageAt S C 4).isLt
  have hv := v.isLt
  simp only [sub, BitVec.toNat_sub]
  omega

end UsdeVerify

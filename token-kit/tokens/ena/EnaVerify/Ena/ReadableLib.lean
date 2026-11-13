import EnaVerify.Ena.Sep
import TokenKit.Evm.Opt06
import TokenKit.Evm.ReadableOpt

/-!
# Word lemmas for the readable corollaries of ENA

- `add_sub_same`: `v + (b - v) = b` on 256-bit words (a transfer to oneself).
- `and_high_comm`, `mask_or_high`, `mask_or_high_addr`, `mask_and_high`: the address in the low
  160 bits of a slot that also keeps its 96 high bits (`_owner`, `_pendingOwner`, the `lastMintTimestamp` slot keeps its own mask, `m40_idem`).
- `transfer_no_wrap`, `mint_no_wrap`, `burn_no_wrap`: the three places where the bytecode of
  OpenZeppelin 4.9 does arithmetic with no check (`unchecked`): under the supply invariant
  `Inv` the result does not wrap.
-/

namespace EnaVerify

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

/-- Masking a word to its 40 low bits twice is masking it once (`lastMintTimestamp()`). -/
theorem m40_idem (w : U256) :
    bitwiseAnd (bitwiseAnd (1099511627775 : U256) w) (1099511627775 : U256) =
      bitwiseAnd (1099511627775 : U256) w := by
  unfold bitwiseAnd
  ext i hi
  simp only [BitVec.getElem_and]
  cases (1099511627775 : BitVec 256)[i] <;> cases w[i] <;> rfl

/-- The quotient of two words, for a divisor that is not 0, as a natural number. -/
theorem div_nat {a b : U256} (hb : b ≠ 0) : (div a b).toNat = a.toNat / b.toNat := by
  unfold div
  rw [if_neg hb, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

/-- The check of the Solidity 0.8 product `10 * x` in `mint` (`x = 0`, or `(10 * x) / x = 10`):
the product does not wrap. -/
theorem mul10_nat {x : U256}
    (h : bitwiseOr (equal (10 : U256) (div (mul (10 : U256) x) x)) (isZero x) ≠ 0) :
    (mul (10 : U256) x).toNat = 10 * x.toNat := by
  have hx := x.isLt
  by_cases h0 : x = 0
  · subst h0
    decide
  · have hz : isZero x = 0 := by
      unfold isZero
      exact if_neg h0
    have he : equal (10 : U256) (div (mul (10 : U256) x) x) ≠ 0 := by
      intro e
      apply h
      rw [e, hz]
      decide
    have e10 : (10 : U256) = div (mul (10 : U256) x) x := by
      by_cases e : (10 : U256) = div (mul (10 : U256) x) x
      · exact e
      · exfalso
        apply he
        unfold equal
        exact if_neg e
    have hd := div_nat (a := mul (10 : U256) x) h0
    have e10n : (div (mul (10 : U256) x) x).toNat = 10 := by
      rw [← e10]
      decide
    rw [e10n] at hd
    have hm : (mul (10 : U256) x).toNat = (10 * x.toNat) % 2 ^ 256 := by
      unfold mul
      rw [BitVec.toNat_mul]
      have e : (10 : U256).toNat = 10 := by decide
      rw [e]
    have h1 := Nat.div_mul_le_self (mul (10 : U256) x).toNat x.toNat
    rw [← hd] at h1
    have h2 : (10 * x.toNat) % 2 ^ 256 ≤ 10 * x.toNat := Nat.mod_le _ _
    omega

/-- `mint`: after the checked `block.timestamp - lastMintTimestamp` and the wait check
(`ISZERO (LT diff 31536000)`), the block time is at least the last mint time plus 365 days. -/
theorem mint_wait_nat {t l : U256} (h5 : isZero (greaterThan (sub t l) t) ≠ 0)
    (h6 : isZero (lessThan (sub t l) (31536000 : U256)) ≠ 0) :
    l.toNat + 31536000 ≤ t.toNat := by
  have a := le_of_sub_check h5
  have b := sub_nat_check h5
  have c := Supply.le_of_cond_lt1 h6
  have e : (31536000 : U256).toNat = 31536000 := by decide
  omega

/-- `mint`: after the checked product and the cap check (`ISZERO (GT amount (10 * x / 100))`),
the amount is at most 10 percent of `x`, rounded down. -/
theorem mint_cap_nat {v x : U256}
    (h7 : bitwiseOr (equal (10 : U256) (div (mul (10 : U256) x) x)) (isZero x) ≠ 0)
    (h8 : isZero (greaterThan v (div (mul (10 : U256) x) (100 : U256))) ≠ 0) :
    v.toNat ≤ 10 * x.toNat / 100 := by
  have m := mul10_nat h7
  have l := Supply.le_of_cond_gt1 h8
  have hd := div_nat (a := mul (10 : U256) x) (b := (100 : U256)) (by decide)
  have e : (100 : U256).toNat = 100 := by decide
  rw [e, m] at hd
  rw [hd] at l
  exact l

/-- The check of `10 * x` passes: `10 * x` is below `2^256`. -/
theorem mul10_bound {x : U256}
    (h : bitwiseOr (equal (10 : U256) (div (mul (10 : U256) x) x)) (isZero x) ≠ 0) :
    10 * x.toNat < 2 ^ 256 := by
  have m := mul10_nat h
  have := (mul (10 : U256) x).isLt
  omega

/-- The mask of the 216 high bits is the complement of the mask of the 40 low bits. -/
theorem high40_eq_not :
    (115792089237316195423570985008687907853269984665640564039457584006813618012160 : U256) =
      ~~~(1099511627775 : U256) := by
  decide

/-- `mint` writes the block time in the 40 low bits of slot 11 and keeps the 216 high bits:
the 40 low bits of the new word are those of the block time. -/
theorem m40_or_high (w x : U256) :
    bitwiseAnd (1099511627775 : U256)
        (bitwiseOr (bitwiseAnd (1099511627775 : U256) w)
          (bitwiseAnd (115792089237316195423570985008687907853269984665640564039457584006813618012160 : U256) x)) =
      bitwiseAnd (1099511627775 : U256) w := by
  unfold bitwiseAnd bitwiseOr
  rw [high40_eq_not]
  exact and_or_not _ _ _

end EnaVerify

import TokenKit.Evm.Opt06
import TokenKit.Evm.ReadableOpt

/-!
# Word facts of optimized Solidity 0.8 code: masks, a packed slot, checked product and quotient

Moved from the local libraries of USDE and ENA (`Usde/ReadableLib.lean`, `Ena/ReadableLib.lean`),
which keep their copies in their own namespaces.

- `add_sub_same`: `v + (b - v) = b`.
- `high_eq_not_mask`, `and_high_comm`, `and_or_not`, `and_and_not`, `mask_or_high`,
  `mask_or_high_addr`, `mask_and_high`: an address packed in the 160 low bits of a word.
- `m40_idem`, `high40_eq_not`, `m40_or_high`: a uint40 packed in the 40 low bits of a word.
- `div_nat`, `mul10_nat`, `mul10_bound`: the quotient as a natural number, and the checked
  product `10 * x` of Solidity 0.8 (`x == 0 || (10 * x) / x == 10`).
-/

namespace TokenKit

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

/-- Masking a word to its 40 low bits twice is masking it once. -/
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

/-- The check of the Solidity 0.8 product `10 * x` (`x = 0`, or `(10 * x) / x = 10`):
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

/-- The 40 low bits of "the 40 low bits of `w`, and the 216 high bits of `x`" are those of `w`. -/
theorem m40_or_high (w x : U256) :
    bitwiseAnd (1099511627775 : U256)
        (bitwiseOr (bitwiseAnd (1099511627775 : U256) w)
          (bitwiseAnd (115792089237316195423570985008687907853269984665640564039457584006813618012160 : U256) x)) =
      bitwiseAnd (1099511627775 : U256) w := by
  unfold bitwiseAnd bitwiseOr
  rw [high40_eq_not]
  exact and_or_not _ _ _

end TokenKit

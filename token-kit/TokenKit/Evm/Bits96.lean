import TokenKit.Evm.Opt06

/-!
# Words of a Compound-style token: 96-bit amounts and 32-bit block numbers

The bytecode of a Compound-style token (UNI, COMP, ONDO) keeps `uint96` amounts under the mask
`2^96 - 1` and `uint32` numbers under the mask `2^32 - 1`.

- `and_m96_comm`, `m96_idem`, `m96_or`: the mask of 96 bits to one form; the low 96 bits of
  "96 bits of `x`, and the other bits of `y`" (how a packed slot is written) are those of `x`.
- `toNat_m96`, `m96_lt`, `m32_lt`, `and_m32_comm`: the masked words as natural numbers.
- `toNat_addW`, `toNat_subW`, `lt_of_cond`, `toNat_2p96`: the EVM words of ADD, SUB and LT as
  natural numbers, for `omega`.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

theorem and_m96_comm (w : U256) :
    bitwiseAnd w (79228162514264337593543950335 : U256) =
      bitwiseAnd (79228162514264337593543950335 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

theorem m96_idem (w : U256) :
    bitwiseAnd (79228162514264337593543950335 : U256)
        (bitwiseAnd (79228162514264337593543950335 : U256) w) =
      bitwiseAnd (79228162514264337593543950335 : U256) w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

theorem and_or_not256 (M w x : BitVec 256) : M &&& ((M &&& w) ||| (~~~M &&& x)) = M &&& w := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases M[i] <;> cases w[i] <;> cases x[i] <;> rfl

theorem high160_eq_not_m96 :
    (115792089237316195423570985008687907853269984665561335876943319670319585689600 : U256) =
      ~~~(79228162514264337593543950335 : U256) := by
  decide

/-- The low 96 bits of "96 bits of `x`, and the 160 high bits of `y`" are those of `x`. -/
theorem m96_or (x y : U256) :
    bitwiseAnd (79228162514264337593543950335 : U256)
        (bitwiseOr (bitwiseAnd (79228162514264337593543950335 : U256) x)
          (bitwiseAnd (115792089237316195423570985008687907853269984665561335876943319670319585689600 : U256) y)) =
      bitwiseAnd (79228162514264337593543950335 : U256) x := by
  unfold bitwiseAnd bitwiseOr
  rw [high160_eq_not_m96]
  exact and_or_not256 _ _ _

theorem toNat_m96 (w : U256) :
    (bitwiseAnd (79228162514264337593543950335 : U256) w).toNat = w.toNat % 2 ^ 96 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 96

theorem m96_lt (w : U256) :
    (bitwiseAnd (79228162514264337593543950335 : U256) w).toNat < 2 ^ 96 := by
  rw [toNat_m96]
  exact Nat.mod_lt _ (by decide)

theorem and_m32_comm (w : U256) :
    bitwiseAnd w (4294967295 : U256) = bitwiseAnd (4294967295 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

theorem m32_lt (w : U256) : (bitwiseAnd (4294967295 : U256) w).toNat < 2 ^ 32 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem m160_lt (w : U256) :
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat < 2 ^ 160 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem m160_ltR (w : U256) :
    (bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256)).toNat < 2 ^ 160 := by
  rw [and_mask_comm]
  exact m160_lt w

theorem m160_idem (w : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

theorem toNat_addW (a b : U256) : (add a b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  simp only [add, BitVec.toNat_add]

theorem toNat_subW (a b : U256) : (sub a b).toNat = (2 ^ 256 - b.toNat + a.toNat) % 2 ^ 256 := by
  simp only [sub, BitVec.toNat_sub]

/-- `LT a b` is not 0: `a < b`. -/
theorem lt_of_cond {a b : U256} (h : lessThan a b ≠ 0) : a.toNat < b.toNat := by
  by_cases hlt : a.toNat < b.toNat
  · exact hlt
  · exfalso
    apply h
    exact if_neg hlt

theorem toNat_2p96 : (79228162514264337593543950336 : U256).toNat = 2 ^ 96 := by decide

theorem toNat_zeroW : (0 : U256).toNat = 0 := rfl

/-- A word below `2^96` is its own low 96 bits. -/
theorem m96_small {a : U256} (h : a.toNat < 2 ^ 96) :
    bitwiseAnd (79228162514264337593543950335 : U256) a = a := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_m96]
  exact Nat.mod_eq_of_lt h

/-- The checked `uint96` subtraction of a Compound-style token (`sub96`): after
`require(a <= o)`, the low 96 bits of the difference are the difference. -/
theorem sub96_nat {a o : U256}
    (h1 : a.toNat ≤ (bitwiseAnd (79228162514264337593543950335 : U256) o).toNat)
    (h2 : a.toNat < 2 ^ 96) :
    (bitwiseAnd (79228162514264337593543950335 : U256)
        (sub (bitwiseAnd (79228162514264337593543950335 : U256) o) a)).toNat =
      (bitwiseAnd (79228162514264337593543950335 : U256) o).toNat - a.toNat := by
  have hx := m96_lt o
  rw [toNat_m96 (sub _ _), toNat_subW]
  have e : 2 ^ 256 - a.toNat +
      (bitwiseAnd (79228162514264337593543950335 : U256) o).toNat =
      2 ^ 256 + ((bitwiseAnd (79228162514264337593543950335 : U256) o).toNat - a.toNat) := by
    omega
  rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The checked `uint96` addition of a Compound-style token (`add96`): after
`require(c >= x)` on the low 96 bits `c` of the sum, the low 96 bits of the sum are the sum. -/
theorem add96_nat {a x : U256}
    (h1 : (bitwiseAnd (79228162514264337593543950335 : U256) x).toNat ≤
      (bitwiseAnd (79228162514264337593543950335 : U256)
        (add a (bitwiseAnd (79228162514264337593543950335 : U256) x))).toNat)
    (h2 : a.toNat < 2 ^ 96) :
    (bitwiseAnd (79228162514264337593543950335 : U256)
        (add a (bitwiseAnd (79228162514264337593543950335 : U256) x))).toNat =
      a.toNat + (bitwiseAnd (79228162514264337593543950335 : U256) x).toNat := by
  have hx := m96_lt x
  rw [toNat_m96 (add _ _), toNat_addW] at h1 ⊢
  rw [Nat.mod_eq_of_lt (a := a.toNat + _) (b := 2 ^ 256) (by omega)] at h1 ⊢
  omega

/-- The check of a SafeMath addition `a + t` (`c >= t` on the sum `c`): the sum does not
wrap. -/
theorem add_nat {a t : U256} (h : t.toNat ≤ (add a t).toNat) :
    (add a t).toNat = a.toNat + t.toNat := by
  have ha := a.isLt
  have ht := t.isLt
  rw [toNat_addW] at h ⊢
  omega

end TokenKit

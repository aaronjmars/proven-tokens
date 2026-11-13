import Mathlib.Tactic.ClearExcept
import TokenKit.Evm.Bits96
import TokenKit.Evm.Named

/-!
# Branch conditions of ONDO as facts on natural numbers

Solidity 0.8 checks every `+`, `-` and `*`, and ONDO also keeps the explicit `safe96`, `add96`
and `sub96` checks of Compound. Many of these checks can never fail where they stand: the
earlier checks of the same path already decide them. A path through the failing side of such a
check would be a theorem with contradicting hypotheses. The path generator does not state it:
it proves, with the tactics of this file, that the check passes, and walks the passing side only.

- `c_*`: a branch condition (`isZero`, `lessThan`, `greaterThan`, `equal`, the AND of two
  flags) that is or is not 0, as a statement on natural numbers.
- `toNat_*`: the words of MUL, DIV and of the masks of 8, 32 and 160 bits as natural numbers.
- `word_omega h1 h2 ...`: rewrites the hypotheses named and the goal with these lemmas, then
  `omega`. `dead_omega` is the same tactic under the name the generator uses for a branch.
- `vest_le`: `initial * elapsed / period <= initial` when `elapsed <= period` (not linear, so
  it is given to `omega` as a fact). `div_max_ge`: the largest word divided by a `uint96` that
  is not 0 is at least `2^160` (the overflow check of a checked multiplication by a word that
  is known to be small).

Nothing here is about the storage of ONDO; the lemmas are about words. They are local to this
token because the shared kit was frozen while this proof was written (status.json,
`to_merge_into_kit`).
-/

namespace OndoVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

theorem c_isZero_ne (x : U256) : (isZero x ≠ 0) = (x = 0) := by
  apply propext
  constructor
  · intro h
    exact Classical.not_not.mp (fun hx => h (isZero_eq_zero_iff.mpr hx))
  · intro h e
    exact (isZero_eq_zero_iff.mp e) h

theorem c_isZero_eq (x : U256) : (isZero x = 0) = (x ≠ 0) :=
  propext isZero_eq_zero_iff

theorem c_lt_ne (a b : U256) : (lessThan a b ≠ 0) = (a.toNat < b.toNat) := by
  apply propext
  constructor
  · exact lt_of_cond
  · intro h e
    have e1 : lessThan a b = 1 := if_pos h
    rw [e1] at e
    exact absurd e (by decide)

theorem c_lt_eq (a b : U256) : (lessThan a b = 0) = (b.toNat ≤ a.toNat) := by
  apply propext
  constructor
  · intro e
    by_cases h : a.toNat < b.toNat
    · have e1 : lessThan a b = 1 := if_pos h
      rw [e1] at e
      exact absurd e (by decide)
    · omega
  · intro h
    exact if_neg (by omega)

theorem c_gt_ne (a b : U256) : (greaterThan a b ≠ 0) = (b.toNat < a.toNat) :=
  c_lt_ne b a

theorem c_gt_eq (a b : U256) : (greaterThan a b = 0) = (a.toNat ≤ b.toNat) :=
  c_lt_eq b a

theorem c_eq_ne (a b : U256) : (equal a b ≠ 0) = (a.toNat = b.toNat) := by
  apply propext
  constructor
  · intro h
    by_cases e : a = b
    · rw [e]
    · exact absurd (if_neg e) h
  · intro h e
    have e1 : equal a b = 1 := if_pos (BitVec.eq_of_toNat_eq h)
    rw [e1] at e
    exact absurd e (by decide)

theorem c_eq_eq (a b : U256) : (equal a b = 0) = (a.toNat ≠ b.toNat) := by
  apply propext
  constructor
  · intro e h
    have e1 : equal a b = 1 := if_pos (BitVec.eq_of_toNat_eq h)
    rw [e1] at e
    exact absurd e (by decide)
  · intro h
    exact if_neg (fun e => h (by rw [e]))

/-- A word is 0 exactly when its number is 0. -/
theorem w_eq0 (x : U256) : (x = 0) = (x.toNat = 0) := by
  apply propext
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact BitVec.eq_of_toNat_eq h

theorem iszz_zero : isZero (isZero (0 : U256)) = 0 := by decide

theorem iszz_ne {y : U256} (h : y ≠ 0) : isZero (isZero y) = 1 := by
  have e : isZero y = 0 := if_neg h
  rw [e]
  decide

/-- The overflow test of a checked multiplication: `y != 0 && a > b`. -/
theorem c_andb_ne (y a b : U256) :
    (bitwiseAnd (isZero (isZero y)) (greaterThan a b) ≠ 0) =
      (y.toNat ≠ 0 ∧ b.toNat < a.toNat) := by
  apply propext
  by_cases hy : y = 0
  · rw [hy, iszz_zero]
    by_cases hg : b.toNat < a.toNat
    · have e : greaterThan a b = 1 := if_pos hg
      rw [e]
      constructor
      · intro h
        exact absurd (by decide) h
      · intro h
        exact absurd rfl h.1
    · have e : greaterThan a b = 0 := if_neg hg
      rw [e]
      constructor
      · intro h
        exact absurd (by decide) h
      · intro h
        exact absurd rfl h.1
  · have hy' : y.toNat ≠ 0 := fun e => hy (BitVec.eq_of_toNat_eq e)
    rw [iszz_ne hy]
    by_cases hg : b.toNat < a.toNat
    · have e : greaterThan a b = 1 := if_pos hg
      rw [e]
      constructor
      · intro _
        exact ⟨hy', hg⟩
      · intro _
        decide
    · have e : greaterThan a b = 0 := if_neg hg
      rw [e]
      constructor
      · intro h
        exact absurd (by decide) h
      · intro h
        exact absurd h.2 hg

theorem c_andb_eq (y a b : U256) :
    (bitwiseAnd (isZero (isZero y)) (greaterThan a b) = 0) =
      (y.toNat = 0 ∨ a.toNat ≤ b.toNat) := by
  apply propext
  have h := c_andb_ne y a b
  constructor
  · intro e
    by_cases hy : y.toNat = 0
    · exact Or.inl hy
    · by_cases hg : b.toNat < a.toNat
      · exact absurd e (h.mpr ⟨hy, hg⟩)
      · exact Or.inr (by omega)
  · intro e
    exact Classical.not_not.mp (fun hne => by
      have := h.mp hne
      omega)

/-- The overflow test of a checked multiplication by a numeral that is not 0: `1 && a > b`. -/
theorem c_and1_ne (a b : U256) :
    (bitwiseAnd (1 : U256) (greaterThan a b) ≠ 0) = (b.toNat < a.toNat) := by
  apply propext
  by_cases hg : b.toNat < a.toNat
  · have e : greaterThan a b = 1 := if_pos hg
    rw [e]
    constructor
    · intro _
      exact hg
    · intro _
      decide
  · have e : greaterThan a b = 0 := if_neg hg
    rw [e]
    constructor
    · intro h
      exact absurd (by decide) h
    · intro h
      exact absurd h hg

theorem c_and1_eq (a b : U256) :
    (bitwiseAnd (1 : U256) (greaterThan a b) = 0) = (a.toNat ≤ b.toNat) := by
  apply propext
  have h := c_and1_ne a b
  constructor
  · intro e
    by_cases hg : b.toNat < a.toNat
    · exact absurd e (h.mpr hg)
    · omega
  · intro e
    exact Classical.not_not.mp (fun hne => by
      have := h.mp hne
      omega)

theorem toNat_mulW (a b : U256) : (mul a b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  simp only [mul, BitVec.toNat_mul]

theorem toNat_divW (a b : U256) : (div a b).toNat = a.toNat / b.toNat := by
  unfold div
  by_cases h : b = 0
  · rw [if_pos h, h]
    show (0 : Nat) = a.toNat / 0
    exact (Nat.div_zero _).symm
  · rw [if_neg h, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt)

theorem toNat_m8 (w : U256) : (bitwiseAnd (255 : U256) w).toNat = w.toNat % 2 ^ 8 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 8

theorem and_m8_comm (w : U256) : bitwiseAnd w (255 : U256) = bitwiseAnd (255 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

theorem toNat_m32 (w : U256) :
    (bitwiseAnd (4294967295 : U256) w).toNat = w.toNat % 2 ^ 32 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 32

theorem toNat_m160 (w : U256) :
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat =
      w.toNat % 2 ^ 160 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  rw [Nat.and_comm]
  exact Nat.and_two_pow_sub_one_eq_mod w.toNat 160

/-- `initial * elapsed / period <= initial` when `elapsed <= period`: the product of a
`uint96` and a period below `2^64` does not wrap. -/
theorem vest_le (y e : U256) (P : Nat) (hP : 0 < P) (hP2 : P < 2 ^ 64)
    (hy : y.toNat < 2 ^ 96) (he : e.toNat ≤ P) :
    (mul y e).toNat / P ≤ y.toNat := by
  have h1 : y.toNat * e.toNat ≤ y.toNat * P := Nat.mul_le_mul_left _ he
  have h2 : y.toNat * P < 2 ^ 96 * 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt hP2))
      (Nat.mul_lt_mul_of_pos_right hy (by decide))
  have h3 : y.toNat * e.toNat < 2 ^ 256 :=
    Nat.lt_of_le_of_lt h1 (Nat.lt_trans h2 (by decide))
  rw [toNat_mulW, Nat.mod_eq_of_lt h3]
  exact Nat.le_trans (Nat.div_le_div_right h1) (Nat.le_of_eq (Nat.mul_div_cancel _ hP))

/-- The largest word divided by a `uint96` that is not 0 is at least `2^160`. -/
theorem div_max_ge (y : U256) (hy : y.toNat < 2 ^ 96) (h0 : y.toNat ≠ 0) :
    2 ^ 160 ≤
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256).toNat /
        y.toNat := by
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero h0)]
  have e : (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
      U256).toNat = 2 ^ 256 - 1 := by decide
  rw [e]
  have h1 : 2 ^ 160 * y.toNat ≤ 2 ^ 160 * (2 ^ 96 - 1) := Nat.mul_le_mul_left _ (by omega)
  exact Nat.le_trans h1 (by decide)

/-- Two thirds of `initial * elapsed / period`, plus a third of `initial`, is at most `initial`
when `elapsed <= period` (the vested amount of a seed investor), and the doubling does not
wrap. The statement is in the form `word_omega` gives to the words of the path. -/
theorem seed_le (y e : U256) (P : Nat) (hP : 0 < P) (hP2 : P < 2 ^ 64)
    (hy : y.toNat < 2 ^ 96) (he : e.toNat ≤ P) :
    (2 * ((mul y e).toNat / P) % 2 ^ 256) / 3 + y.toNat / 3 ≤ y.toNat ∧
      (2 * ((mul y e).toNat / P) % 2 ^ 256) / 3 < 2 ^ 96 := by
  have h := vest_le y e P hP hP2 hy he
  generalize (mul y e).toNat / P = v at h ⊢
  omega

end OndoVerify

/-- A checked subtraction of words that does not wrap, as a subtraction of natural numbers. -/
theorem OndoVerify.sub_mod_of_le {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 256) :
    (2 ^ 256 - b + a) % 2 ^ 256 = a - b := by omega

/-- Rewrite the named hypotheses and the goal (branch conditions, words) as statements on
natural numbers, drop every `% n` of a number that `omega` shows to be below `n` (the `omega`
of Lean does not always find that such a quotient is 0), then `omega`. -/
macro "word_omega" hs:(ppSpace colGt ident)* : tactic => `(tactic| (
  try simp only [UsdtVerify.storageAt_readSlot, TokenKit.and_m96_comm, TokenKit.and_m32_comm,
    TokenKit.and_mask_comm, OndoVerify.and_m8_comm,
    OndoVerify.c_isZero_ne, OndoVerify.c_isZero_eq, OndoVerify.c_andb_ne, OndoVerify.c_andb_eq,
    OndoVerify.c_and1_ne, OndoVerify.c_and1_eq, OndoVerify.c_lt_ne, OndoVerify.c_lt_eq,
    OndoVerify.c_gt_ne, OndoVerify.c_gt_eq, OndoVerify.c_eq_ne, OndoVerify.c_eq_eq]
    at $[$hs:ident]* ⊢
  try simp only [ne_eq, OndoVerify.w_eq0, TokenKit.toNat_m96, OndoVerify.toNat_m8,
    OndoVerify.toNat_m32, OndoVerify.toNat_m160, TokenKit.toNat_addW, TokenKit.toNat_subW,
    OndoVerify.toNat_mulW, OndoVerify.toNat_divW, BitVec.reduceToNat] at $[$hs:ident]* ⊢
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at $[$hs:ident]* ⊢
  try simp (disch := omega) only [Nat.mod_eq_of_lt, OndoVerify.sub_mod_of_le] at $[$hs:ident]* ⊢
  omega))

/-- Decide a branch from earlier conditions of the path (see `word_omega`). -/
macro "dead_omega" hs:(ppSpace colGt ident)* : tactic =>
  `(tactic| (clear * - $[$hs:ident]*; word_omega $[$hs:ident]*))

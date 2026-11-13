import WbtcVerify.Wbtc.Lib
import WbtcVerify.Wbtc.Sep
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt
import TokenKit.Evm.Opt06
import TokenKit.Evm.Bits08

/-!
# Lemmas for the readable corollaries of WBTC

What it proves (pure facts about 256-bit words, nothing about a run of the code):

- `Readable.add_bound_ltc`, `Readable.add_nat_ltc`: the SafeMath addition of Solidity 0.4 with the
  optimizer on (`ISZERO (LT (ADD v b) b)` is not 0): no overflow, and the sum as a number.
- `Readable.lt_of_lessThan`, `Readable.ge_of_lessThan`: `LT a b` as a jump condition.
- `and_255_comm`, `and_255_idem`: the mask of a byte.
- `slot_5_6`, `slot_6_5`: slots 5 and 6 are two slots.
- `div_256`, `div_168`, `div_176`: a division by `2^8`, `2^168`, `2^176` is a shift to the right.
- The fields of the packed slot 5 after each write the code makes. With `x` the old word of
  slot 5 and `y` the old word of slot 6:
  `pause` writes `2^176 | (x & ~(0xff << 176))` (`paused_pause`, `owner_pause`, `minting_pause`,
  `decimals_pause`); `unpause` writes `x & ~(0xff << 176)` (`paused_unpause`, `owner_unpause`,
  `minting_unpause`, `decimals_unpause`); `claimOwnership` writes
  `((y & mask160) * 256) | (x & ~(mask160 << 8))` (`owner_claim`, `paused_claim`,
  `minting_claim`, `decimals_claim`). Each lemma gives one field of the new word: the byte of
  `paused` (byte 22), the byte of `mintingFinished` (byte 21), `owner` (bits 8 to 167) or
  `decimals` (byte 0).

What is assumed: nothing (no hypothesis on keccak, no axiom beyond Lean's own).
What is not covered: nothing about the bytecode; the lemmas are used by Readable.lean and
Roles.lean.
-/

set_option autoImplicit false

namespace WbtcVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Readable

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- After the SafeMath addition of Solidity 0.4 with the optimizer on (`c = v + b;
assert(c >= b)`), the sum is below `2^256`. -/
theorem add_bound_ltc {v b : U256} (h : isZero (lessThan (add v b) b) ≠ 0) :
    b.toNat + v.toNat < 2 ^ 256 := by
  have f := WbtcVerify.Supply.add_fact_ltc h
  have := (add v b).isLt
  omega

/-- After the same check, the sum as a natural number. -/
theorem add_nat_ltc {v b : U256} (h : isZero (lessThan (add v b) b) ≠ 0) :
    (add v b).toNat = v.toNat + b.toNat := by
  have f := WbtcVerify.Supply.add_fact_ltc h
  omega

/-- `LT a b` is not 0: `a < b`. -/
theorem lt_of_lessThan {a b : U256} (h : lessThan a b ≠ 0) : a.toNat < b.toNat := by
  by_cases hlt : a.toNat < b.toNat
  · exact hlt
  · exfalso
    have e : lessThan a b = 0 := if_neg hlt
    exact h e

/-- `LT a b` is 0: `b <= a`. -/
theorem ge_of_lessThan {a b : U256} (h : lessThan a b = 0) : b.toNat ≤ a.toNat := by
  by_cases hlt : a.toNat < b.toNat
  · exfalso
    have e : lessThan a b = 1 := if_pos hlt
    rw [e] at h
    exact absurd h (by decide)
  · omega

end WbtcVerify.Readable

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Readable

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The mask of a byte on the right of AND is the mask on the left. -/
theorem and_255_comm (w : U256) : bitwiseAnd w (255 : U256) = bitwiseAnd (255 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

/-- The mask of a byte, twice. -/
theorem and_255_idem (w : U256) :
    bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) w) = bitwiseAnd (255 : U256) w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

/-- Slot 5 is not slot 6. -/
theorem slot_5_6 : ((5 : U256) = (6 : U256)) = False := eq_false (by decide)

/-- Slot 6 is not slot 5. -/
theorem slot_6_5 : ((6 : U256) = (5 : U256)) = False := eq_false (by decide)

/-! ## Bits -/

theorem and_or_and (m a c x : BitVec 256) :
    m &&& (a ||| (c &&& x)) = (m &&& a) ||| ((m &&& c) &&& x) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases m[i] <;> cases a[i] <;> cases c[i] <;> cases x[i] <;> rfl

theorem zero_or_and (m x : BitVec 256) : (0 : BitVec 256) ||| (m &&& x) = m &&& x := by
  ext i hi
  simp

theorem or_zero_and (v x : BitVec 256) : v ||| ((0 : BitVec 256) &&& x) = v := by
  ext i hi
  simp

theorem zero_and_any (x : BitVec 256) : (0 : BitVec 256) &&& x = 0 := by
  ext i hi
  simp

/-- A division by a power of two is a shift to the right. -/
theorem div_pow (w p : U256) (k : Nat) (hp : p.toNat = 2 ^ k) : div w p = w >>> k := by
  have hne : p ≠ 0 := by
    intro e
    rw [e] at hp
    have h0 : (0 : U256).toNat = 0 := rfl
    rw [h0] at hp
    exact absurd hp (Nat.ne_of_lt (Nat.two_pow_pos k))
  unfold div
  rw [if_neg hne]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hp]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) w.isLt)

theorem div_256 (w : U256) : div w (256 : U256) = w >>> 8 := div_pow w _ 8 (by decide)

theorem div_168 (w : U256) : div w (374144419156711147060143317175368453031918731001856 : U256) = w >>> 168 := div_pow w _ 168 (by decide +kernel)

theorem div_176 (w : U256) : div w (95780971304118053647396689196894323976171195136475136 : U256) = w >>> 176 := div_pow w _ 176 (by decide +kernel)

/-- A field (mask `m` after a shift by `k`) of the word `a | (c & x)`. -/
theorem fld (m a c x v cc : BitVec 256) (k : Nat) (h1 : m &&& (a >>> k) = v)
    (h2 : m &&& (c >>> k) = cc) :
    m &&& ((a ||| (c &&& x)) >>> k) = v ||| (cc &&& (x >>> k)) := by
  rw [BitVec.ushiftRight_or_distrib, BitVec.ushiftRight_and_distrib, and_or_and, h1, h2]

/-- The same with no shift. -/
theorem fldN (m a c x v cc : BitVec 256) (h1 : m &&& a = v) (h2 : m &&& c = cc) :
    m &&& (a ||| (c &&& x)) = v ||| (cc &&& x) := by
  rw [and_or_and, h1, h2]

/-- A field of the word `c & x`. -/
theorem fld0 (m c x cc : BitVec 256) (k : Nat) (h2 : m &&& (c >>> k) = cc) :
    m &&& ((c &&& x) >>> k) = cc &&& (x >>> k) := by
  rw [BitVec.ushiftRight_and_distrib, ← BitVec.and_assoc, h2]

/-- The same with no shift. -/
theorem fld0N (m c x cc : BitVec 256) (h2 : m &&& c = cc) : m &&& (c &&& x) = cc &&& x := by
  rw [← BitVec.and_assoc, h2]

/-! ## pause(): the word `2^176 | (x & ~(0xff << 176))` -/

theorem paused_pause (x : U256) :
    bitwiseAnd (255 : U256) (div (bitwiseOr (95780971304118053647396689196894323976171195136475136 : U256) (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x)) (95780971304118053647396689196894323976171195136475136 : U256)) = 1 := by
  simp only [div_176, bitwiseAnd, bitwiseOr]
  exact (fld (255 : U256) (95780971304118053647396689196894323976171195136475136 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x 1 0 176 (by decide +kernel) (by decide +kernel)).trans
    (or_zero_and _ _)

theorem owner_pause (x : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (bitwiseOr (95780971304118053647396689196894323976171195136475136 : U256) (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x)) (256 : U256)) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div x (256 : U256)) := by
  simp only [div_256, bitwiseAnd, bitwiseOr]
  exact (fld (1461501637330902918203684832716283019655932542975 : U256) (95780971304118053647396689196894323976171195136475136 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x 0 (1461501637330902918203684832716283019655932542975 : U256) 8 (by decide +kernel) (by decide +kernel)).trans
    (zero_or_and _ _)

theorem minting_pause (x : U256) :
    bitwiseAnd (255 : U256) (div (bitwiseOr (95780971304118053647396689196894323976171195136475136 : U256) (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x)) (374144419156711147060143317175368453031918731001856 : U256)) =
      bitwiseAnd (255 : U256) (div x (374144419156711147060143317175368453031918731001856 : U256)) := by
  simp only [div_168, bitwiseAnd, bitwiseOr]
  exact (fld (255 : U256) (95780971304118053647396689196894323976171195136475136 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x 0 (255 : U256) 168 (by decide +kernel) (by decide +kernel)).trans
    (zero_or_and _ _)

theorem decimals_pause (x : U256) :
    bitwiseAnd (255 : U256) (bitwiseOr (95780971304118053647396689196894323976171195136475136 : U256) (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x)) = bitwiseAnd (255 : U256) x := by
  simp only [bitwiseAnd, bitwiseOr]
  exact (fldN (255 : U256) (95780971304118053647396689196894323976171195136475136 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x 0 (255 : U256) (by decide +kernel) (by decide +kernel)).trans
    (zero_or_and _ _)

/-! ## unpause(): the word `x & ~(0xff << 176)` -/

theorem paused_unpause (x : U256) : bitwiseAnd (255 : U256) (div (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x) (95780971304118053647396689196894323976171195136475136 : U256)) = 0 := by
  simp only [div_176, bitwiseAnd]
  exact (fld0 (255 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x 0 176 (by decide +kernel)).trans (zero_and_any _)

theorem owner_unpause (x : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x) (256 : U256)) = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div x (256 : U256)) := by
  simp only [div_256, bitwiseAnd]
  exact fld0 (1461501637330902918203684832716283019655932542975 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x (1461501637330902918203684832716283019655932542975 : U256) 8 (by decide +kernel)

theorem minting_unpause (x : U256) :
    bitwiseAnd (255 : U256) (div (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x) (374144419156711147060143317175368453031918731001856 : U256)) = bitwiseAnd (255 : U256) (div x (374144419156711147060143317175368453031918731001856 : U256)) := by
  simp only [div_168, bitwiseAnd]
  exact fld0 (255 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x (255 : U256) 168 (by decide +kernel)

theorem decimals_unpause (x : U256) : bitwiseAnd (255 : U256) (bitwiseAnd (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x) = bitwiseAnd (255 : U256) x := by
  simp only [bitwiseAnd]
  exact fld0N (255 : U256) (115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256) x (255 : U256) (by decide +kernel)

/-! ## claimOwnership(): the word `((y & mask160) * 256) | (x & ~(mask160 << 8))` -/

/-- An address word times 256, as a number. -/
theorem toNat_mul256 (p : U256) (hp : p.toNat < 2 ^ 160) :
    (mul p (256 : U256)).toNat = p.toNat * 256 := by
  unfold mul
  rw [BitVec.toNat_mul]
  have h : (256 : U256).toNat = 256 := rfl
  rw [h]
  apply Nat.mod_eq_of_lt
  omega

theorem mul_shr8 (p : U256) (hp : p.toNat < 2 ^ 160) : (mul p (256 : U256)) >>> 8 = p := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_mul256 p hp, Nat.shiftRight_eq_div_pow]
  omega

theorem mul_shr168 (p : U256) (hp : p.toNat < 2 ^ 160) :
    (mul p (256 : U256)) >>> 168 = (0 : U256) := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [BitVec.toNat_ushiftRight, toNat_mul256 p hp, Nat.shiftRight_eq_div_pow, h0]
  apply Nat.div_eq_of_lt
  omega

theorem mul_shr176 (p : U256) (hp : p.toNat < 2 ^ 160) :
    (mul p (256 : U256)) >>> 176 = (0 : U256) := by
  apply BitVec.eq_of_toNat_eq
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [BitVec.toNat_ushiftRight, toNat_mul256 p hp, Nat.shiftRight_eq_div_pow, h0]
  apply Nat.div_eq_of_lt
  omega

theorem and255_mul (p : U256) (hp : p.toNat < 2 ^ 160) :
    (255 : U256) &&& mul p (256 : U256) = (0 : U256) := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (255 : U256).toNat = 2 ^ 8 - 1 := by decide
  have h0 : (0 : U256).toNat = 0 := rfl
  rw [BitVec.toNat_and, toNat_mul256 p hp, h255, h0, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem owner_claim (x y : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (bitwiseOr (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (bitwiseAnd (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x))
      (256 : U256)) = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y := by
  have hp : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y).toNat < 2 ^ 160 := mask_lt y
  have h1 : (1461501637330902918203684832716283019655932542975 : U256) &&& (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256) >>> 8) = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y := by
    rw [mul_shr8 _ hp]
    exact mask_idem y
  simp only [div_256]
  exact (fld (1461501637330902918203684832716283019655932542975 : U256) (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) 0 8 h1
    (by decide +kernel)).trans (or_zero_and _ _)

theorem paused_claim (x y : U256) :
    bitwiseAnd (255 : U256) (div (bitwiseOr (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (bitwiseAnd (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x))
      (95780971304118053647396689196894323976171195136475136 : U256)) = bitwiseAnd (255 : U256) (div x (95780971304118053647396689196894323976171195136475136 : U256)) := by
  have hp : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y).toNat < 2 ^ 160 := mask_lt y
  have h1 : (255 : U256) &&& (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256) >>> 176) = (0 : U256) := by
    rw [mul_shr176 _ hp]
    decide
  simp only [div_176]
  exact (fld (255 : U256) (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x 0 (255 : U256) 176 h1
    (by decide +kernel)).trans (zero_or_and _ _)

theorem minting_claim (x y : U256) :
    bitwiseAnd (255 : U256) (div (bitwiseOr (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (bitwiseAnd (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x))
      (374144419156711147060143317175368453031918731001856 : U256)) = bitwiseAnd (255 : U256) (div x (374144419156711147060143317175368453031918731001856 : U256)) := by
  have hp : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y).toNat < 2 ^ 160 := mask_lt y
  have h1 : (255 : U256) &&& (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256) >>> 168) = (0 : U256) := by
    rw [mul_shr168 _ hp]
    decide
  simp only [div_168]
  exact (fld (255 : U256) (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x 0 (255 : U256) 168 h1
    (by decide +kernel)).trans (zero_or_and _ _)

theorem decimals_claim (x y : U256) :
    bitwiseAnd (255 : U256) (bitwiseOr (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (bitwiseAnd (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x)) =
      bitwiseAnd (255 : U256) x := by
  have hp : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y).toNat < 2 ^ 160 := mask_lt y
  exact (fldN (255 : U256) (mul (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) y) (256 : U256)) (115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256) x 0 (255 : U256) (and255_mul _ hp)
    (by decide +kernel)).trans (zero_or_and _ _)

end WbtcVerify

import TokenKit.Evm.Readable
import TokenKit.Evm.SupplyOpt

/-!
# Facts from the jump conditions of optimized Solidity 0.8 code

The optimizer drops the doubled ISZERO of old code, checks the size of the call data with a
signed comparison, and checks addresses and booleans of the call data for dirty bits. Each
lemma turns one such condition into a fact, for the readable corollaries.

- `size_of_slt`: `ISZERO (SLT (CALLDATASIZE - 4) k)` is not 0: at least `4 + k` bytes.
- `ne_of_isZero0`, `zero_of_cond2z`, `ne_of_cond2z`: a word under one or two ISZERO.
- `eq_of_equal`, `ne_of_equal`, `eq_of_isZero_equal`, `ne_of_isZero_equal`: `EQ a b`.
- `le_of_cond2_gt`: `ISZERO ISZERO (GT a b)` is 0: `a ≤ b`.
- `readable_close08`: closes one conjunct of a readable corollary of such code.

Nothing here is about one token.
-/

namespace TokenKit.Readable

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The check of the size of the call data of Solidity 0.8:
`ISZERO (SLT (CALLDATASIZE - 4) k)` is not 0. -/
theorem size_of_slt {n : Nat} {k : U256} (h4 : 4 ≤ n) (hn : n < 2 ^ 256)
    (hk : k.toNat < 2 ^ 255)
    (h : isZero (signedLessThan (sub (BitVec.ofNat 256 n) (4 : U256)) k) ≠ 0) :
    4 + k.toNat ≤ n := by
  have e : (sub (BitVec.ofNat 256 n) (4 : U256)).toNat = n - 4 := by
    have h4' : (4 : U256).toNat = 4 := rfl
    simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, h4', Nat.mod_eq_of_lt hn]
    omega
  by_cases hlt : U256.toSigned (sub (BitVec.ofNat 256 n) (4 : U256)) < U256.toSigned k
  · exfalso
    apply h
    have e' : signedLessThan (sub (BitVec.ofNat 256 n) (4 : U256)) k = 1 := if_pos hlt
    rw [e']
    decide
  · unfold U256.toSigned at hlt
    rw [e, if_pos hk] at hlt
    split at hlt <;> omega

/-- `ISZERO w` is 0: `w` is not 0. -/
theorem ne_of_isZero0 {w : U256} (h : isZero w = 0) : w ≠ 0 := by
  intro e
  subst e
  exact absurd h (by decide)

/-- `ISZERO ISZERO w` is 0: `w` is 0. -/
theorem zero_of_cond2z {w : U256} (h : isZero (isZero w) = 0) : w = 0 := by
  by_cases e : w = 0
  · exact e
  · exfalso
    have e1 : isZero w = 0 := by unfold isZero; exact if_neg e
    rw [e1] at h
    exact absurd h (by decide)

/-- `ISZERO ISZERO w` is not 0: `w` is not 0. -/
theorem ne_of_cond2z {w : U256} (h : isZero (isZero w) ≠ 0) : w ≠ 0 := by
  intro e
  subst e
  exact h (by decide)

/-- `EQ a b` is not 0. -/
theorem eq_of_equal {a b : U256} (h : equal a b ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exfalso
    apply h
    unfold equal
    exact if_neg e

/-- `EQ a b` is 0. -/
theorem ne_of_equal {a b : U256} (h : equal a b = 0) : a ≠ b := by
  intro e
  subst e
  unfold equal at h
  rw [if_pos rfl] at h
  exact absurd h (by decide)

/-- `ISZERO (EQ a b)` is 0. -/
theorem eq_of_isZero_equal {a b : U256} (h : isZero (equal a b) = 0) : a = b :=
  eq_of_equal (ne_of_isZero0 h)

/-- `ISZERO (EQ a b)` is not 0. -/
theorem ne_of_isZero_equal {a b : U256} (h : isZero (equal a b) ≠ 0) : a ≠ b :=
  ne_of_equal (value_of_cond h)

/-- `require(a <= b)` as optimized: `ISZERO ISZERO (GT a b)` is 0. -/
theorem le_of_cond2_gt {a b : U256} (h : isZero (isZero (greaterThan a b)) = 0) :
    a.toNat ≤ b.toNat := by
  have e := zero_of_cond2z h
  by_cases hgt : a.toNat > b.toNat
  · exfalso
    have e' : greaterThan a b = 1 := if_pos hgt
    rw [e'] at e
    exact absurd e (by decide)
  · omega

end TokenKit.Readable

/-- Closes one conjunct of a readable corollary of optimized Solidity 0.8 code: as
`readable_close`, and also a claim under hypotheses that the facts of the path refute, one side
of a disjunction, and "every other slot keeps its word" for four written slots. -/
macro "readable_close08" : tactic =>
  `(tactic| first
    | (readable_close; done)
    | (intro k h1 h2 h3 h4; simp only [h1, h2, h3, h4, ↓reduceIte]; done)
    | (intros; first
        | (with_reducible contradiction)
        | (exact Or.inl (by with_reducible assumption))
        | (exact Or.inr (by with_reducible assumption))
        | (readable_fin; done)
        | (exfalso; omega))
    | rfl)

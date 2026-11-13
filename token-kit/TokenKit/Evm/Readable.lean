import TokenKit.Evm.Rules
import TokenKit.Evm.Supply

/-!
# From the raw conditions of a path to plain arithmetic

The path theorems state their conditions and results as the terms the opcodes compute. The
lemmas here turn them into facts a reader can check against the source of a token:

- `value_of_cond`, `size_of_cond`, `ne_of_cond`, `add_bound` (with `Supply.le_of_cond_gt`,
  `Supply.sub_fact`, `Supply.add_fact`): the checks solc 0.5 compiles (no value, enough call
  data, an address that is not 0, SafeMath) as equations and inequalities of numbers.
- `storageAt_writeSlot_ite`: the word of a slot after a write, as an `if` on the slot.
- `log3`, `logs_logSub`, `logs_storeSub`, `logs_accessSlot`: the list of logs after a LOG3, an
  SSTORE and an SLOAD.
- `low_byte`: the low byte of a word, as solc 0.5 reads a `uint8` from a slot.
- `eq_of_cond`, `le_of_cond_gt1`, `lt_of_cond_gt1`, `sub_fact1`, `div_one`: the shapes solc 0.4
  compiles for `require(a == b)`, `if (v > a)` and a read of an address at offset 0 of a slot.
- `readable_close`: the tactic that closes one conjunct of a readable corollary.

Nothing here is about one token.
-/

namespace TokenKit.Readable

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The word of slot `m` after a write of `v` in slot `n`. -/
theorem storageAt_writeSlot_ite {S : State.TransactionState} {C : Address} {n m v : U256}
    (h : hasAccount S C) :
    storageAt (writeSlot S C n v) C m = if m = n then v else storageAt S C m := by
  by_cases e : m = n
  · subst e
    rw [if_pos rfl]
    exact storageAt_writeSlot_self h
  · rw [if_neg e]
    exact storageAt_writeSlot_of_ne h e

/-- `require(w != 0)` as compiled: `ISZERO ISZERO ISZERO (EQ w 0)` is not 0. -/
theorem ne_of_cond {w : U256} (h : isZero (isZero (isZero (equal w 0))) ≠ 0) : w ≠ 0 := by
  intro e
  apply h
  subst e
  decide

/-- The check of a function that takes no value: `ISZERO CALLVALUE` is not 0. -/
theorem value_of_cond {w : U256} (h : isZero w ≠ 0) : w = 0 := by
  by_cases e : w = 0
  · exact e
  · exfalso
    apply h
    unfold isZero
    exact if_neg e

/-- The check of the size of the call data: `ISZERO (LT (CALLDATASIZE - 4) k)` is not 0. -/
theorem size_of_cond {n : Nat} {k : U256} (h4 : 4 ≤ n) (hn : n < 2 ^ 256)
    (h : isZero (lessThan (sub (BitVec.ofNat 256 n) (4 : U256)) k) ≠ 0) : 4 + k.toNat ≤ n := by
  by_cases hlt : (sub (BitVec.ofNat 256 n) (4 : U256)).toNat < k.toNat
  · exfalso
    apply h
    have e : lessThan (sub (BitVec.ofNat 256 n) (4 : U256)) k = 1 := if_pos hlt
    rw [e]
    decide
  · have e : (sub (BitVec.ofNat 256 n) (4 : U256)).toNat = n - 4 := by
      have h4' : (4 : U256).toNat = 4 := rfl
      simp only [sub, BitVec.toNat_sub, BitVec.toNat_ofNat, h4', Nat.mod_eq_of_lt hn]
      omega
    omega

/-- After the check of SafeMath `add`, the sum is below `2^256`. -/
theorem add_bound {a v : U256} (h : isZero (isZero (isZero (lessThan (add a v) a))) ≠ 0) :
    a.toNat + v.toNat < 2 ^ 256 := by
  have hle := Supply.le_of_cond_lt h
  have ha := a.isLt
  have hv := v.isLt
  simp only [add, BitVec.toNat_add] at hle
  omega

/-- The low byte of a word, as solc 0.5 reads a `uint8` at offset 0 of a slot. -/
theorem low_byte (w : U256) :
    bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) (div w (1 : U256)))) =
      BitVec.ofNat 256 (w.toNat % 256) := by
  have hd : div w (1 : U256) = w := by
    unfold div
    rw [if_neg (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp
  have ha : ∀ x : U256, (bitwiseAnd (255 : U256) x).toNat = x.toNat % 256 := by
    intro x
    simp only [bitwiseAnd, BitVec.toNat_and]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 8
  rw [hd]
  apply BitVec.eq_of_toNat_eq
  rw [ha, ha, ha, BitVec.toNat_ofNat]
  have := w.isLt
  omega

/-- `require(a == b)` as compiled: `ISZERO ISZERO (EQ a b)` is not 0. -/
theorem eq_of_cond {a b : U256} (h : isZero (isZero (equal a b)) ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exfalso
    apply h
    have e' : equal a b = 0 := by unfold equal; exact if_neg e
    rw [e']
    decide

/-- `if (v > a)` as compiled, not taken: `ISZERO (GT v a)` is not 0. -/
theorem le_of_cond_gt1 {v a : U256} (h : isZero (greaterThan v a) ≠ 0) : v.toNat ≤ a.toNat := by
  by_cases hgt : v.toNat > a.toNat
  · exfalso
    apply h
    have e : greaterThan v a = 1 := if_pos hgt
    rw [e]
    decide
  · omega

/-- `if (v > a)` as compiled, taken: `ISZERO (GT v a)` is 0. -/
theorem lt_of_cond_gt1 {v a : U256} (h : isZero (greaterThan v a) = 0) : a.toNat < v.toNat := by
  by_cases hgt : v.toNat > a.toNat
  · exact hgt
  · exfalso
    have e : greaterThan v a = 0 := if_neg hgt
    rw [e] at h
    exact absurd h (by decide)

/-- When `v > a` is false, `a - v` does not wrap. -/
theorem sub_fact1 {v a : U256} (h : isZero (greaterThan v a) ≠ 0) :
    ((sub a v).toNat : Int) = a.toNat - v.toNat := by
  have hle := le_of_cond_gt1 h
  have ha := a.isLt
  have hv := v.isLt
  have e : (sub a v).toNat = a.toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  omega

/-- A division by 1, as solc 0.4 reads an address at offset 0 of a slot. -/
theorem div_one (w : U256) : div w (1 : U256) = w := by
  unfold div
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp

theorem toNat_zero : (0 : U256).toNat = 0 := rfl

/-- `a == b` as a jump condition (`ISZERO ISZERO (EQ a b)`), when it is not 0. -/
theorem eq_of_cond2 {a b : U256} (h : isZero (isZero (equal a b)) ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exfalso
    apply h
    unfold equal
    rw [if_neg e]
    decide

/-- `a == b` as a jump condition (`ISZERO ISZERO (EQ a b)`), when it is 0. -/
theorem ne_of_cond2 {a b : U256} (h : isZero (isZero (equal a b)) = 0) : a ≠ b := by
  intro e
  subst e
  unfold equal at h
  rw [if_pos rfl] at h
  exact absurd h (by decide)

/-- A log of the contract `C` with two topics. -/
abbrev log2 (C : Address) (t1 t2 : U256) (data : ByteArray) : Blocks.Log :=
  { address := C
    topics := [U256.toBeBytes t1, U256.toBeBytes t2]
    data := data }

theorem logs_logSub2 (ss : Substate) (C : Address) (t1 t2 : U256) (d : ByteArray) :
    (logSub2 ss C t1 t2 d).logs = ss.logs.push (log2 C t1 t2 d) := rfl

/-- A log of the contract `C` with three topics. -/
abbrev log3 (C : Address) (t1 t2 t3 : U256) (data : ByteArray) : Blocks.Log :=
  { address := C
    topics := [U256.toBeBytes t1, U256.toBeBytes t2, U256.toBeBytes t3]
    data := data }

theorem logs_logSub (ss : Substate) (C : Address) (t1 t2 t3 : U256) (d : ByteArray) :
    (logSub ss C t1 t2 t3 d).logs = ss.logs.push (log3 C t1 t2 t3 d) := rfl

theorem logs_storeSub (fork : Fork) (ss : Substate) (C : Address) (n o c v : U256) :
    (storeSub fork ss C n o c v).logs = ss.logs := rfl

theorem logs_accessSlot (ss : Substate) (C : Address) (n : U256) :
    (accessSlot ss C n).logs = ss.logs := rfl

end TokenKit.Readable

/-- Closes a goal of numbers or words from the hypotheses. -/
macro "readable_fin" : tactic =>
  `(tactic| first
    | (exact True.intro)
    | (with_reducible assumption)
    | omega
    | (with_reducible rfl)
    | (apply BitVec.eq_of_toNat_eq; omega)
    | (refine ⟨?_, ?_⟩ <;> first
        | (with_reducible assumption) | omega | (with_reducible rfl)
        | (apply BitVec.eq_of_toNat_eq; omega)))

/-- Closes one conjunct of a readable corollary: a fact of the context, arithmetic, a case that
cannot happen, or "every other slot keeps its word". -/
macro "readable_close" : tactic =>
  `(tactic| first
    | (readable_fin; done)
    | (intro k h1 h2 h3; simp only [h1, h2, h3, ↓reduceIte]; done)
    | (intro k h1 h2; simp only [h1, h2, ↓reduceIte]; done)
    | (intro k h1; simp only [h1, ↓reduceIte]; done)
    | (intro h; first
        | (with_reducible exact absurd rfl h) | (exact False.elim h)
        | (with_reducible contradiction) | (readable_fin; done))
    | (intro h1 h2; first
        | (with_reducible contradiction) | (exact False.elim h1) | (exact False.elim h2)
        | (readable_fin; done))
    | (intros; exact True.intro))

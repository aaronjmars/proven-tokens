import TokenKit.Evm.Supply
import TokenKit.Evm.Supply2
import TokenKit.Evm.SupplyOpt

/-!
# Unchecked arithmetic on balances, from the supply invariant

Solidity 0.8 code may add to a balance or subtract from the total supply inside `unchecked`
(SKY; OpenZeppelin ERC20 from 4.x does the same): the bytecode has no check there. The sum cannot
wrap all the same, because one balance is at most the sum of all balances, and that sum is the
total supply, a word. So the exact effect follows from the invariant, not from a branch.

- `bal_le_D`: one balance is at most the sum of all balances (`D` plus the total supply).
- `le_D_of_cond`: after `require(balance >= v)`, `v` is at most that sum.
- `add_bal_bound`: `v + balance` does not wrap when the sum of all balances plus `v` is below
  `2^256` (a conditional rewrite rule: the invariant proofs discharge the bound).
- `sub_toNat_le`: `a - v` does not wrap when `v ≤ a`.
- `add_sub_self`: `v + (a - v)` is `a`, as words.
- `add_bound_gt`, `add_fact_gt`, `add_nat_gt`: the checked addition of Solidity 0.8 compiled as
  `ISZERO (GT a (ADD v a))`.

Nothing here is about one token.
-/

namespace TokenKit.Supply

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

variable {b t : U256} {C : Address} {S : State.TransactionState}

theorem sumTo_nonneg {f : Nat → Int} (hf : ∀ i, 0 ≤ f i) : ∀ n, 0 ≤ sumTo f n
  | 0 => Int.le_refl 0
  | n + 1 => by
    have h1 := sumTo_nonneg hf n
    have h2 := hf n
    rw [sumTo]
    omega

/-- One term of a sum of terms that are not negative is at most the sum. -/
theorem le_sumTo {f : Nat → Int} (hf : ∀ i, 0 ≤ f i) {a : Nat} :
    ∀ n, a < n → f a ≤ sumTo f n
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [sumTo]
    have h2 := hf n
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | h'
    · have h1 := le_sumTo hf n h'
      omega
    · subst h'
      have h1 := sumTo_nonneg hf a
      omega

/-- The balance of an address word is at most the sum of all balances. -/
theorem bal_le_sumBal {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((storageAt S C (mapSlot x b)).toNat : Int) ≤ sumBal b C S := by
  have h := le_sumTo (f := bal b C S) (fun i => Int.natCast_nonneg _) (2 ^ 160) hx
  simp only [bal, ofNat_toNat] at h
  exact h

/-- The balance of an address word is at most `D` plus the total supply. -/
theorem bal_le_D {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((storageAt S C (mapSlot x b)).toNat : Int) ≤ D b t C S + (storageAt S C t).toNat := by
  have h := bal_le_sumBal (b := b) (C := C) (S := S) hx
  unfold D
  omega

/-- After `require(balance >= v)`, `v` is at most `D` plus the total supply. -/
theorem le_D_of_cond {x v : U256}
    (h : isZero (lessThan (storageAt S C (mapSlot x b)) v) ≠ 0) (hx : x.toNat < 2 ^ 160) :
    (v.toNat : Int) ≤ D b t C S + (storageAt S C t).toNat := by
  have h1 := le_of_cond_lt1 h
  have h2 := bal_le_D (b := b) (t := t) (C := C) (S := S) hx
  omega

/-- `v + balance` does not wrap when the sum of all balances plus `v` is below `2^256`. -/
theorem add_bal_bound {x v : U256} (hx : x.toNat < 2 ^ 160)
    (hb : D b t C S + (storageAt S C t).toNat + v.toNat < 2 ^ 256) :
    (add v (storageAt S C (mapSlot x b))).toNat =
      v.toNat + (storageAt S C (mapSlot x b)).toNat := by
  have h2 := bal_le_D (b := b) (t := t) (C := C) (S := S) hx
  simp only [add, BitVec.toNat_add]
  omega

/-- `a - v` does not wrap when `v ≤ a`. -/
theorem sub_toNat_le {a v : U256} (h : v.toNat ≤ a.toNat) :
    (sub a v).toNat = a.toNat - v.toNat := by
  have ha := a.isLt
  have hv := v.isLt
  simp only [sub, BitVec.toNat_sub]
  omega

/-- The check `ISZERO (GT a (ADD v a))` of a Solidity 0.8 addition (the sum is not below one of
its terms): the sum is below `2^256`. -/
theorem add_bound_gt {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    a.toNat + v.toNat < 2 ^ 256 := by
  have hle := le_of_cond_gt1 h
  have ha := a.isLt
  have hv := v.isLt
  simp only [add, BitVec.toNat_add] at hle
  omega

/-- After that check, the sum `v + a` does not wrap. -/
theorem add_fact_gt {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    ((add v a).toNat : Int) = v.toNat + a.toNat := by
  have hb := add_bound_gt h
  have e : (add v a).toNat = v.toNat + a.toNat := by
    simp only [add, BitVec.toNat_add]
    omega
  rw [e]
  omega

/-- The same as a fact about natural numbers. -/
theorem add_nat_gt {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    (add v a).toNat = v.toNat + a.toNat := by
  have hb := add_bound_gt h
  simp only [add, BitVec.toNat_add]
  omega

/-- `v + (a - v)` is `a`, as words: what an unchecked transfer to oneself leaves. -/
theorem add_sub_self (a v : U256) : add v (sub a v) = a := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hv := v.isLt
  simp only [add, sub, BitVec.toNat_add, BitVec.toNat_sub]
  omega

end TokenKit.Supply

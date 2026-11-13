import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt

/-!
# Unchecked balance arithmetic: what the supply invariant gives

OpenZeppelin ERC20 from 4.8 (USDe, ENA) adds to the balance of the receiver and subtracts from
the total supply inside `unchecked` blocks: the bytecode has no overflow test there, because the
invariant "the sum of all balances is the total supply" excludes the overflow. So the proof that
a call keeps the invariant has to use the invariant at these two places. The shared library has
the lemmas for checked arithmetic only; these are the missing ones. Nothing here is about one
token (see `status.json`, `to_merge_into_kit`).

- `sumTo_nonneg`, `le_sumTo`, `two_le_sumTo`: a sum of terms that are not negative is not
  negative, is at least each term, and at least each two terms.
- `bal_le_sumBal`, `two_bal_le_sumBal`: so one balance, and two balances of two different
  address words, are at most the sum of all balances. No hypothesis on keccak: the sum is over
  address numbers, not over slots.
- `add_bal_inv`: if `D + v ≤ 0` in a state (`D`: the sum of the balances minus the total
  supply), the unchecked `balance + v` read in that state does not wrap.
- `sub_tot_inv`: if `D + v ≤ 0` in a state, the unchecked `totalSupply - v` does not wrap.
- `add_bound_gtc`, `add_nat_gtc`, `add_fact_gtc`: the checked addition of Solidity 0.8.19 with
  the optimizer on, compiled as `ISZERO (GT a (ADD v a))`.
- `inv_bal_le`, `inv_two_bal_le`: under the invariant, a balance is at most the total supply and
  so are two balances of two different address words together.
-/

namespace TokenKit.Supply

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

theorem sumTo_nonneg {f : Nat → Int} (h : ∀ i, 0 ≤ f i) : ∀ n, 0 ≤ sumTo f n
  | 0 => Int.le_refl 0
  | n + 1 => by
    rw [sumTo]
    have h1 := sumTo_nonneg h n
    have h2 := h n
    omega

theorem le_sumTo {f : Nat → Int} (h : ∀ i, 0 ≤ f i) {a : Nat} :
    ∀ n, a < n → f a ≤ sumTo f n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    rw [sumTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with h' | h'
    · have h1 := le_sumTo h n h'
      have h2 := h n
      omega
    · subst h'
      have h1 := sumTo_nonneg h a
      omega

theorem two_le_sumTo {f : Nat → Int} (h : ∀ i, 0 ≤ f i) {a b : Nat} (hab : a < b) :
    ∀ n, b < n → f a + f b ≤ sumTo f n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    rw [sumTo]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with h' | h'
    · have h1 := two_le_sumTo h hab n h'
      have h2 := h n
      omega
    · subst h'
      have h1 := le_sumTo h b hab
      omega

variable {b t : U256} {C : Address} {S : State.TransactionState}

theorem bal_nonneg (i : Nat) : 0 ≤ bal b C S i := Int.natCast_nonneg _

/-- The term of the sum at the number of an address word is the balance word of that word. -/
theorem bal_at (x : U256) :
    bal b C S x.toNat = ((storageAt S C (mapSlot x b)).toNat : Int) := by
  show ((storageAt S C (mapSlot (BitVec.ofNat 256 x.toNat) b)).toNat : Int) = _
  rw [ofNat_toNat]

/-- One balance is at most the sum of all balances. -/
theorem bal_le_sumBal {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((storageAt S C (mapSlot x b)).toNat : Int) ≤ sumBal b C S := by
  rw [← bal_at (b := b) (C := C) (S := S) x]
  exact le_sumTo (fun i => bal_nonneg i) _ hx

/-- The balances of two different address words are together at most the sum of all balances. -/
theorem two_bal_le_sumBal {x y : U256} (hx : x.toNat < 2 ^ 160) (hy : y.toNat < 2 ^ 160)
    (hne : x ≠ y) :
    ((storageAt S C (mapSlot x b)).toNat : Int) + (storageAt S C (mapSlot y b)).toNat ≤
      sumBal b C S := by
  have hn : x.toNat ≠ y.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  rw [← bal_at (b := b) (C := C) (S := S) x, ← bal_at (b := b) (C := C) (S := S) y]
  rcases Nat.lt_or_gt_of_ne hn with h | h
  · exact two_le_sumTo (fun i => bal_nonneg i) h _ hy
  · have h1 := two_le_sumTo (f := bal b C S) (fun i => bal_nonneg i) h _ hx
    unfold sumBal
    omega

/-- The sum of all balances is not negative. -/
theorem sumBal_nonneg : 0 ≤ sumBal b C S := sumTo_nonneg (fun i => bal_nonneg i) _

/-- An unchecked `balances[x] += v`: when the sum of the balances minus the total supply is at
most `-v` in the state `S`, the new word does not wrap. -/
theorem add_bal_inv {x v : U256} (hx : x.toNat < 2 ^ 160)
    (hD : D b t C S + (v.toNat : Int) ≤ 0) :
    ((add v (storageAt S C (mapSlot x b))).toNat : Int) =
      v.toNat + (storageAt S C (mapSlot x b)).toNat := by
  have h1 := bal_le_sumBal (b := b) (C := C) (S := S) hx
  have ht := (storageAt S C t).isLt
  unfold D at hD
  have hb : v.toNat + (storageAt S C (mapSlot x b)).toNat < 2 ^ 256 := by omega
  have e : (add v (storageAt S C (mapSlot x b))).toNat =
      v.toNat + (storageAt S C (mapSlot x b)).toNat := by
    simp only [add, BitVec.toNat_add]
    omega
  rw [e]
  omega

/-- An unchecked `totalSupply -= v`: when the sum of the balances minus the total supply is at
most `-v` in the state `S`, the new word does not wrap. -/
theorem sub_tot_inv {v : U256} (hD : D b t C S + (v.toNat : Int) ≤ 0) :
    ((sub (storageAt S C t) v).toNat : Int) = (storageAt S C t).toNat - v.toNat := by
  have h0 := sumBal_nonneg (b := b) (C := C) (S := S)
  unfold D at hD
  have hle : v.toNat ≤ (storageAt S C t).toNat := by omega
  have ha := (storageAt S C t).isLt
  have hv := v.isLt
  have e : (sub (storageAt S C t) v).toNat = (storageAt S C t).toNat - v.toNat := by
    simp only [sub, BitVec.toNat_sub]
    omega
  rw [e]
  omega

/-- The check of `a + v` of Solidity 0.8.19 with the optimizer on, `ISZERO (GT a (ADD v a))`:
the sum is below `2^256`. -/
theorem add_bound_gtc {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    v.toNat + a.toNat < 2 ^ 256 := by
  have hle := le_of_cond_gt1 h
  have ha := a.isLt
  have hv := v.isLt
  simp only [add, BitVec.toNat_add] at hle
  omega

/-- After that check, the sum does not wrap. -/
theorem add_nat_gtc {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    (add v a).toNat = v.toNat + a.toNat := by
  have hb := add_bound_gtc h
  simp only [add, BitVec.toNat_add]
  omega

/-- The same over the integers. -/
theorem add_fact_gtc {a v : U256} (h : isZero (greaterThan a (add v a)) ≠ 0) :
    ((add v a).toNat : Int) = v.toNat + a.toNat := by
  rw [add_nat_gtc h]
  omega

/-- Under the invariant, a balance is at most the total supply. -/
theorem inv_bal_le {x : U256} (hx : x.toNat < 2 ^ 160) (h : Inv b t C S) :
    (storageAt S C (mapSlot x b)).toNat ≤ (storageAt S C t).toNat := by
  have h1 := bal_le_sumBal (b := b) (C := C) (S := S) hx
  unfold Inv D at h
  omega

/-- Under the invariant, the balances of two different address words are together at most the
total supply: so an unchecked `balances[to] += amount` after `balances[from] -= amount` cannot
wrap. -/
theorem inv_two_bal_le {x y : U256} (hx : x.toNat < 2 ^ 160) (hy : y.toNat < 2 ^ 160)
    (hne : x ≠ y) (h : Inv b t C S) :
    (storageAt S C (mapSlot x b)).toNat + (storageAt S C (mapSlot y b)).toNat ≤
      (storageAt S C t).toNat := by
  have h1 := two_bal_le_sumBal (b := b) (C := C) (S := S) hx hy hne
  unfold Inv D at h
  omega

end TokenKit.Supply

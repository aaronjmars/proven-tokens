import TokenKit.Seq.Tx
import TokenKit.Evm.Supply
import TokenKit.Evm.Supply2
import TokenKit.Evm.SupplyMask

/-!
# The supply invariants of the kit meet the interface of `TokenKit.Seq`

GENERIC kit file: nothing here is about one token. For each of the three supply invariants of
the kit it proves the two facts that `Seq/Tx.lean` asks of the invariant of a token:

- `Seq.StorageOnly C (Inv ...)`: the invariant reads the storage words of `C` only;
- `Seq.ZeroBase C (Inv ...)`: the base case, a state where every storage word of `C` is zero
  satisfies the invariant.

The invariants: `Supply.Inv b t` (sum of the balances at base slot `b` = the word at slot `t`),
`Supply.Inv2 b1 b2 t` (two balance mappings), `SupplyMask.Inv m b t` (balances under a mask).
A token whose `Inv` is an `abbrev` of one of them gets both facts in one line each.
-/

set_option autoImplicit false

namespace TokenKit.Seq

open UsdtVerify
open EthLib.Base (U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.State (TransactionState)

/-- A sum of zeros is zero. -/
theorem sumTo_zero (f : Nat → Int) : ∀ n, (∀ i, i < n → f i = 0) → Supply.sumTo f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [Supply.sumTo, sumTo_zero f n (fun i hi => h i (by omega)), h n (by omega)]
    rfl

/-- A state with the storage words of `S` at `C` has the words of `S` at every slot number. -/
theorem storageAt_of_getStorage {C : Address} {S S' : TransactionState}
    (h : ∀ k, S'.getStorage C k = S.getStorage C k) (n : U256) :
    storageAt S' C n = storageAt S C n := h _

/-- All-zero storage, read at a slot number. -/
theorem storageAt_of_zero {C : Address} {S : TransactionState}
    (h0 : ∀ k, S.getStorage C k = 0) (n : U256) : storageAt S C n = 0 := h0 _

/-! ## `Supply.Inv` -/

/-- The sum of the balances reads the storage of `C` only. -/
theorem sumBal_congr {b : U256} {C : Address} {S S' : TransactionState}
    (h : ∀ k, S'.getStorage C k = S.getStorage C k) :
    Supply.sumBal b C S' = Supply.sumBal b C S := by
  unfold Supply.sumBal
  exact Supply.sumTo_congr _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [storageAt_of_getStorage h])

/-- The sum of the balances of all-zero storage is zero. -/
theorem sumBal_zero {b : U256} {C : Address} {S : TransactionState}
    (h0 : ∀ k, S.getStorage C k = 0) : Supply.sumBal b C S = 0 := by
  unfold Supply.sumBal
  exact sumTo_zero _ _ (fun i _ => by
    show ((storageAt S C _).toNat : Int) = 0
    rw [storageAt_of_zero h0]
    rfl)

/-- `Supply.Inv b t C` reads the storage words of `C` only. -/
theorem storageOnly_supply (b t : U256) (C : Address) : StorageOnly C (Supply.Inv b t C) := by
  intro S S' h hI
  unfold Supply.Inv Supply.D at hI ⊢
  rw [sumBal_congr h, storageAt_of_getStorage h]
  exact hI

/-- `Supply.Inv b t C` holds when every storage word of `C` is zero. -/
theorem zeroBase_supply (b t : U256) (C : Address) : ZeroBase C (Supply.Inv b t C) := by
  intro S h0
  unfold Supply.Inv Supply.D
  rw [sumBal_zero h0, storageAt_of_zero h0]
  rfl

/-! ## `Supply.Inv2` -/

/-- `Supply.Inv2 b1 b2 t C` reads the storage words of `C` only. -/
theorem storageOnly_supply2 (b1 b2 t : U256) (C : Address) :
    StorageOnly C (Supply.Inv2 b1 b2 t C) := by
  intro S S' h hI
  unfold Supply.Inv2 Supply.D2 at hI ⊢
  rw [sumBal_congr h, sumBal_congr h, storageAt_of_getStorage h]
  exact hI

/-- `Supply.Inv2 b1 b2 t C` holds when every storage word of `C` is zero. -/
theorem zeroBase_supply2 (b1 b2 t : U256) (C : Address) :
    ZeroBase C (Supply.Inv2 b1 b2 t C) := by
  intro S h0
  unfold Supply.Inv2 Supply.D2
  rw [sumBal_zero h0, sumBal_zero h0, storageAt_of_zero h0]
  rfl

/-! ## `SupplyMask.Inv` -/

/-- The sum of the masked balances reads the storage of `C` only. -/
theorem sumBalMask_congr {m b : U256} {C : Address} {S S' : TransactionState}
    (h : ∀ k, S'.getStorage C k = S.getStorage C k) :
    SupplyMask.sumBal m b C S' = SupplyMask.sumBal m b C S := by
  unfold SupplyMask.sumBal
  exact Supply.sumTo_congr _ (fun i _ => by
    show ((bitwiseAnd m (storageAt S' C _)).toNat : Int) =
      ((bitwiseAnd m (storageAt S C _)).toNat : Int)
    rw [storageAt_of_getStorage h])

/-- A mask of the zero word is the zero word. -/
theorem bitwiseAnd_zero_right (m : U256) : bitwiseAnd m 0 = 0 := by
  simp [bitwiseAnd]

/-- The sum of the masked balances of all-zero storage is zero. -/
theorem sumBalMask_zero {m b : U256} {C : Address} {S : TransactionState}
    (h0 : ∀ k, S.getStorage C k = 0) : SupplyMask.sumBal m b C S = 0 := by
  unfold SupplyMask.sumBal
  exact sumTo_zero _ _ (fun i _ => by
    show ((bitwiseAnd m (storageAt S C _)).toNat : Int) = 0
    rw [storageAt_of_zero h0, bitwiseAnd_zero_right]
    rfl)

/-- `SupplyMask.Inv m b t C` reads the storage words of `C` only. -/
theorem storageOnly_supplyMask (m b t : U256) (C : Address) :
    StorageOnly C (SupplyMask.Inv m b t C) := by
  intro S S' h hI
  unfold SupplyMask.Inv SupplyMask.D at hI ⊢
  rw [sumBalMask_congr h, storageAt_of_getStorage h]
  exact hI

/-- `SupplyMask.Inv m b t C` holds when every storage word of `C` is zero. -/
theorem zeroBase_supplyMask (m b t : U256) (C : Address) :
    ZeroBase C (SupplyMask.Inv m b t C) := by
  intro S h0
  unfold SupplyMask.Inv SupplyMask.D
  rw [sumBalMask_zero h0, storageAt_of_zero h0]
  rfl

end TokenKit.Seq

import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt

/-!
# The supply invariant of PEPE and the hypothesis on keccak it needs

The storage of PEPE, as the bytecode reads it: `_owner` in slot 0, `_balances[a]` in slot
`mapSlot a 1`, `_allowances[o][s]` in slot `mapSlot s (mapSlot o 2)`, `_totalSupply` in slot 3,
`limited` in the low byte of slot 6, `maxHoldingAmount` in slot 7, `minHoldingAmount` in slot 8,
`uniswapV2Pair` in slot 9, `blacklists[a]` in the low byte of slot `mapSlot a 10`.

- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` equals the word of slot 3.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: slot 3 is the balance slot of no
  address; the balance slot of a word of `A` is the balance slot of no other address; an
  allowance slot keyed by two words of `A` is no balance slot and is not slot 3; the blacklist
  slot of a word of `A` is no balance slot and is not slot 3; none of the slots 0, 6, 7, 8, 9 is
  a balance slot. Finitely many facts, each about one given slot against the 2^160 balance slots
  (it follows upstream's `SepOn`, UsdtVerify/Usdt/Invariant/Supply.lean).
-/

namespace PepeVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of PEPE: the sum of all balances (base slot 1) is `_totalSupply` (slot 3). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv 1 3 C S

/-- The mask of an address, as the bytecode builds it (`(1 << 160) - 1`). -/
theorem mask_idem (w : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

theorem mask_lt (w : U256) :
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat < 2 ^ 160 := by
  simp only [bitwiseAnd, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

/-- The address words a call can use as mapping keys. -/
def callKeys {fork : Fork} (message : Message fork) : List U256 :=
  [bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256,
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32)]

/-- The separation of slots for the address words of `A` (a hypothesis about keccak). -/
structure Sep (A : List U256) : Prop where
  /-- Slot 3 (`_totalSupply`) is the balance slot of no address. -/
  total : Supply.NotBal 1 3
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 1 x
  /-- An allowance slot keyed by two words of `A` is no balance slot and is not slot 3. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 1 (mapSlot s (mapSlot o 2)) ∧ mapSlot s (mapSlot o 2) ≠ 3
  /-- The blacklist slot of a word of `A` is no balance slot and is not slot 3. -/
  black : ∀ x ∈ A, Supply.NotBal 1 (mapSlot x 10) ∧ mapSlot x 10 ≠ 3
  /-- The slots of `_owner`, `limited`, `maxHoldingAmount`, `minHoldingAmount` and
  `uniswapV2Pair` are balance slots of no address. -/
  fixed : Supply.NotBal 1 0 ∧ Supply.NotBal 1 6 ∧ Supply.NotBal 1 7 ∧ Supply.NotBal 1 8 ∧
    Supply.NotBal 1 9

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a masked word of `A`. -/
theorem D_bal (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 1) v) =
      Supply.D 1 3 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 1)).toNat +
        v.toNat :=
  Supply.D_write_bal hacc (hsep.uniq _ hx) (mask_lt w) hsep.total v

/-- A write of `_totalSupply`. -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 3 v) =
      Supply.D 1 3 C S + (storageAt S C 3).toNat - v.toNat :=
  Supply.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C (mapSlot s (mapSlot o 2)) v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2 v

/-- A write of the blacklist flag of a word of `A`. -/
theorem D_black (hsep : Sep A) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C (mapSlot x 10) v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc (hsep.black x hx).1 (hsep.black x hx).2 v

/-- A write of `_owner` (slot 0). -/
theorem D_owner (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 0 v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc hsep.fixed.1 (by decide) v

/-- A write of `limited` (slot 6). -/
theorem D_limited (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 6 v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc hsep.fixed.2.1 (by decide) v

/-- A write of `maxHoldingAmount` (slot 7). -/
theorem D_max (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 7 v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc hsep.fixed.2.2.1 (by decide) v

/-- A write of `minHoldingAmount` (slot 8). -/
theorem D_min (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 8 v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc hsep.fixed.2.2.2.1 (by decide) v

/-- A write of `uniswapV2Pair` (slot 9). -/
theorem D_pair (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 1 3 C (writeSlot S C 9 v) = Supply.D 1 3 C S :=
  Supply.D_write_other hacc hsep.fixed.2.2.2.2 (by decide) v

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Pepe/Readable.lean`): under `Sep A`, an equation
between two slots a call uses is an equation between their keys, or is false. -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 1 = mapSlot x 1) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_tot_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((3 : U256) = mapSlot x 1) = False :=
  eq_false (hsep.total x hx)

theorem slot_bal_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 1 = (3 : U256)) = False :=
  eq_false (fun e => hsep.total x hx e.symm)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 2) = mapSlot x 1) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 1 = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 2) = (3 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((3 : U256) = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2 e.symm)

end PepeVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word below `2^160`, or
that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact PepeVerify.mask_lt _
    | supply_side)

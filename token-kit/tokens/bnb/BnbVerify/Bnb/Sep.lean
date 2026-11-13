import TokenKit.Evm.Supply2

/-!
# The supply invariant of BNB and the hypothesis on keccak it needs

The storage of BNB, as the bytecode reads it: `totalSupply` in slot 3, `balanceOf[a]` in slot
`mapSlot a 5`, `freezeOf[a]` in slot `mapSlot a 6`, `allowance[o][s]` in slot
`mapSlot s (mapSlot o 7)`.

- `Inv C S`: in the state `S`, the sum of the `balanceOf` words of the 2^160 addresses of the
  contract `C`, plus the sum of their `freezeOf` words, equals the word of slot 3. The two sums
  are sums of natural numbers (no wrap); the equation is between integers.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved. For SHIB it had three parts; the
  second mapping adds the parts marked (new):
  - slot 3 is the `balanceOf` slot of no address, and (new) the `freezeOf` slot of no address;
  - the `balanceOf` slot of a word of `A` is the `balanceOf` slot of no other address, and (new)
    the same for `freezeOf`;
  - (new) the `balanceOf` slot of a word of `A` is the `freezeOf` slot of no address, and the
    `freezeOf` slot of a word of `A` is the `balanceOf` slot of no address;
  - an allowance slot keyed by two words of `A` is no `balanceOf` slot, (new) no `freezeOf`
    slot, and is not slot 3.
-/

namespace BnbVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of BNB: the sum of all `balanceOf` (base slot 5) plus the sum of all `freezeOf`
(base slot 6) is `totalSupply` (slot 3). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv2 5 6 3 C S

/-- The mask of an address, as the bytecode pushes it (PUSH20 of 20 bytes 0xff). -/
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
  /-- Slot 3 (`totalSupply`) is the `balanceOf` slot of no address. -/
  totalBal : Supply.NotBal 5 3
  /-- Slot 3 (`totalSupply`) is the `freezeOf` slot of no address. -/
  totalFrz : Supply.NotBal 6 3
  /-- The `balanceOf` slot of a word of `A` is the `balanceOf` slot of no other address. -/
  uniqBal : ∀ x ∈ A, Supply.UniqBal 5 x
  /-- The `freezeOf` slot of a word of `A` is the `freezeOf` slot of no other address. -/
  uniqFrz : ∀ x ∈ A, Supply.UniqBal 6 x
  /-- The `balanceOf` slot of a word of `A` is the `freezeOf` slot of no address. -/
  balFrz : ∀ x ∈ A, Supply.NotBal 6 (mapSlot x 5)
  /-- The `freezeOf` slot of a word of `A` is the `balanceOf` slot of no address. -/
  frzBal : ∀ x ∈ A, Supply.NotBal 5 (mapSlot x 6)
  /-- An allowance slot keyed by two words of `A` is no `balanceOf` slot, no `freezeOf` slot,
  and is not slot 3. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 5 (mapSlot s (mapSlot o 7)) ∧ Supply.NotBal 6 (mapSlot s (mapSlot o 7)) ∧
      mapSlot s (mapSlot o 7) ≠ 3

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the `balanceOf` word of a masked word of `A`. -/
theorem D_bal (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D2 5 6 3 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 5) v) =
      Supply.D2 5 6 3 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 5)).toNat +
        v.toNat :=
  Supply.D2_write_bal1 hacc (hsep.uniqBal _ hx) (mask_lt w) (hsep.balFrz _ hx) hsep.totalBal v

/-- A write of the `freezeOf` word of a masked word of `A`. -/
theorem D_frz (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D2 5 6 3 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 6) v) =
      Supply.D2 5 6 3 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 6)).toNat +
        v.toNat :=
  Supply.D2_write_bal2 hacc (hsep.uniqFrz _ hx) (mask_lt w) (hsep.frzBal _ hx) hsep.totalFrz v

/-- A write of `totalSupply`. -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D2 5 6 3 C (writeSlot S C 3 v) = Supply.D2 5 6 3 C S + (storageAt S C 3).toNat - v.toNat :=
  Supply.D2_write_tot hacc hsep.totalBal hsep.totalFrz v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D2 5 6 3 C (writeSlot S C (mapSlot s (mapSlot o 7)) v) = Supply.D2 5 6 3 C S :=
  Supply.D2_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2.1
    (hsep.allow o ho s hs).2.2 v

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Bnb/Readable.lean`): under `Sep A`, an equation
between two slots a call uses is an equation between their keys, or is false. -/

/-- Two `balanceOf` slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 5 = mapSlot x 5) = (y = x) :=
  propext ⟨fun e => hsep.uniqBal x hx y hy e, fun e => by rw [e]⟩

theorem slot_bal_frz (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot x 5 = mapSlot y 6) = False :=
  eq_false (hsep.balFrz x hx y hy)

theorem slot_frz_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 6 = mapSlot x 5) = False :=
  eq_false (fun e => hsep.balFrz x hx y hy e.symm)

theorem slot_tot_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((3 : U256) = mapSlot x 5) = False :=
  eq_false (hsep.totalBal x hx)

theorem slot_bal_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 5 = (3 : U256)) = False :=
  eq_false (fun e => hsep.totalBal x hx e.symm)

theorem slot_tot_frz (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((3 : U256) = mapSlot x 6) = False :=
  eq_false (hsep.totalFrz x hx)

theorem slot_frz_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 6 = (3 : U256)) = False :=
  eq_false (fun e => hsep.totalFrz x hx e.symm)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 7) = mapSlot x 5) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 5 = mapSlot s (mapSlot o 7)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 7) = (3 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2.2

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((3 : U256) = mapSlot s (mapSlot o 7)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2.2 e.symm)

end BnbVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word below `2^160`, or
that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact BnbVerify.mask_lt _
    | supply_side)

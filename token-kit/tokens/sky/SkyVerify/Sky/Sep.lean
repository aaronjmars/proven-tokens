import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Opt06
import TokenKit.Evm.SupplyUnchecked

/-!
# The supply invariant of SKY and the hypothesis on keccak it needs

The storage of SKY, as the bytecode reads it: `wards[a]` in slot `mapSlot a 0`, `totalSupply` in
slot 1, `balanceOf[a]` in slot `mapSlot a 2`, `allowance[o][s]` in slot
`mapSlot s (mapSlot o 3)`, `nonces[a]` in slot `mapSlot a 4`. No other slot is used.

- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` equals the word of slot 1.
- `callKeys message`: the address words a call can use as mapping keys: the caller (its word has
  no bit above the address, so the bytecode uses it with or without a mask) and the first two
  argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: slot 1 is the balance slot of no
  address; the balance slot of a word of `A` is the balance slot of no other address; an
  allowance slot keyed by two words of `A` is no balance slot and is not slot 1; the `wards` slot
  and the `nonces` slot of a word of `A` are no balance slot and are not slot 1; an allowance
  slot keyed by two words of `A` is the `nonces` slot of no word of `A`. Finitely many facts,
  each about one given slot against the 2^160 balance slots or against one other slot (it follows
  upstream's `SepOn`, UsdtVerify/Usdt/Invariant/Supply.lean).

The bytecode of SKY adds to a balance and subtracts from `totalSupply` with no check (`unchecked`
in the source): `tot_bal`, `tot_allow`, `add_bal`, `sub_tot` and the tactic `sky_side` are the
rules that prove from `Inv` that such a sum does not wrap (TokenKit/Evm/SupplyUnchecked.lean).
-/

namespace SkyVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of SKY: the sum of all balances (base slot 2) is `totalSupply` (slot 1). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv 2 1 C S

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
  [message.caller.toU256,
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32)]

/-- The separation of slots for the address words of `A` (a hypothesis about keccak). -/
structure Sep (A : List U256) : Prop where
  /-- Slot 1 (`totalSupply`) is the balance slot of no address. -/
  total : Supply.NotBal 2 1
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 2 x
  /-- An allowance slot keyed by two words of `A` is no balance slot and is not slot 1. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 2 (mapSlot s (mapSlot o 3)) ∧ mapSlot s (mapSlot o 3) ≠ 1
  /-- The `wards` slot of a word of `A` is no balance slot and is not slot 1. -/
  ward : ∀ x ∈ A, Supply.NotBal 2 (mapSlot x 0) ∧ mapSlot x 0 ≠ 1
  /-- The `nonces` slot of a word of `A` is no balance slot, is not slot 1, and is no allowance
  slot keyed by two words of `A`. -/
  nonce : ∀ x ∈ A, Supply.NotBal 2 (mapSlot x 4) ∧ mapSlot x 4 ≠ 1 ∧
    ∀ o ∈ A, ∀ s ∈ A, mapSlot s (mapSlot o 3) ≠ mapSlot x 4

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a word of `A` that is below `2^160`. -/
theorem D_bal (hsep : Sep A) {x : U256} (hx : x ∈ A) (hlt : x.toNat < 2 ^ 160)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 1 C (writeSlot S C (mapSlot x 2) v) =
      Supply.D 2 1 C S - (storageAt S C (mapSlot x 2)).toNat + v.toNat :=
  Supply.D_write_bal hacc (hsep.uniq _ hx) hlt hsep.total v

/-- A write of `totalSupply`. -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 1 C (writeSlot S C 1 v) =
      Supply.D 2 1 C S + (storageAt S C 1).toNat - v.toNat :=
  Supply.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 1 C (writeSlot S C (mapSlot s (mapSlot o 3)) v) = Supply.D 2 1 C S :=
  Supply.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2 v

/-- A write of `wards` of a word of `A`. -/
theorem D_ward (hsep : Sep A) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 1 C (writeSlot S C (mapSlot x 0) v) = Supply.D 2 1 C S :=
  Supply.D_write_other hacc (hsep.ward x hx).1 (hsep.ward x hx).2 v

/-- A write of `nonces` of a word of `A`. -/
theorem D_nonce (hsep : Sep A) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 1 C (writeSlot S C (mapSlot x 4) v) = Supply.D 2 1 C S :=
  Supply.D_write_other hacc (hsep.nonce x hx).1 (hsep.nonce x hx).2.1 v

/-- The word of `totalSupply` after a write of the balance of an address word. -/
theorem tot_bal (hsep : Sep A) {x : U256} (hlt : x.toNat < 2 ^ 160) (hacc : hasAccount S C)
    (v : U256) : storageAt (writeSlot S C (mapSlot x 2) v) C 1 = storageAt S C 1 :=
  storageAt_writeSlot_of_ne hacc (hsep.total x hlt)

/-- The word of `totalSupply` after a write of an allowance keyed by two words of `A`. -/
theorem tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) (hacc : hasAccount S C)
    (v : U256) : storageAt (writeSlot S C (mapSlot s (mapSlot o 3)) v) C 1 = storageAt S C 1 :=
  storageAt_writeSlot_of_ne hacc (fun e => (hsep.allow o ho s hs).2 e.symm)

/-- The word of a balance after a write of an allowance keyed by two words of `A`. -/
theorem bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hlt : x.toNat < 2 ^ 160) (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot s (mapSlot o 3)) v) C (mapSlot x 2) =
      storageAt S C (mapSlot x 2) :=
  storageAt_writeSlot_of_ne hacc (fun e => (hsep.allow o ho s hs).1 x hlt e.symm)

/-- `v + balance` with no check: it does not wrap when the sum of all balances plus `v` is below
`2^256` (a conditional rewrite rule; `sky_side` proves the bound from the invariant). -/
theorem add_bal {x v : U256} (hx : x.toNat < 2 ^ 160)
    (hb : Supply.D 2 1 C S + (storageAt S C 1).toNat + v.toNat < 2 ^ 256) :
    (add v (storageAt S C (mapSlot x 2))).toNat =
      v.toNat + (storageAt S C (mapSlot x 2)).toNat :=
  Supply.add_bal_bound hx hb

/-- `totalSupply - v` with no check: it does not wrap when `v` is at most `totalSupply`. -/
theorem sub_tot {v : U256} (h : v.toNat ≤ (storageAt S C 1).toNat) :
    (sub (storageAt S C 1) v).toNat = (storageAt S C 1).toNat - v.toNat :=
  Supply.sub_toNat_le h

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Sky/Readable.lean`): under `Sep A`, an equation
between two slots a call uses is an equation between their keys, or is false. -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 2 = mapSlot x 2) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_tot_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((1 : U256) = mapSlot x 2) = False :=
  eq_false (hsep.total x hx)

theorem slot_bal_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 2 = (1 : U256)) = False :=
  eq_false (fun e => hsep.total x hx e.symm)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 3) = mapSlot x 2) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 2 = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 3) = (1 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((1 : U256) = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2 e.symm)

theorem slot_allow_nonce (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A) (hx : x ∈ A) :
    (mapSlot s (mapSlot o 3) = mapSlot x 4) = False :=
  eq_false ((hsep.nonce x hx).2.2 o ho s hs)

theorem slot_nonce_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A) (hx : x ∈ A) :
    (mapSlot x 4 = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.nonce x hx).2.2 o ho s hs e.symm)

end SkyVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word or the word of an
address below `2^160`, or that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact SkyVerify.mask_lt _
    | exact TokenKit.toNat_toU256_lt _
    | supply_side)

/-- Closes the side goals of the rules of the invariant proofs of SKY: those of `slot_side`, and
the bounds of the unchecked sums (`add_bal`, `sub_tot`), from the facts of the context (the
invariant, the checks of the path). `h` is the hypothesis `Sep`. -/
macro "sky_side" h:ident : tactic =>
  `(tactic| first
    | (slot_side; done)
    | omega
    | (simp (disch := slot_side) only [TokenKit.Supply.D_read, SkyVerify.D_bal $h,
        SkyVerify.D_tot $h, SkyVerify.D_allow $h, SkyVerify.D_ward $h, SkyVerify.D_nonce $h,
        UsdtVerify.storageAt_readSlot, SkyVerify.tot_bal $h, SkyVerify.tot_allow $h,
        SkyVerify.bal_allow $h]
       omega))

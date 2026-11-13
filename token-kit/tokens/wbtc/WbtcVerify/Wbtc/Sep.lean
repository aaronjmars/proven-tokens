import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Opt06

/-!
# The supply invariant of WBTC and the hypothesis on keccak it needs

The storage of WBTC, as the bytecode reads it (docs/MAP.md): `balances[a]` in slot `mapSlot a 0`,
`totalSupply_` in slot 1, `allowed[o][s]` in slot `mapSlot s (mapSlot o 2)`, `name` in slot 3,
`symbol` in slot 4; slot 5 packs `decimals` (byte 0), `owner` (bits 8 to 167), `mintingFinished`
(byte 21) and `paused` (byte 22); `pendingOwner` in the low 160 bits of slot 6.

- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` equals the word of slot 1.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: slot 1 is the balance slot of no
  address; the balance slot of a word of `A` is the balance slot of no other address; an
  allowance slot keyed by two words of `A` is no balance slot and is not slot 1; neither of the
  slots 5 and 6 is a balance slot. Finitely many facts, each about one given slot against the
  2^160 balance slots (it follows upstream's `SepOn`, UsdtVerify/Usdt/Invariant/Supply.lean).
-/

namespace WbtcVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of WBTC: the sum of all balances (base slot 0) is `totalSupply_` (slot 1). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv 0 1 C S

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

/-- The same with the mask on the right. -/
theorem mask_ltR (w : U256) :
    (bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256)).toNat < 2 ^ 160 := by
  rw [and_mask_comm]
  exact mask_lt w

/-- The address words a call can use as mapping keys. -/
def callKeys {fork : Fork} (message : Message fork) : List U256 :=
  [message.caller.toU256,
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32)]

/-- The separation of slots for the address words of `A` (a hypothesis about keccak). -/
structure Sep (A : List U256) : Prop where
  /-- Slot 1 (`totalSupply_`) is the balance slot of no address. -/
  total : Supply.NotBal 0 1
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 0 x
  /-- An allowance slot keyed by two words of `A` is no balance slot and is not slot 1. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 0 (mapSlot s (mapSlot o 2)) ∧ mapSlot s (mapSlot o 2) ≠ 1
  /-- Slot 5 (decimals, owner, mintingFinished, paused) and slot 6 (pendingOwner) are balance
  slots of no address. -/
  fixed : Supply.NotBal 0 5 ∧ Supply.NotBal 0 6

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a word of `A` that is below `2^160`. -/
theorem D_bal (hsep : Sep A) {x : U256} (hx : x ∈ A) (hlt : x.toNat < 2 ^ 160)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C (mapSlot x 0) v) =
      Supply.D 0 1 C S - (storageAt S C (mapSlot x 0)).toNat + v.toNat :=
  Supply.D_write_bal hacc (hsep.uniq _ hx) hlt hsep.total v

/-- A write of `totalSupply_`. -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C 1 v) =
      Supply.D 0 1 C S + (storageAt S C 1).toNat - v.toNat :=
  Supply.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C (mapSlot s (mapSlot o 2)) v) = Supply.D 0 1 C S :=
  Supply.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2 v

/-- A write of slot 5 (decimals, owner, mintingFinished, paused). -/
theorem D_owner (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C 5 v) = Supply.D 0 1 C S :=
  Supply.D_write_other hacc hsep.fixed.1 (by decide) v

/-- A write of `pendingOwner` (slot 6). -/
theorem D_pending (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C 6 v) = Supply.D 0 1 C S :=
  Supply.D_write_other hacc hsep.fixed.2 (by decide) v

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Wbtc/Readable.lean`): under `Sep A`, an equation
between two slots a call uses is an equation between their keys, or is false. -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 0 = mapSlot x 0) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_tot_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((1 : U256) = mapSlot x 0) = False :=
  eq_false (hsep.total x hx)

theorem slot_bal_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 0 = (1 : U256)) = False :=
  eq_false (fun e => hsep.total x hx e.symm)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 2) = mapSlot x 0) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 0 = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 2) = (1 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((1 : U256) = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2 e.symm)

end WbtcVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word or the word of an
address below `2^160`, or that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact WbtcVerify.mask_lt _
    | exact TokenKit.toNat_toU256_lt _
    | supply_side)

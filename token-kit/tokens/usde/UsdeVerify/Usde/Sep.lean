import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Opt06
import UsdeVerify.Usde.SupplyLib

/-!
# The supply invariant of USDe and the hypothesis on keccak it needs

The storage of USDe, as the bytecode reads it (docs/MAP.md): `_owner` in the low 160 bits of
slot 0, `_pendingOwner` in the low 160 bits of slot 1, `_balances[a]` in slot `mapSlot a 2`,
`_allowances[o][s]` in slot `mapSlot s (mapSlot o 3)`, `_totalSupply` in slot 4, `_name` in
slot 5, `_symbol` in slot 6, the two fallback strings of EIP-712 in slots 7 and 8, `_nonces[a]`
in slot `mapSlot a 9`, `minter` in the low 160 bits of slot 11.

- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` equals the word of slot 4.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: slot 4 is the balance slot of no
  address; the balance slot of a word of `A` is the balance slot of no other address; an
  allowance slot keyed by two words of `A` is no balance slot and is not slot 4; the nonce slot
  of a word of `A` is no balance slot, is not slot 4 and is no allowance slot keyed by two words
  of `A`; none of the slots 0, 1, 11 is a balance slot. Finitely many facts, each about one
  given slot against the 2^160 balance slots (it follows upstream's `SepOn`,
  UsdtVerify/Usdt/Invariant/Supply.lean).
-/

namespace UsdeVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of USDe: the sum of all balances (base slot 2) is `_totalSupply` (slot 4). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv 2 4 C S

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
  /-- Slot 4 (`_totalSupply`) is the balance slot of no address. -/
  total : Supply.NotBal 2 4
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 2 x
  /-- An allowance slot keyed by two words of `A` is no balance slot and is not slot 4. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 2 (mapSlot s (mapSlot o 3)) ∧ mapSlot s (mapSlot o 3) ≠ 4
  /-- The `_nonces` slot of a word of `A` is no balance slot, is not slot 4, and is no allowance
  slot keyed by two words of `A`. -/
  nonce : ∀ x ∈ A, Supply.NotBal 2 (mapSlot x 9) ∧ mapSlot x 9 ≠ 4 ∧
    ∀ o ∈ A, ∀ s ∈ A, mapSlot s (mapSlot o 3) ≠ mapSlot x 9
  /-- The slots of `_owner`, `_pendingOwner` and `minter` are balance slots of no address. -/
  fixed : Supply.NotBal 2 0 ∧ Supply.NotBal 2 1 ∧ Supply.NotBal 2 11

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a word of `A` that is below `2^160`. -/
theorem D_bal (hsep : Sep A) {x : U256} (hx : x ∈ A) (hlt : x.toNat < 2 ^ 160)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C (mapSlot x 2) v) =
      Supply.D 2 4 C S - (storageAt S C (mapSlot x 2)).toNat + v.toNat :=
  Supply.D_write_bal hacc (hsep.uniq _ hx) hlt hsep.total v

/-- A write of `_totalSupply`. -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C 4 v) =
      Supply.D 2 4 C S + (storageAt S C 4).toNat - v.toNat :=
  Supply.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C (mapSlot s (mapSlot o 3)) v) = Supply.D 2 4 C S :=
  Supply.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2 v

/-- A write of `_nonces` of a word of `A`. -/
theorem D_nonce (hsep : Sep A) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C (mapSlot x 9) v) = Supply.D 2 4 C S :=
  Supply.D_write_other hacc (hsep.nonce x hx).1 (hsep.nonce x hx).2.1 v

/-- A write of `_owner` (slot 0). -/
theorem D_owner (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C 0 v) = Supply.D 2 4 C S :=
  Supply.D_write_other hacc hsep.fixed.1 (by decide) v

/-- A write of `_pendingOwner` (slot 1). -/
theorem D_pending (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C 1 v) = Supply.D 2 4 C S :=
  Supply.D_write_other hacc hsep.fixed.2.1 (by decide) v

/-- A write of `minter` (slot 11). -/
theorem D_minter (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 2 4 C (writeSlot S C 11 v) = Supply.D 2 4 C S :=
  Supply.D_write_other hacc hsep.fixed.2.2 (by decide) v

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Usde/Readable.lean`): under `Sep A`, an equation
between two slots a call uses is an equation between their keys, or is false. -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 2 = mapSlot x 2) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_tot_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((4 : U256) = mapSlot x 2) = False :=
  eq_false (hsep.total x hx)

theorem slot_bal_tot (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 2 = (4 : U256)) = False :=
  eq_false (fun e => hsep.total x hx e.symm)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 3) = mapSlot x 2) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 2 = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 3) = (4 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((4 : U256) = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2 e.symm)

theorem slot_allow_nonce (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A) (hx : x ∈ A) :
    (mapSlot s (mapSlot o 3) = mapSlot x 9) = False :=
  eq_false ((hsep.nonce x hx).2.2 o ho s hs)

theorem slot_nonce_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A) (hx : x ∈ A) :
    (mapSlot x 9 = mapSlot s (mapSlot o 3)) = False :=
  eq_false (fun e => (hsep.nonce x hx).2.2 o ho s hs e.symm)

/-! ## What the invariant gives for the unchecked arithmetic of the bytecode -/

/-- Under the invariant, `_balances[x]` is at most `_totalSupply`. -/
theorem inv_balance_le {x : U256} (hx : x.toNat < 2 ^ 160) (h : Inv C S) :
    (storageAt S C (mapSlot x 2)).toNat ≤ (storageAt S C 4).toNat :=
  Supply.inv_bal_le hx h

/-- Under the invariant, the balances of two different address words are together at most
`_totalSupply`; so they are together below `2^256`. -/
theorem inv_two_balances_le {x y : U256} (hx : x.toNat < 2 ^ 160) (hy : y.toNat < 2 ^ 160)
    (hne : x ≠ y) (h : Inv C S) :
    (storageAt S C (mapSlot x 2)).toNat + (storageAt S C (mapSlot y 2)).toNat ≤
      (storageAt S C 4).toNat :=
  Supply.inv_two_bal_le hx hy hne h

end UsdeVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word or the word of an
address below `2^160`, or that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact UsdeVerify.mask_lt _
    | exact TokenKit.toNat_toU256_lt _
    | supply_side)

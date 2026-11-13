import TokenKit.Evm.Supply

/-!
# The balances of QNT against `totalSupply_`, and the hypothesis on keccak the proofs need

The storage of QNT (StandardToken, solc 0.4.21), as the bytecode reads it: `balances[a]` in slot
`mapSlot a 0`, `totalSupply_` in slot 1, `allowed[o][s]` in slot `mapSlot s (mapSlot o 2)`,
`crowdsale` in the low 160 bits of slot 3.

- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` equals the word of slot 1. The bytecode of `mint` does NOT keep it (it adds to a
  balance and never writes slot 1); see Invariant.lean and Seq.lean for what is proved.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the proofs use, for the address words of `A`. It is a
  hypothesis about keccak only, and it is NOT proved: slots 1 and 3 are the balance slot of no
  address; the balance slot of a word of `A` is the balance slot of no other address; an
  allowance slot keyed by two words of `A` is no balance slot and is neither slot 1 nor slot 3.
  Finitely many facts, each about one given slot against the 2^160 balance slots (it follows
  upstream's `SepOn`, UsdtVerify/Usdt/Invariant/Supply.lean).
-/

namespace QntVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The sum of all balances (base slot 0) is `totalSupply_` (slot 1). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop := Supply.Inv 0 1 C S

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
  /-- Slot 1 (`totalSupply_`) is the balance slot of no address. -/
  total : Supply.NotBal 0 1
  /-- Slot 3 (`crowdsale`) is the balance slot of no address. -/
  crowd : Supply.NotBal 0 3
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 0 x
  /-- An allowance slot keyed by two words of `A` is no balance slot, not slot 1, not slot 3. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 0 (mapSlot s (mapSlot o 2)) ∧ mapSlot s (mapSlot o 2) ≠ 1 ∧
      mapSlot s (mapSlot o 2) ≠ 3

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a masked word of `A`. -/
theorem D_bal (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 0) v) =
      Supply.D 0 1 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 0)).toNat +
        v.toNat :=
  Supply.D_write_bal hacc (hsep.uniq _ hx) (mask_lt w) hsep.total v

/-- A write of `totalSupply_` (no function of QNT does it; the rule is here for the generator). -/
theorem D_tot (hsep : Sep A) (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C 1 v) =
      Supply.D 0 1 C S + (storageAt S C 1).toNat - v.toNat :=
  Supply.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.D 0 1 C (writeSlot S C (mapSlot s (mapSlot o 2)) v) = Supply.D 0 1 C S :=
  Supply.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2.1 v

/-- A write of a balance keeps the word of slot 1 and of slot 3. -/
theorem keep_bal (hsep : Sep A) {w n : U256} (hn : n = 1 ∨ n = 3) (hacc : hasAccount S C)
    (v : U256) :
    storageAt (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 0) v) C n =
      storageAt S C n := by
  rcases hn with rfl | rfl
  · exact storageAt_writeSlot_of_ne hacc (hsep.total _ (mask_lt w))
  · exact storageAt_writeSlot_of_ne hacc (hsep.crowd _ (mask_lt w))

/-- A write of an allowance keyed by two words of `A` keeps the word of slot 1 and of slot 3. -/
theorem keep_allow (hsep : Sep A) {o s n : U256} (hn : n = 1 ∨ n = 3) (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot s (mapSlot o 2)) v) C n = storageAt S C n := by
  rcases hn with rfl | rfl
  · exact storageAt_writeSlot_of_ne hacc (Ne.symm (hsep.allow o ho s hs).2.1)
  · exact storageAt_writeSlot_of_ne hacc (Ne.symm (hsep.allow o ho s hs).2.2)

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries (`Qnt/Readable.lean`): under `Sep A`, an equation
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

theorem slot_crowd_bal (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((3 : U256) = mapSlot x 0) = False :=
  eq_false (hsep.crowd x hx)

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 2) = mapSlot x 0) = False :=
  eq_false ((hsep.allow o ho s hs).1 x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 0 = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).1 x hx e.symm)

theorem slot_allow_tot (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    (mapSlot s (mapSlot o 2) = (1 : U256)) = False :=
  eq_false (hsep.allow o ho s hs).2.1

theorem slot_tot_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((1 : U256) = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2.1 e.symm)

theorem slot_crowd_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A) :
    ((3 : U256) = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs).2.2 e.symm)

end QntVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word below `2^160`, or
that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact QntVerify.mask_lt _
    | supply_side)

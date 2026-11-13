import TokenKit.Evm.Solvent

/-!
# The solvency invariant of WETH9 and the hypothesis on keccak it needs

The storage of WETH9, as the bytecode reads it: `balanceOf[a]` in slot `mapSlot a 3`,
`allowance[o][s]` in slot `mapSlot s (mapSlot o 4)`. There is no slot for the total supply:
`totalSupply()` returns the ether balance of the contract.

- `Solvent C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` is at most the ether balance of `C`.
- `Backed v C S`: that sum plus `v` is at most the ether balance of `C` (the form at the start of
  a frame whose message carries `v` wei, already credited to `C`).
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: the balance slot of a word of `A`
  is the balance slot of no other address; an allowance slot keyed by two words of `A` is no
  balance slot. Finitely many facts, each about one given slot against the 2^160 balance slots
  (it follows upstream's `SepOn`, UsdtVerify/Usdt/Invariant/Supply.lean).

## Why an inequality and not an equality

The invariant is `sum of balanceOf <= ether of the contract`, not `=`:

- ether can reach the contract with no run of its code (the beneficiary of a SELFDESTRUCT, a
  block reward or a withdrawal credited to its address), which raises the right side only;
- `deposit()` adds `msg.value` to the balance word with an addition that the bytecode does not
  check; if the word wrapped, the sum would drop by 2^256 while the ether rose.

So no equality holds for every state and every run; the inequality does.
-/

namespace WethVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The sum of all balances (base slot 3) is at most the ether of the contract. -/
abbrev Solvent (C : Address) (S : State.TransactionState) : Prop := Supply.Solvent 3 C S

/-- The sum of all balances (base slot 3) plus `v` is at most the ether of the contract. -/
abbrev Backed (v : U256) (C : Address) (S : State.TransactionState) : Prop :=
  Supply.Backed 3 v C S

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
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 3 x
  /-- An allowance slot keyed by two words of `A` is no balance slot. -/
  allow : ∀ o ∈ A, ∀ s ∈ A, Supply.NotBal 3 (mapSlot s (mapSlot o 4))

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a masked word of `A`. -/
theorem sum_bal (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.sumBal 3 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 3) v) =
      Supply.sumBal 3 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 3)).toNat +
        v.toNat :=
  Supply.sumBal_write_bal hacc (hsep.uniq _ hx) (mask_lt w) v

/-- A write of an allowance keyed by two words of `A`. -/
theorem sum_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.sumBal 3 C (writeSlot S C (mapSlot s (mapSlot o 4)) v) = Supply.sumBal 3 C S :=
  Supply.sumBal_write_nb hacc (hsep.allow o ho s hs) v

/-- A read of a balance after a write of an allowance keyed by two words of `A`. -/
theorem read_bal_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (w v : U256) :
    storageAt (writeSlot S C (mapSlot s (mapSlot o 4)) v) C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 3) =
      storageAt S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 3) :=
  storageAt_writeSlot_of_ne hacc (fun e => hsep.allow o ho s hs _ (mask_lt w) e.symm)

/-! ## When two slots of a call are the same slot

Rewrite rules for the readable corollaries: under `Sep A`, an equation between two slots a call
uses is an equation between their keys, or is false. -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 3 = mapSlot x 3) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 4) = mapSlot x 3) = False :=
  eq_false ((hsep.allow o ho s hs) x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 3 = mapSlot s (mapSlot o 4)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs) x hx e.symm)

end WethVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word below `2^160`, or
that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | assumption
    | exact WethVerify.mask_lt _
    | supply_side)

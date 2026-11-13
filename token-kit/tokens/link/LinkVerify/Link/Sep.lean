import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Opt06
import TokenKit.Evm.Safe

/-!
# The supply invariant of LINK and the hypothesis on keccak it needs

The storage of LINK, as the bytecode reads it: `balances[a]` in slot `mapSlot a 1` and
`allowed[o][s]` in slot `mapSlot s (mapSlot o 2)`. The total supply is no slot: `totalSupply()`
returns the constant `10^27` of the code, and no function mints or burns.

- `TOTAL`: the constant `10^27` that `totalSupply()` returns.
- `Inv C S`: in the state `S`, the sum of the balance words of the 2^160 addresses of the
  contract `C` is `TOTAL`.
- `callKeys message`: the address words a call can use as mapping keys: the caller and the first
  two argument words, each masked to 160 bits.
- `Sep A`: the separation of slots that the invariant proofs use, for the address words of `A`.
  It is a hypothesis about keccak only, and it is NOT proved: the balance slot of a word of `A`
  is the balance slot of no other address; an allowance slot keyed by two words of `A` is no
  balance slot.
- `S_bal`, `S_allow`: what a write of a balance and of an allowance does to the sum.
- `inv_of_ro`: a run that only reads keeps the invariant.
-/

namespace TokenKit.Supply

open UsdtVerify
open EthLib.Base (U256)
open EthLib.Execution.Evm

/-- The SafeMath addition of Solidity 0.4 with the optimizer on: `c = v + b; assert(c >= b)`. -/
theorem add_fact_ltc {v b : U256} (h : isZero (lessThan (add v b) b) ≠ 0) :
    ((add v b).toNat : Int) = v.toNat + b.toNat := by
  have e : add v b = add b v := by
    unfold add
    exact BitVec.add_comm _ _
  rw [e] at h ⊢
  have := add_fact_lt h
  omega

end TokenKit.Supply

namespace LinkVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The total supply of LINK: the constant `10^27` in the code. -/
abbrev TOTAL : Int := 1000000000000000000000000000

/-- The invariant of LINK: the sum of all balances (base slot 1) is `TOTAL`. -/
def Inv (C : Address) (S : State.TransactionState) : Prop := Supply.sumBal 1 C S = TOTAL

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
  uniq : ∀ x ∈ A, Supply.UniqBal 1 x
  /-- An allowance slot keyed by two words of `A` is no balance slot. -/
  allow : ∀ o ∈ A, ∀ s ∈ A, Supply.NotBal 1 (mapSlot s (mapSlot o 2))

variable {C : Address} {S : State.TransactionState} {A : List U256}

/-- A write of the balance of a masked word of `A`. -/
theorem S_bal (hsep : Sep A) {w : U256}
    (hx : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.sumBal 1 C (writeSlot S C
        (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 1) v) =
      Supply.sumBal 1 C S -
        (storageAt S C (mapSlot
          (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) 1)).toNat +
        v.toNat :=
  Supply.sumBal_write_bal hacc (hsep.uniq _ hx) (mask_lt w) v

/-- A write of an allowance keyed by two words of `A`. -/
theorem S_allow (hsep : Sep A) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Supply.sumBal 1 C (writeSlot S C (mapSlot s (mapSlot o 2)) v) = Supply.sumBal 1 C S :=
  Supply.sumBal_write_nb hacc (hsep.allow o ho s hs) v

/-- The sum of the balances depends on the storage words of `C` only. -/
theorem sumBal_congr {S S' : State.TransactionState}
    (h : ∀ k : U256, storageAt S' C k = storageAt S C k) :
    Supply.sumBal 1 C S' = Supply.sumBal 1 C S := by
  unfold Supply.sumBal
  exact Supply.sumTo_congr _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h])

/-- A run that only reads keeps the invariant. -/
theorem inv_of_ro {S S' : State.TransactionState} {ss ss' : Substate}
    (h : Ro C S ss S' ss') (hinv : Inv C S) : Inv C S' := by
  unfold Inv at hinv ⊢
  rw [sumBal_congr (h.storage C)]
  exact hinv

/-! ## When two slots of a call are the same slot -/

/-- Two balance slots are the same slot only for the same address word. -/
theorem slot_bal_bal (hsep : Sep A) {x y : U256} (hx : x ∈ A) (hy : y.toNat < 2 ^ 160) :
    (mapSlot y 1 = mapSlot x 1) = (y = x) :=
  propext ⟨fun e => hsep.uniq x hx y hy e, fun e => by rw [e]⟩

theorem slot_allow_bal (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot s (mapSlot o 2) = mapSlot x 1) = False :=
  eq_false ((hsep.allow o ho s hs) x hx)

theorem slot_bal_allow (hsep : Sep A) {o s x : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hx : x.toNat < 2 ^ 160) : (mapSlot x 1 = mapSlot s (mapSlot o 2)) = False :=
  eq_false (fun e => (hsep.allow o ho s hs) x hx e.symm)

end LinkVerify

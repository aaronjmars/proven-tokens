import TokenKit.Evm.Supply
import TokenKit.Evm.SupplyMask
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Supply2
import TokenKit.Evm.Opt06
import TokenKit.Evm.Bits96

/-!
# The supply invariant of UNI and the hypothesis on keccak it needs

The storage of UNI, as the bytecode reads it (docs/MAP.md): `totalSupply` (a full word) in slot
0, `minter` in the low 160 bits of slot 1, `mintingAllowedAfter` in slot 2, `allowances[o][s]`
in the low 96 bits of slot `mapSlot s (mapSlot o 3)`, `balances[a]` in the low 96 bits of slot
`mapSlot a 4`, `delegates[a]` in the low 160 bits of slot `mapSlot a 5`, the checkpoint number
`i` of the delegate `d` (block number in the low 32 bits, votes in the 96 bits above) in slot
`mapSlot i (mapSlot d 6)`, `numCheckpoints[d]` in the low 32 bits of slot `mapSlot d 7`,
`nonces[a]` in slot `mapSlot a 8`.

- `Inv C S`: in the state `S`, the sum of the `uint96` balances (the low 96 bits of the balance
  word) of the 2^160 addresses of the contract `C` equals the word of slot 0. The bytecode never
  changes the other 160 bits of a balance word, and `balanceOf` returns the low 96 bits.
- `callKeys message`: the address words a call can use as keys of `balances` and `allowances`:
  the caller and the first two argument words masked to 160 bits.
- `delegKeys message S`: the delegates of those three words in the state `S` (the low 160 bits
  of their `delegates` words). `ckKeys message S` is both lists together: the delegates whose
  checkpoints a call of `transfer`, `transferFrom`, `mint` or `delegate` can write.
- `Sep A D`: the separation of slots that the invariant proofs use. It is a hypothesis about
  keccak only, and it is NOT proved (it cannot be proved by computation: see below). Every field
  is about finitely many given slots (the keys of the lists `A` and `D`), each against the 2^160
  balance slots and slot 0, or against one other given slot. `A` are the address words used as
  keys of `balances`, `allowances`, `delegates` and `nonces`; `D` are the delegates whose
  checkpoints are written. No field speaks about every address word.
- `SepAll A`: the form used before the fix round of audit 4 (UNI-2). Its fields `deleg`, `num`,
  `nonce`, `ck` speak about EVERY address word: "no `delegates` slot of any address is the
  balance slot of any address" is about 2^320 pairs of keccak inputs and 2^256 outputs, so for
  a random function it would be FALSE (about 2^64 such pairs are expected). A theorem under
  `SepAll` is therefore most likely empty. It is kept only as the weaker old form
  (`SepAll.sep`: it gives `Sep A D`, with three finite facts added).

What can and cannot be proved about `Sep`: `Supply.NotBal b n` and `Supply.UniqBal b x` are
statements over the 2^160 address words (one given slot against every balance slot). keccak is
a concrete function in the model (not opaque), so each is a closed statement, but a proof by
computation would evaluate keccak 2^160 times. They are true unless keccak-256 has a collision
between two given 64-byte inputs (or a preimage of a small word). The fields that compare two
given slots (`mapSlot x 5 ≠ 0` and the like) are single keccak evaluations.
-/

namespace UniVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The invariant of UNI: the sum of all `uint96` balances (base slot 4) is `totalSupply`
(slot 0). -/
abbrev Inv (C : Address) (S : State.TransactionState) : Prop :=
  SupplyMask.Inv (79228162514264337593543950335 : U256) 4 0 C S

/-- The sum of all `uint96` balances minus `totalSupply`. -/
abbrev Dsum (C : Address) (S : State.TransactionState) : Int :=
  SupplyMask.D (79228162514264337593543950335 : U256) 4 0 C S

theorem mask_idem (w : U256) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w :=
  m160_idem w

theorem mask_lt (w : U256) :
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat < 2 ^ 160 :=
  m160_lt w

/-- The address words a call can use as keys of `balances` and `allowances`. -/
def callKeys {fork : Fork} (message : Message fork) : List U256 :=
  [message.caller.toU256,
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 36 32)]

/-- The delegate of the address word `x` in the state `S`. -/
def delegOf (C : Address) (S : State.TransactionState) (x : U256) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (storageAt S C (mapSlot x 5))

/-- The delegates of the keys of a call in the state `S`. -/
def delegKeys {fork : Fork} (message : Message fork) (S : State.TransactionState) : List U256 :=
  [delegOf message.currentTarget S message.caller.toU256,
    delegOf message.currentTarget S
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 4 32)),
    delegOf message.currentTarget S
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (loadWord message.data 36 32))]

/-- The delegates whose checkpoints a call can write: the keys of the call and their
delegates in the state `S`. -/
def ckKeys {fork : Fork} (message : Message fork) (S : State.TransactionState) : List U256 :=
  callKeys message ++ delegKeys message S

/-- The separation of slots (a hypothesis about keccak), finite-key form: `A` are the address
words used as keys of `balances`, `allowances`, `delegates` and `nonces`, `D` the delegates
whose checkpoints are written. -/
structure Sep (A D : List U256) : Prop where
  /-- Slot 0 (`totalSupply`) is the balance slot of no address. -/
  total : Supply.NotBal 4 0
  /-- The balance slot of a word of `A` is the balance slot of no other address. -/
  uniq : ∀ x ∈ A, Supply.UniqBal 4 x
  /-- An allowance slot keyed by two words of `A` is no balance slot and is not slot 0. -/
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 4 (mapSlot s (mapSlot o 3)) ∧ mapSlot s (mapSlot o 3) ≠ 0
  /-- The slots of `minter` and `mintingAllowedAfter` are balance slots of no address. -/
  fixed : Supply.NotBal 4 1 ∧ Supply.NotBal 4 2
  /-- The `delegates` slot of a word of `A` is no balance slot and is not slot 0 or slot 2. -/
  deleg : ∀ x ∈ A, Supply.NotBal 4 (mapSlot x 5) ∧ mapSlot x 5 ≠ 0 ∧ mapSlot x 5 ≠ 2
  /-- The `nonces` slot of a word of `A` is no balance slot and is not slot 0. -/
  nonce : ∀ x ∈ A, Supply.NotBal 4 (mapSlot x 8) ∧ mapSlot x 8 ≠ 0
  /-- An allowance slot keyed by two words of `A` is the `delegates` slot of no word of `A`. -/
  allowDeleg : ∀ o ∈ A, ∀ s ∈ A, ∀ x ∈ A, mapSlot x 5 ≠ mapSlot s (mapSlot o 3)
  /-- The `nonces` slot of a word of `A` is the `delegates` slot of no word of `A`. -/
  nonceDeleg : ∀ x ∈ A, ∀ y ∈ A, mapSlot y 5 ≠ mapSlot x 8
  /-- The `numCheckpoints` slot of a word of `D` is no balance slot and is not slot 0. -/
  num : ∀ d ∈ D, Supply.NotBal 4 (mapSlot d 7) ∧ mapSlot d 7 ≠ 0
  /-- A `checkpoints` slot of a word of `D`, for a number below 2^32, is no balance slot and is
  not slot 0. -/
  ck : ∀ d ∈ D, ∀ i : U256, i.toNat < 2 ^ 32 →
    Supply.NotBal 4 (mapSlot i (mapSlot d 6)) ∧ mapSlot i (mapSlot d 6) ≠ 0

/-- The OLD, weaker form (before audit 4, UNI-2): the facts on the slots of the delegation are
asked for EVERY address word. Most likely false for keccak (see the header), so a theorem under
it most likely says nothing. Kept only so the old statements can still be named. -/
structure SepAll (A : List U256) : Prop where
  total : Supply.NotBal 4 0
  uniq : ∀ x ∈ A, Supply.UniqBal 4 x
  allow : ∀ o ∈ A, ∀ s ∈ A,
    Supply.NotBal 4 (mapSlot s (mapSlot o 3)) ∧ mapSlot s (mapSlot o 3) ≠ 0
  fixed : Supply.NotBal 4 1 ∧ Supply.NotBal 4 2
  deleg : ∀ d : U256, d.toNat < 2 ^ 160 → Supply.NotBal 4 (mapSlot d 5) ∧ mapSlot d 5 ≠ 0
  num : ∀ d : U256, d.toNat < 2 ^ 160 → Supply.NotBal 4 (mapSlot d 7) ∧ mapSlot d 7 ≠ 0
  nonce : ∀ d : U256, d.toNat < 2 ^ 160 → Supply.NotBal 4 (mapSlot d 8) ∧ mapSlot d 8 ≠ 0
  ck : ∀ d i : U256, d.toNat < 2 ^ 160 → i.toNat < 2 ^ 32 →
    Supply.NotBal 4 (mapSlot i (mapSlot d 6)) ∧ mapSlot i (mapSlot d 6) ≠ 0

/-- The three facts between two given slots that the finite form needs and the old form did not
state: for the words of `A`, a `delegates` slot is not slot 2, no allowance slot and no
`nonces` slot. -/
structure SepCross (A : List U256) : Prop where
  two : ∀ x ∈ A, mapSlot x 5 ≠ 2
  allowDeleg : ∀ o ∈ A, ∀ s ∈ A, ∀ x ∈ A, mapSlot x 5 ≠ mapSlot s (mapSlot o 3)
  nonceDeleg : ∀ x ∈ A, ∀ y ∈ A, mapSlot y 5 ≠ mapSlot x 8

/-- The old form (with the three finite facts `SepCross`) gives the finite form for any lists of
address words below 2^160. -/
theorem SepAll.sep {A D : List U256} (h : SepAll A) (hc : SepCross A)
    (hA : ∀ x ∈ A, x.toNat < 2 ^ 160) (hD : ∀ d ∈ D, d.toNat < 2 ^ 160) : Sep A D :=
  ⟨h.total, h.uniq, h.allow, h.fixed,
    fun x hx => ⟨(h.deleg x (hA x hx)).1, (h.deleg x (hA x hx)).2, hc.two x hx⟩,
    fun x hx => h.nonce x (hA x hx), hc.allowDeleg, hc.nonceDeleg,
    fun d hd => h.num d (hD d hd), fun d hd i hi => h.ck d i (hD d hd) hi⟩

variable {C : Address} {S : State.TransactionState} {A D : List U256}

/-- An SLOAD changes neither the balances nor the total supply. -/
theorem D_rd (c : Address) (n : U256) : Dsum C (readSlot S c n) = Dsum C S :=
  SupplyMask.D_read c n

/-- A write of the balance word of a word of `A` that is below `2^160`. -/
theorem D_bal (hsep : Sep A D) {x : U256} (hx : x ∈ A) (hlt : x.toNat < 2 ^ 160)
    (hacc : hasAccount S C) (v : U256) :
    Dsum C (writeSlot S C (mapSlot x 4) v) =
      Dsum C S - (bitwiseAnd (79228162514264337593543950335 : U256)
        (storageAt S C (mapSlot x 4))).toNat +
        (bitwiseAnd (79228162514264337593543950335 : U256) v).toNat :=
  SupplyMask.D_write_bal hacc (hsep.uniq _ hx) hlt hsep.total v

/-- A write of `totalSupply`. -/
theorem D_tot (hsep : Sep A D) (hacc : hasAccount S C) (v : U256) :
    Dsum C (writeSlot S C 0 v) = Dsum C S + (storageAt S C 0).toNat - v.toNat :=
  SupplyMask.D_write_tot hacc hsep.total v

/-- A write of an allowance keyed by two words of `A`. -/
theorem D_allow (hsep : Sep A D) {o s : U256} (ho : o ∈ A) (hs : s ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    Dsum C (writeSlot S C (mapSlot s (mapSlot o 3)) v) = Dsum C S :=
  SupplyMask.D_write_other hacc (hsep.allow o ho s hs).1 (hsep.allow o ho s hs).2 v

/-- A write of `minter` (slot 1). -/
theorem D_minter (hsep : Sep A D) (hacc : hasAccount S C) (v : U256) :
    Dsum C (writeSlot S C 1 v) = Dsum C S :=
  SupplyMask.D_write_other hacc hsep.fixed.1 (by decide) v

/-- A write of `mintingAllowedAfter` (slot 2). -/
theorem D_after (hsep : Sep A D) (hacc : hasAccount S C) (v : U256) :
    Dsum C (writeSlot S C 2 v) = Dsum C S :=
  SupplyMask.D_write_other hacc hsep.fixed.2 (by decide) v

/-- A write of `delegates` of a word of `A`. -/
theorem D_deleg (hsep : Sep A D) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C)
    (v : U256) : Dsum C (writeSlot S C (mapSlot x 5) v) = Dsum C S :=
  SupplyMask.D_write_other hacc (hsep.deleg x hx).1 (hsep.deleg x hx).2.1 v

/-- A write of `nonces` of a word of `A`. -/
theorem D_nonce (hsep : Sep A D) {x : U256} (hx : x ∈ A) (hacc : hasAccount S C)
    (v : U256) : Dsum C (writeSlot S C (mapSlot x 8) v) = Dsum C S :=
  SupplyMask.D_write_other hacc (hsep.nonce x hx).1 (hsep.nonce x hx).2 v

/-- The `delegates` word of a word of `A` after a write of a balance word. -/
theorem st_deleg_bal (hsep : Sep A D) {x y : U256} (hy : y ∈ A) (hx : x.toNat < 2 ^ 160)
    (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot x 4) v) C (mapSlot y 5) = storageAt S C (mapSlot y 5) :=
  storageAt_writeSlot_of_ne hacc ((hsep.deleg y hy).1 x hx)

/-- The `delegates` word of a word of `A` after a write of `totalSupply` (slot 0). -/
theorem st_deleg_tot (hsep : Sep A D) {y : U256} (hy : y ∈ A) (hacc : hasAccount S C)
    (v : U256) :
    storageAt (writeSlot S C 0 v) C (mapSlot y 5) = storageAt S C (mapSlot y 5) :=
  storageAt_writeSlot_of_ne hacc (hsep.deleg y hy).2.1

/-- The `delegates` word of a word of `A` after a write of `mintingAllowedAfter` (slot 2). -/
theorem st_deleg_after (hsep : Sep A D) {y : U256} (hy : y ∈ A) (hacc : hasAccount S C)
    (v : U256) :
    storageAt (writeSlot S C 2 v) C (mapSlot y 5) = storageAt S C (mapSlot y 5) :=
  storageAt_writeSlot_of_ne hacc (hsep.deleg y hy).2.2

/-- The `delegates` word of a word of `A` after a write of an allowance keyed by words of
`A`. -/
theorem st_deleg_allow (hsep : Sep A D) {o s y : U256} (ho : o ∈ A) (hs : s ∈ A) (hy : y ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot s (mapSlot o 3)) v) C (mapSlot y 5) =
      storageAt S C (mapSlot y 5) :=
  storageAt_writeSlot_of_ne hacc (hsep.allowDeleg o ho s hs y hy)

/-- The `delegates` word of a word of `A` after a write of the nonce of a word of `A`. -/
theorem st_deleg_nonce (hsep : Sep A D) {x y : U256} (hx : x ∈ A) (hy : y ∈ A)
    (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot x 8) v) C (mapSlot y 5) = storageAt S C (mapSlot y 5) :=
  storageAt_writeSlot_of_ne hacc (hsep.nonceDeleg x hx y hy)

/-- The slot `k` is a slot of the checkpoints of a delegate of the list `D`: a checkpoint for a
number below 2^32, or the `numCheckpoints` slot. The code that moves the votes of the delegates
(`_moveDelegates`, `_writeCheckpoint`) writes these slots only. -/
def CkSlot (D : List U256) (k : U256) : Prop :=
  ∃ d ∈ D, (∃ i : U256, i.toNat < 2 ^ 32 ∧ k = mapSlot i (mapSlot d 6)) ∨ k = mapSlot d 7

/-- A write of a checkpoint is not seen at a slot that is no checkpoint slot. -/
theorem st_ck {k : U256} (hk : ¬ CkSlot D k) {d i : U256} (hd : d ∈ D)
    (hi : i.toNat < 2 ^ 32) (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot i (mapSlot d 6)) v) C k = storageAt S C k :=
  storageAt_writeSlot_of_ne hacc (fun e => hk ⟨d, hd, Or.inl ⟨i, hi, e⟩⟩)

/-- A write of `numCheckpoints` is not seen at a slot that is no checkpoint slot. -/
theorem st_num {k : U256} (hk : ¬ CkSlot D k) {d : U256} (hd : d ∈ D)
    (hacc : hasAccount S C) (v : U256) :
    storageAt (writeSlot S C (mapSlot d 7) v) C k = storageAt S C k :=
  storageAt_writeSlot_of_ne hacc (fun e => hk ⟨d, hd, Or.inr e⟩)

/-- Under `Sep`, slot 0 is no checkpoint slot. -/
theorem not_ck_zero (hsep : Sep A D) : ¬ CkSlot D 0 := by
  rintro ⟨d, hd, ⟨i, hi, e⟩ | e⟩
  · exact (hsep.ck d hd i hi).2 e.symm
  · exact (hsep.num d hd).2 e.symm

/-- Under `Sep`, a balance slot is no checkpoint slot. -/
theorem not_ck_bal (hsep : Sep A D) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ¬ CkSlot D (mapSlot x 4) := by
  rintro ⟨d, hd, ⟨i, hi, e⟩ | e⟩
  · exact (hsep.ck d hd i hi).1 x hx e.symm
  · exact (hsep.num d hd).1 x hx e.symm

/-- A change of checkpoint slots only keeps the sum of the balances and the total supply. -/
theorem Dsum_frame (hsep : Sep A D) {S' : State.TransactionState}
    (h : ∀ k, ¬ CkSlot D k → storageAt S' C k = storageAt S C k) : Dsum C S' = Dsum C S := by
  show SupplyMask.D _ 4 0 C S' = SupplyMask.D _ 4 0 C S
  unfold SupplyMask.D SupplyMask.sumBal
  rw [h 0 (not_ck_zero hsep), Supply.sumTo_congr (g := SupplyMask.bal _ 4 C S) _ (fun i hi => by
    show ((bitwiseAnd _ (storageAt S' C _)).toNat : Int) =
      ((bitwiseAnd _ (storageAt S C _)).toNat : Int)
    rw [h _ (not_ck_bal hsep (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi))])]

/-- The separation for fewer keys. -/
theorem Sep.mono {A' D' : List U256} (hsep : Sep A D) (h : ∀ x ∈ A', x ∈ A)
    (h' : ∀ x ∈ D', x ∈ D) : Sep A' D' :=
  ⟨hsep.total, fun x hx => hsep.uniq x (h x hx),
    fun o ho s hs => hsep.allow o (h o ho) s (h s hs), hsep.fixed,
    fun x hx => hsep.deleg x (h x hx), fun x hx => hsep.nonce x (h x hx),
    fun o ho s hs x hx => hsep.allowDeleg o (h o ho) s (h s hs) x (h x hx),
    fun x hx y hy => hsep.nonceDeleg x (h x hx) y (h y hy),
    fun d hd => hsep.num d (h' d hd), fun d hd i hi => hsep.ck d (h' d hd) i hi⟩

end UniVerify

/-- Closes the side goals of the slot rules: a key of the call, a masked word or the word of an
address below `2^160`, a number below `2^32`, or that the contract still has its account. -/
macro "slot_side" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | exact UniVerify.mask_lt _
    | exact TokenKit.m160_ltR _
    | exact TokenKit.m32_lt _
    | exact TokenKit.toNat_toU256_lt _
    | supply_side)

/-- Proves that a key is in a list of keys: it is a hypothesis (compared without unfolding
`mapSlot`: two different slots are not compared by computing keccak), or a hypothesis once the
masks are in one form, or a member of the lists of the call. -/
macro "key_mem" : tactic =>
  `(tactic| first
    | with_reducible assumption
    | (simp only [TokenKit.and_mask_comm, UniVerify.mask_idem, TokenKit.mask_toU256']
       with_reducible assumption)
    | (simp [UniVerify.ckKeys, UniVerify.callKeys, UniVerify.delegKeys, UniVerify.delegOf]
       done))

/-- `key_mem`, also for the delegate of a key read after writes of balances, allowances, nonces,
`totalSupply` and `mintingAllowedAfter`: under the separation `hsep` the read is the read in the
start state. -/
macro "key_mem_sep" hsep:ident : tactic =>
  `(tactic| first
    | key_mem
    | (simp (disch := slot_side) only [UniVerify.delegOf, TokenKit.and_mask_comm,
         UniVerify.mask_idem, TokenKit.mask_toU256', UsdtVerify.storageAt_readSlot,
         UniVerify.st_deleg_bal $hsep, UniVerify.st_deleg_allow $hsep,
         UniVerify.st_deleg_tot $hsep, UniVerify.st_deleg_after $hsep,
         UniVerify.st_deleg_nonce $hsep]
       with_reducible assumption)
    | (simp (disch := slot_side) only [UniVerify.delegOf, TokenKit.and_mask_comm,
         UniVerify.mask_idem, TokenKit.mask_toU256', UsdtVerify.storageAt_readSlot,
         UniVerify.st_deleg_bal $hsep, UniVerify.st_deleg_allow $hsep,
         UniVerify.st_deleg_tot $hsep, UniVerify.st_deleg_after $hsep,
         UniVerify.st_deleg_nonce $hsep]
       simp [UniVerify.ckKeys, UniVerify.callKeys, UniVerify.delegKeys, UniVerify.delegOf]
       done))

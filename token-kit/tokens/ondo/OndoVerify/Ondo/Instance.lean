import OndoVerify.Ondo.Tx
import OndoVerify.Ondo.Sanity.Zero

/-!
# One closed instance: a concrete state and a concrete call (audit 5, fix ONDO-2)

Written by hand (not generated), on the model of `tokens/uni/UniVerify/Uni/Instance.lean`. The
supply theorems of ONDO take three kinds of hypotheses: the start invariant `Inv`, the state
fact `NoDelegation1` (used by `delegateBySig` only) and the hypothesis on keccak
`RealSep message state` (the finite-key form of Sep.lean). The audit found that none of them was
ever shown to hold for one concrete state and one concrete call (ONDO-2). This file does that,
as far as Lean can go.

The state: `sState C []`, one account at the contract `C`, every storage word 0.
The call: `m0`, `allowance(K, K)` sent by the address `Witness.CALLER1`, where `K` is the
address word of that caller. So the three mapping keys of the call are the one word `K`; the
signer word that `RealSep` adds for `delegateBySig` (`sigSigner`, what ECRECOVER returns on
the call data of this message) is the word 0, because the `v` byte of this call data is 0 and
EthLib's `Ecrecover.compute` rejects every `v` but 27 and 28 (`sigSigner_m0`, proved, nothing
assumed about ECRECOVER); the delegate of every word in that state is the word 0.

What is PROVED with no hypothesis:
- `inv_start`: the start invariant holds in that state (sum of balances 0, total supply 0).
- `noDelegation1_of_emptyHash`, `noDelegation1_sState`, `noDelegation1_before_pectra`:
  `NoDelegation1` holds in every state where the account at address 1 has the hash of the empty
  code, so in every state `sState C kvs`, and before Pectra in every state.
- `recoveredWord_v0`, `sigSigner_m0`: ECRECOVER returns nothing for `v = 0`, so the signer word
  of `m0` is 0.
- `realKeys_m0`, `realCk_m0`: the keys of the call are `[0, K, K, K]`, and the delegates whose
  checkpoints it could write are `[0, K, K, K, 0, 0, 0]`; the role word is `K`.
- The slot facts of `Sep` that are about given slots only, computed by the kernel with the real
  keccak (26 facts, `*_ne4`, `deleg*_ne_allow*`, `deleg*_ne_nonce*`).

What can NOT be proved in Lean: the rest of `Sep`. Each remaining fact says that one given slot
is the balance slot `keccak(a, 6)` of NO address word `a`, or of no other one (a statement over
2^160 values of keccak), or it is about the 2^32 checkpoint slots of one delegate. keccak is a
real, computable function here (not opaque), but no proof can run it 2^160 times, and no shorter
argument is known (it is preimage and collision resistance of keccak for these inputs). So the
hypothesis for this call is REDUCED to the smallest list: `KeyFacts`, 21 named facts, and
`realSep_m0_iff` proves that `RealSep m0 (sState C [])` is exactly that list (both directions).

- `supply_m0`: the closed instance of `supply_preserved_real`. Every run of the call `m0` by
  EthLib's real runner from the state `sState C []` that ends with no error ends in a state
  where the invariant holds. Its only hypotheses are the fork range and `KeyFacts`; every other
  hypothesis of `supply_preserved_real` (the start invariant, `NoDelegation1`, the size of the
  call data) is discharged here.
- `qMsg_m0`: the hypothesis `QMsg` of the transaction theorems (Tx.lean) for this message and
  state is exactly `KeyFacts` too.

Fork: `supply_m0` is stated for Paris <= fork < Glamsterdam (the one-counter gas meter is the
one EthLib runs only before Glamsterdam).
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace OndoVerify.Instance

open UsdtVerify
open TokenKit
open OndoVerify OndoVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork}

/-- The one key word of the instance: the address word of `Witness.CALLER1`. -/
abbrev K : U256 := Witness.CALLER1W

/-- The call `allowance(K, K)` from `Witness.CALLER1` to `C`. -/
abbrev m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data2 SEL_allowance K K)

/-- The mapping keys of the call `m0` are the one word `K`, three times. -/
theorem callKeys_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    callKeys (m0 b t C) = [K, K, K] := by
  have hc : (m0 b t C).caller.toU256 = K := Witness.caller1_toU256
  have h1 : loadWord (m0 b t C).data 4 32 = K := Witness.arg1_data2 size_SEL_allowance _ _
  have h2 : loadWord (m0 b t C).data 36 32 = K := Witness.arg2_data2 size_SEL_allowance _ _
  have hm : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) K = K := by
    decide
  unfold callKeys
  rw [hc, h1, h2, hm]

/-! ## The signer word of `m0` is 0 (ECRECOVER rejects `v = 0`) -/

theorem byteAt_append_left {a b : ByteArray} {i : Nat} (h : i < a.size) :
    EthLib.Base.byteAt (a ++ b) i = EthLib.Base.byteAt a i := by
  have h' : i < (a ++ b).size := by rw [ByteArray.size_append]; omega
  unfold EthLib.Base.byteAt
  rw [dif_pos h', dif_pos h]
  exact ByteArray.getElem_append_left h

theorem byteAt_append_right (a b : ByteArray) (j : Nat) :
    EthLib.Base.byteAt (a ++ b) (a.size + j) = EthLib.Base.byteAt b j := by
  unfold EthLib.Base.byteAt
  by_cases hj : j < b.size
  · have h' : a.size + j < (a ++ b).size := by rw [ByteArray.size_append]; omega
    rw [dif_pos h', dif_pos hj, ByteArray.getElem_append_right (by omega)]
    simp
  · have h' : ¬ a.size + j < (a ++ b).size := by rw [ByteArray.size_append]; omega
    rw [dif_neg h', dif_neg hj]

/-- The second word that ECRECOVER reads from the 128 input bytes is the `v` word. -/
theorem word32_sigInput (d v r s : U256) :
    Precompiles.Ecrecover.word (sigInput d v r s) 32 = Precompiles.Ecrecover.word (wordBytes v) 0 := by
  unfold Precompiles.Ecrecover.word
  congr 1
  funext i
  have hd : (wordBytes d).size = 32 := size_wordBytes d
  have h1 : (wordBytes d ++ wordBytes v).size = 64 := by
    rw [ByteArray.size_append, hd, size_wordBytes]
  have h2 : (wordBytes d ++ wordBytes v ++ wordBytes r).size = 96 := by
    rw [ByteArray.size_append, h1, size_wordBytes]
  have hi := i.isLt
  unfold sigInput
  rw [byteAt_append_left (by rw [h2]; omega), byteAt_append_left (by rw [h1]; omega)]
  have e := byteAt_append_right (wordBytes d) (wordBytes v) i.val
  rw [hd] at e
  rw [e, Nat.zero_add]

/-- ECRECOVER gives no output for `v = 0`, so the word the caller reads is 0. -/
theorem recoveredWord_v0 (d r s : U256) : recoveredWord (sigInput d 0 r s) = 0 := by
  have hv : EthLib.Base.bytesToNat (Precompiles.Ecrecover.word (wordBytes 0) 0).toList = 0 := by
    decide +kernel
  have ho : ∀ h : Vector UInt8 32, ∀ r' s' : Nat,
      Precompiles.Ecrecover.output h 0 r' s' = ByteArray.empty := by
    intro h r' s'
    unfold Precompiles.Ecrecover.output
    rw [dif_neg (by decide)]
  unfold recoveredWord Precompiles.Ecrecover.compute
  rw [word32_sigInput, hv, ho]
  rfl

/-- The `v` word of the call data of `m0` (bytes 100 to 131) is 0: the call data has 68 bytes. -/
theorem v_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    bitwiseAnd (loadWord (m0 b t C).data 100 32) (255 : U256) = 0 := by
  show bitwiseAnd (loadWord (data2 SEL_allowance K K) 100 32) (255 : U256) = 0
  decide +kernel

/-- The signer word that `RealSep` adds for `delegateBySig` is 0 for the call `m0`. -/
theorem sigSigner_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    sigSigner (m0 b t C) = 0 := by
  unfold sigSigner
  rw [v_m0, recoveredWord_v0]
  decide

/-- The keys of the call `m0`, the signer word included: `0` and `K`. -/
theorem realKeys_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    realKeys (m0 b t C) = [0, K, K, K] := by
  unfold realKeys
  rw [sigSigner_m0, callKeys_m0]

/-- In the state with all-zero storage every address word delegates to the word 0. -/
theorem delegOf_zero (C : Address) (x : U256) : delegOf C (sState C []) x = 0 := by
  unfold delegOf
  rw [storageAt_sState_nil]
  decide

/-- The delegates whose checkpoints the call `m0` could write from the state with all-zero
storage: `K` and the word 0. -/
theorem realCk_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    realCk (m0 b t C) (sState C []) = [0, K, K, K, 0, 0, 0] := by
  have hct : (m0 b t C).currentTarget = C := rfl
  unfold realCk ckKeys delegKeys
  rw [callKeys_m0, hct, delegOf_zero, delegOf_zero, delegOf_zero, delegOf_zero]
  rfl

/-- The role word of `m0` (the first argument word) is `K`. -/
theorem role_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    loadWord (m0 b t C).data 4 32 = K := Witness.arg1_data2 size_SEL_allowance _ _

/-! ## The part of `Sep` that the kernel computes (26 facts) -/

theorem allow00_ne4 : mapSlot (0 : U256) (mapSlot (0 : U256) 5) ≠ (4 : U256) := by decide +kernel
theorem allow0K_ne4 : mapSlot K (mapSlot (0 : U256) 5) ≠ (4 : U256) := by decide +kernel
theorem allowK0_ne4 : mapSlot (0 : U256) (mapSlot K 5) ≠ (4 : U256) := by decide +kernel
theorem allowKK_ne4 : mapSlot K (mapSlot K 5) ≠ (4 : U256) := by decide +kernel
theorem inv0_ne4 : mapSlot (0 : U256) 2 ≠ (4 : U256) := by decide +kernel
theorem invK_ne4 : mapSlot K 2 ≠ (4 : U256) := by decide +kernel
theorem role0_ne4 : mapSlot (0 : U256) (mapSlot K 0) ≠ (4 : U256) := by decide +kernel
theorem roleK_ne4 : mapSlot K (mapSlot K 0) ≠ (4 : U256) := by decide +kernel
theorem deleg0_ne4 : mapSlot (0 : U256) 7 ≠ (4 : U256) := by decide +kernel
theorem delegK_ne4 : mapSlot K 7 ≠ (4 : U256) := by decide +kernel
theorem nonce0_ne4 : mapSlot (0 : U256) 10 ≠ (4 : U256) := by decide +kernel
theorem nonceK_ne4 : mapSlot K 10 ≠ (4 : U256) := by decide +kernel
theorem num0_ne4 : mapSlot (0 : U256) 9 ≠ (4 : U256) := by decide +kernel
theorem numK_ne4 : mapSlot K 9 ≠ (4 : U256) := by decide +kernel
theorem deleg0_ne_allow00 : mapSlot (0 : U256) 7 ≠ mapSlot (0 : U256) (mapSlot (0 : U256) 5) := by
  decide +kernel
theorem deleg0_ne_allow0K : mapSlot (0 : U256) 7 ≠ mapSlot K (mapSlot (0 : U256) 5) := by
  decide +kernel
theorem deleg0_ne_allowK0 : mapSlot (0 : U256) 7 ≠ mapSlot (0 : U256) (mapSlot K 5) := by
  decide +kernel
theorem deleg0_ne_allowKK : mapSlot (0 : U256) 7 ≠ mapSlot K (mapSlot K 5) := by decide +kernel
theorem delegK_ne_allow00 : mapSlot K 7 ≠ mapSlot (0 : U256) (mapSlot (0 : U256) 5) := by
  decide +kernel
theorem delegK_ne_allow0K : mapSlot K 7 ≠ mapSlot K (mapSlot (0 : U256) 5) := by decide +kernel
theorem delegK_ne_allowK0 : mapSlot K 7 ≠ mapSlot (0 : U256) (mapSlot K 5) := by decide +kernel
theorem delegK_ne_allowKK : mapSlot K 7 ≠ mapSlot K (mapSlot K 5) := by decide +kernel
theorem deleg0_ne_nonce0 : mapSlot (0 : U256) 7 ≠ mapSlot (0 : U256) 10 := by decide +kernel
theorem deleg0_ne_nonceK : mapSlot (0 : U256) 7 ≠ mapSlot K 10 := by decide +kernel
theorem delegK_ne_nonce0 : mapSlot K 7 ≠ mapSlot (0 : U256) 10 := by decide +kernel
theorem delegK_ne_nonceK : mapSlot K 7 ≠ mapSlot K 10 := by decide +kernel

/-! ## The part of `Sep` that stays a hypothesis: 21 named facts -/

/-- The facts about keccak that the hypothesis asks for the call `m0` from the state with
all-zero storage and that Lean cannot prove: each is a statement over the 2^160 address words,
or over the 2^32 checkpoint numbers of one delegate. NOT proved; this is the whole list. -/
structure KeyFacts : Prop where
  /-- Slot 4 (`totalSupply`) is the balance slot of no address. -/
  total : Supply.NotBal 6 4
  /-- No other address word has the balance slot of the word 0. -/
  uniq0 : Supply.UniqBal 6 0
  /-- No other address word has the balance slot of `K`. -/
  uniqK : Supply.UniqBal 6 K
  /-- The four allowance slots keyed by `0` and `K` are balance slots of no address. -/
  allow00 : Supply.NotBal 6 (mapSlot (0 : U256) (mapSlot (0 : U256) 5))
  allow0K : Supply.NotBal 6 (mapSlot K (mapSlot (0 : U256) 5))
  allowK0 : Supply.NotBal 6 (mapSlot (0 : U256) (mapSlot K 5))
  allowKK : Supply.NotBal 6 (mapSlot K (mapSlot K 5))
  /-- Slot 1 (`cliffTimestamp`) is the balance slot of no address. -/
  cliff : Supply.NotBal 6 1
  /-- Slot 3 (`transferAllowed`) is the balance slot of no address. -/
  flag : Supply.NotBal 6 3
  /-- The `investorBalances` slots of `0` and `K` are balance slots of no address. -/
  inv0 : Supply.NotBal 6 (mapSlot (0 : U256) 2)
  invK : Supply.NotBal 6 (mapSlot K 2)
  /-- The member slots of `0` and `K` for the role word `K` are balance slots of no address. -/
  role0 : Supply.NotBal 6 (mapSlot (0 : U256) (mapSlot K 0))
  roleK : Supply.NotBal 6 (mapSlot K (mapSlot K 0))
  /-- The `delegates` slots of `0` and `K` are balance slots of no address. -/
  deleg0 : Supply.NotBal 6 (mapSlot (0 : U256) 7)
  delegK : Supply.NotBal 6 (mapSlot K 7)
  /-- The `nonces` slots of `0` and `K` are balance slots of no address. -/
  nonce0 : Supply.NotBal 6 (mapSlot (0 : U256) 10)
  nonceK : Supply.NotBal 6 (mapSlot K 10)
  /-- The `numCheckpoints` slots of `0` and `K` are balance slots of no address. -/
  num0 : Supply.NotBal 6 (mapSlot (0 : U256) 9)
  numK : Supply.NotBal 6 (mapSlot K 9)
  /-- A `checkpoints` slot of the word 0, for a number below 2^32, is no balance slot and not
  slot 4. -/
  ck0 : ∀ i : U256, i.toNat < 2 ^ 32 →
    Supply.NotBal 6 (mapSlot i (mapSlot (0 : U256) 8)) ∧ mapSlot i (mapSlot (0 : U256) 8) ≠ 4
  /-- A `checkpoints` slot of `K`, for a number below 2^32, is no balance slot and not slot 4. -/
  ckK : ∀ i : U256, i.toNat < 2 ^ 32 →
    Supply.NotBal 6 (mapSlot i (mapSlot K 8)) ∧ mapSlot i (mapSlot K 8) ≠ 4

theorem mem4 {x : U256} (h : x ∈ [0, K, K, K]) : x = 0 ∨ x = K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exact .inl h
  · exact .inr h
  · exact .inr h
  · exact .inr h

theorem mem7 {x : U256} (h : x ∈ [0, K, K, K, 0, 0, 0]) : x = 0 ∨ x = K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h
  · exact .inl h
  · exact .inr h
  · exact .inr h
  · exact .inr h
  · exact .inl h
  · exact .inl h
  · exact .inl h

/-- `Sep` for the keys `[0, K, K, K]`, the delegates `[0, K, K, K, 0, 0, 0]` and the role word
`K` is exactly `KeyFacts`: the list cannot be made shorter, and nothing else is hidden in
`Sep`. -/
theorem sep_iff : Sep [0, K, K, K] [0, K, K, K, 0, 0, 0] K ↔ KeyFacts := by
  constructor
  · intro h
    exact {
    total := h.total
    uniq0 := h.uniq 0 (by simp)
    uniqK := h.uniq K (by simp)
    allow00 := (h.allow 0 (by simp) 0 (by simp)).1
    allow0K := (h.allow 0 (by simp) K (by simp)).1
    allowK0 := (h.allow K (by simp) 0 (by simp)).1
    allowKK := (h.allow K (by simp) K (by simp)).1
    cliff := h.fixed.1
    flag := h.fixed.2
    inv0 := (h.inv 0 (by simp)).1
    invK := (h.inv K (by simp)).1
    role0 := (h.role 0 (by simp)).1
    roleK := (h.role K (by simp)).1
    deleg0 := (h.deleg 0 (by simp)).1
    delegK := (h.deleg K (by simp)).1
    nonce0 := (h.nonce 0 (by simp)).1
    nonceK := (h.nonce K (by simp)).1
    num0 := (h.num 0 (by simp)).1
    numK := (h.num K (by simp)).1
    ck0 := h.ck 0 (by simp)
    ckK := h.ck K (by simp)
    }
  · intro h
    exact {
    total := h.total
    uniq := fun x hx => by
      rcases mem4 hx with e | e <;> rw [e]
      · exact h.uniq0
      · exact h.uniqK
    allow := fun o ho s hs => by
      rcases mem4 ho with e | e <;> rcases mem4 hs with f | f <;> rw [e, f]
      · exact ⟨h.allow00, allow00_ne4⟩
      · exact ⟨h.allow0K, allow0K_ne4⟩
      · exact ⟨h.allowK0, allowK0_ne4⟩
      · exact ⟨h.allowKK, allowKK_ne4⟩
    fixed := ⟨h.cliff, h.flag⟩
    inv := fun x hx => by
      rcases mem4 hx with e | e <;> rw [e]
      · exact ⟨h.inv0, inv0_ne4⟩
      · exact ⟨h.invK, invK_ne4⟩
    role := fun x hx => by
      rcases mem4 hx with e | e <;> rw [e]
      · exact ⟨h.role0, role0_ne4⟩
      · exact ⟨h.roleK, roleK_ne4⟩
    deleg := fun x hx => by
      rcases mem4 hx with e | e <;> rw [e]
      · exact ⟨h.deleg0, deleg0_ne4⟩
      · exact ⟨h.delegK, delegK_ne4⟩
    nonce := fun x hx => by
      rcases mem4 hx with e | e <;> rw [e]
      · exact ⟨h.nonce0, nonce0_ne4⟩
      · exact ⟨h.nonceK, nonceK_ne4⟩
    allowDeleg := fun o ho s hs x hx => by
      rcases mem4 ho with e | e <;> rcases mem4 hs with f | f <;> rcases mem4 hx with g | g <;>
        rw [e, f, g]
      · exact deleg0_ne_allow00
      · exact delegK_ne_allow00
      · exact deleg0_ne_allow0K
      · exact delegK_ne_allow0K
      · exact deleg0_ne_allowK0
      · exact delegK_ne_allowK0
      · exact deleg0_ne_allowKK
      · exact delegK_ne_allowKK
    nonceDeleg := fun x hx y hy => by
      rcases mem4 hx with e | e <;> rcases mem4 hy with f | f <;> rw [e, f]
      · exact deleg0_ne_nonce0
      · exact delegK_ne_nonce0
      · exact deleg0_ne_nonceK
      · exact delegK_ne_nonceK
    num := fun d hd => by
      rcases mem7 hd with e | e <;> rw [e]
      · exact ⟨h.num0, num0_ne4⟩
      · exact ⟨h.numK, numK_ne4⟩
    ck := fun d hd => by
      rcases mem7 hd with e | e <;> rw [e]
      · exact h.ck0
      · exact h.ckK
    }

/-- The hypothesis on keccak of the call `m0` from the state with all-zero storage is exactly
`KeyFacts`. -/
theorem realSep_m0_iff (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : RealSep (m0 b t C) (sState C []) ↔ KeyFacts := by
  unfold RealSep
  rw [realKeys_m0, realCk_m0, role_m0]
  exact sep_iff

/-! ## The start invariant and `NoDelegation1` -/

/-- Every storage word of `C` is 0 in the state `sState C []`. -/
theorem getStorage_sState_nil (C : Address) (k : EthLib.Base.Bytes32) :
    (sState C []).getStorage C k = 0 := by
  simp [sState, State.TransactionState.ofBlock, State.TransactionState.getStorage,
    State.State.getStorage, State.StorageMap.slot, slotMap]

/-- The start invariant holds in the state with all-zero storage. -/
theorem inv_start (C : Address) : Inv C (sState C []) :=
  inv_zeroBase C _ (getStorage_sState_nil C)

/-- `NoDelegation1` holds in every state where the account at address 1 has the hash of the
empty code. -/
theorem noDelegation1_of_emptyHash {S : State.TransactionState}
    (h : (S.getAccount (toAddressMasked 1)).codeHash = EMPTY_CODE_HASH) :
    NoDelegation1 fork S := by
  intro c hc _
  rw [h] at hc
  have e : S.getCode EMPTY_CODE_HASH = .ok ByteArray.empty := by
    simp [State.TransactionState.getCode]
  rw [e] at hc
  cases hc
  exact Payee.delegatedAddress_empty

/-- Before Pectra `NoDelegation1` holds in every state. -/
theorem noDelegation1_before_pectra (hf : fork < .pectra) (S : State.TransactionState) :
    NoDelegation1 fork S :=
  fun _ _ hp => absurd hp (Nat.not_le.mpr hf)

/-- Every account of a state `sState C kvs` has the hash of the empty code. -/
theorem codeHash_sState (C : Address) (kvs : List (U256 × U256)) (a : Address) :
    ((sState C kvs).getAccount a).codeHash = EMPTY_CODE_HASH := by
  by_cases h : C = a
  · subst h
    simp [sState, S_ACCOUNT, State.TransactionState.ofBlock, State.TransactionState.getAccount,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional]
  · simp [sState, S_ACCOUNT, State.TransactionState.ofBlock, State.TransactionState.getAccount,
      State.TransactionState.getAccountOptional, State.State.getAccountOptional, h]
    rfl

/-- `NoDelegation1` holds in every state `sState C kvs`, at every fork. -/
theorem noDelegation1_sState (C : Address) (kvs : List (U256 × U256)) :
    NoDelegation1 fork (sState C kvs) :=
  noDelegation1_of_emptyHash (codeHash_sState C kvs _)

/-! ## The closed instance -/

/-- The hypothesis `QMsg` of the transaction theorems of Tx.lean, for the call `m0` from the
state with all-zero storage, is exactly `KeyFacts`. -/
theorem qMsg_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    QMsg fork (m0 b t C) (sState C []) ↔ KeyFacts :=
  ⟨fun h => (realSep_m0_iff b t C).mp h.1,
    fun h => ⟨(realSep_m0_iff b t C).mpr h, noDelegation1_sState C []⟩⟩

/-- THE CLOSED INSTANCE of `supply_preserved_real`: the call `m0` (`allowance(K, K)` from
`Witness.CALLER1`) from the state with all-zero storage, run by EthLib's real runner. Every run
that ends with no error ends in a state where the invariant holds. The only hypotheses left are
the fork range and `KeyFacts` (the 21 facts about keccak that cannot be proved). -/
theorem supply_m0 (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) (keys : KeyFacts)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    {substate : Substate} {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE (m0 b t C) 0 [] .empty gas (sState C []) substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv C s.state := by
  have hdata : (m0 b t C).data = data2 SEL_allowance K K := rfl
  have hsz : (m0 b t C).data.size = 68 := by
    rw [hdata]
    exact size_data2 size_SEL_allowance _ _
  exact supply_preserved_real hparis hglam (by rw [hsz]; decide) (noDelegation1_sState C [])
    ((realSep_m0_iff b t C).mpr keys) (inv_start C) start within hrun hok

end OndoVerify.Instance

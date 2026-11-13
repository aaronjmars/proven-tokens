import UniVerify.Uni.Tx
import UniVerify.Uni.Sanity.Zero

/-!
# One closed instance: a concrete state and a concrete call (audit 4, fix 5 and fix 6)

Written by hand (not generated). The theorems of UNI about the supply invariant take three
kinds of hypotheses: the start invariant `Inv`, the state fact `NoDelegation1` (used by `permit`
and `delegateBySig` only) and the hypothesis on keccak `RealSep message state` (the finite-key
form of Sep.lean). The auditors found that none of them was ever shown to hold for one concrete
state and one concrete call (UNI-2, UNI-5). This file does that, as far as Lean can go.

The state: `sState C []`, one account at the contract `C`, every storage word 0.
The call: `m0`, `allowance(K, K)` sent by the address `Witness.CALLER1`, where `K` is the
address word of that caller. So the three mapping keys of the call are the one word `K`, and
the delegate of `K` in that state is the address word 0.

What is PROVED with no hypothesis:
- `inv_start`: the start invariant holds in that state (sum of balances 0, total supply 0).
- `noDelegation1_of_emptyHash`, `noDelegation1_sState`, `noDelegation1_before_pectra`:
  `NoDelegation1` holds in every state where the account at address 1 has the hash of the empty
  code, so in every state `sState C kvs`, and before Pectra in every state.
- `realKeys_m0`, `realCk_m0`: the keys of the call are `[K, K, K]`, and the delegates whose
  checkpoints it could write are `[K, K, K, 0, 0, 0]`.
- The slot facts of `Sep` that are about given slots only, computed by the kernel with the real
  keccak: `allow_ne_total`, `deleg_ne_total`, `deleg_ne_two`, `nonce_ne_total`,
  `deleg_ne_allow`, `deleg_ne_nonce`, `numK_ne_total`, `num0_ne_total`.

What can NOT be proved in Lean: the rest of `Sep`. Each remaining fact says that one given slot
is the balance slot `keccak(a, 4)` of NO address word `a`, or of no other one (a statement over
2^160 values of keccak), or it is about the 2^32 checkpoint slots of one delegate. keccak is a
real, computable function here (not opaque), but no proof can run it 2^160 times, and no shorter
argument is known (it is preimage and collision resistance of keccak for these inputs). So the
hypothesis for this call is REDUCED to the smallest list: `KeyFacts`, 11 named facts, and
`realSep_m0_iff` proves that `RealSep m0 (sState C [])` is exactly that list (both directions).

- `supply_m0`: the closed instance of `supply_preserved_real`. Every run of the call `m0` by
  EthLib's real runner from the state `sState C []` that ends with no error ends in a state
  where the invariant holds. Its only hypotheses are the fork range and `KeyFacts`; every other
  hypothesis of `supply_preserved_real` (the start invariant, `NoDelegation1`, the size of the
  call data) is discharged here.

Fork: `supply_m0` is stated for Paris <= fork < Glamsterdam (the one-counter gas meter is the
one EthLib runs only before Glamsterdam).

NOT done here (audit 4, UNI-3): a concrete successful run of `transfer`, `transferFrom`, `mint`,
`delegate`, `delegateBySig` or `permit`. See `not_covered` in status.json for what is missing.
-/

set_option autoImplicit false

namespace UniVerify.Instance

open UsdtVerify
open TokenKit
open UniVerify UniVerify.Sanity

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

/-- The selector of the call `m0` is the one of `allowance`. -/
theorem selector_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    selector (m0 b t C).data = selector SEL_allowance :=
  selector_data2 size_SEL_allowance _ _

/-- The call `m0` is no `delegateBySig`: it has no signer key. -/
theorem sigKeys_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    sigKeys (m0 b t C) = [] := by
  unfold sigKeys
  rw [selector_m0, if_neg (by decide)]

/-- The keys of the call `m0`, the signer of `delegateBySig` included: `K` only. -/
theorem realKeys_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    realKeys (m0 b t C) = [K, K, K] := by
  unfold realKeys
  rw [sigKeys_m0, callKeys_m0]
  rfl

/-- In the state with all-zero storage every address word delegates to the word 0. -/
theorem delegOf_zero (C : Address) (x : U256) : delegOf C (sState C []) x = 0 := by
  unfold delegOf
  rw [storageAt_sState_nil]
  decide

/-- The delegates whose checkpoints the call `m0` could write from the state with all-zero
storage: `K` and the word 0. -/
theorem realCk_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    realCk (m0 b t C) (sState C []) = [K, K, K, 0, 0, 0] := by
  have hct : (m0 b t C).currentTarget = C := rfl
  unfold realCk ckKeys delegKeys
  rw [sigKeys_m0, callKeys_m0, hct, delegOf_zero, delegOf_zero, delegOf_zero]
  rfl

/-! ## The part of `Sep` that the kernel computes -/

/-- Computed by the kernel: the allowance slot of `(K, K)` is not slot 0. -/
theorem allow_ne_total : mapSlot K (mapSlot K 3) ≠ (0 : U256) := by decide +kernel

/-- Computed by the kernel: the `delegates` slot of `K` is not slot 0. -/
theorem deleg_ne_total : mapSlot K 5 ≠ (0 : U256) := by decide +kernel

/-- Computed by the kernel: the `delegates` slot of `K` is not slot 2. -/
theorem deleg_ne_two : mapSlot K 5 ≠ (2 : U256) := by decide +kernel

/-- Computed by the kernel: the `nonces` slot of `K` is not slot 0. -/
theorem nonce_ne_total : mapSlot K 8 ≠ (0 : U256) := by decide +kernel

/-- Computed by the kernel: the `delegates` slot of `K` is not the allowance slot of `(K, K)`. -/
theorem deleg_ne_allow : mapSlot K 5 ≠ mapSlot K (mapSlot K 3) := by decide +kernel

/-- Computed by the kernel: the `delegates` slot of `K` is not the `nonces` slot of `K`. -/
theorem deleg_ne_nonce : mapSlot K 5 ≠ mapSlot K 8 := by decide +kernel

/-- Computed by the kernel: the `numCheckpoints` slot of `K` is not slot 0. -/
theorem numK_ne_total : mapSlot K 7 ≠ (0 : U256) := by decide +kernel

/-- Computed by the kernel: the `numCheckpoints` slot of the word 0 is not slot 0. -/
theorem num0_ne_total : mapSlot (0 : U256) 7 ≠ (0 : U256) := by decide +kernel

/-! ## The part of `Sep` that stays a hypothesis: 11 named facts -/

/-- The facts about keccak that the hypothesis asks for the call `m0` from the state with
all-zero storage and that Lean cannot prove: each is a statement over the 2^160 address words,
or over the 2^32 checkpoint numbers of one delegate. NOT proved; this is the whole list. -/
structure KeyFacts : Prop where
  /-- Slot 0 (the total supply) is the balance slot of no address. -/
  total : Supply.NotBal 4 0
  /-- No other address word has the balance slot of `K`. -/
  uniq : Supply.UniqBal 4 K
  /-- The allowance slot of `(K, K)` is the balance slot of no address. -/
  allow : Supply.NotBal 4 (mapSlot K (mapSlot K 3))
  /-- Slot 1 (`minter`) is the balance slot of no address. -/
  minter : Supply.NotBal 4 1
  /-- Slot 2 (`mintingAllowedAfter`) is the balance slot of no address. -/
  after : Supply.NotBal 4 2
  /-- The `delegates` slot of `K` is the balance slot of no address. -/
  deleg : Supply.NotBal 4 (mapSlot K 5)
  /-- The `nonces` slot of `K` is the balance slot of no address. -/
  nonce : Supply.NotBal 4 (mapSlot K 8)
  /-- The `numCheckpoints` slot of `K` is the balance slot of no address. -/
  numK : Supply.NotBal 4 (mapSlot K 7)
  /-- The `numCheckpoints` slot of the word 0 is the balance slot of no address. -/
  num0 : Supply.NotBal 4 (mapSlot 0 7)
  /-- A `checkpoints` slot of `K`, for a number below 2^32, is no balance slot and not slot 0. -/
  ckK : ∀ i : U256, i.toNat < 2 ^ 32 →
    Supply.NotBal 4 (mapSlot i (mapSlot K 6)) ∧ mapSlot i (mapSlot K 6) ≠ 0
  /-- A `checkpoints` slot of the word 0, for a number below 2^32, is no balance slot and not
  slot 0. -/
  ck0 : ∀ i : U256, i.toNat < 2 ^ 32 →
    Supply.NotBal 4 (mapSlot i (mapSlot 0 6)) ∧ mapSlot i (mapSlot 0 6) ≠ 0

theorem mem3 {x : U256} (h : x ∈ [K, K, K]) : x = K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h
  exact h

theorem mem6 {x : U256} (h : x ∈ [K, K, K, 0, 0, 0]) : x = K ∨ x = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h
  · exact .inl h
  · exact .inl h
  · exact .inl h
  · exact .inr h
  · exact .inr h
  · exact .inr h

/-- `Sep` for the keys `[K, K, K]` and the delegates `[K, K, K, 0, 0, 0]` is exactly
`KeyFacts`: the list cannot be made shorter, and nothing else is hidden in `Sep`. -/
theorem sep_iff : Sep [K, K, K] [K, K, K, 0, 0, 0] ↔ KeyFacts := by
  constructor
  · intro h
    exact {
    total := h.total
    uniq := h.uniq K (by simp)
    allow := (h.allow K (by simp) K (by simp)).1
    minter := h.fixed.1
    after := h.fixed.2
    deleg := (h.deleg K (by simp)).1
    nonce := (h.nonce K (by simp)).1
    numK := (h.num K (by simp)).1
    num0 := (h.num 0 (by simp)).1
    ckK := h.ck K (by simp)
    ck0 := h.ck 0 (by simp)
    }
  · intro h
    exact {
    total := h.total
    uniq := fun x hx => by
      rw [mem3 hx]
      exact h.uniq
    allow := fun o ho s hs => by
      rw [mem3 ho, mem3 hs]
      exact ⟨h.allow, allow_ne_total⟩
    fixed := ⟨h.minter, h.after⟩
    deleg := fun x hx => by
      rw [mem3 hx]
      exact ⟨h.deleg, deleg_ne_total, deleg_ne_two⟩
    nonce := fun x hx => by
      rw [mem3 hx]
      exact ⟨h.nonce, nonce_ne_total⟩
    allowDeleg := fun o ho s hs x hx => by
      rw [mem3 ho, mem3 hs, mem3 hx]
      exact deleg_ne_allow
    nonceDeleg := fun x hx y hy => by
      rw [mem3 hx, mem3 hy]
      exact deleg_ne_nonce
    num := fun d hd => by
      rcases mem6 hd with e | e
      · rw [e]
        exact ⟨h.numK, numK_ne_total⟩
      · rw [e]
        exact ⟨h.num0, num0_ne_total⟩
    ck := fun d hd => by
      rcases mem6 hd with e | e
      · rw [e]
        exact h.ckK
      · rw [e]
        exact h.ck0
    }

/-- The hypothesis on keccak of the call `m0` from the state with all-zero storage is exactly
`KeyFacts`. -/
theorem realSep_m0_iff (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) : RealSep (m0 b t C) (sState C []) ↔ KeyFacts := by
  unfold RealSep
  rw [realKeys_m0, realCk_m0]
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

/-- THE CLOSED INSTANCE of `supply_preserved_real`: the call `m0` (`allowance(K, K)` from
`Witness.CALLER1`) from the state with all-zero storage, run by EthLib's real runner. Every run
that ends with no error ends in a state where the invariant holds. The only hypotheses left are
the fork range and `KeyFacts` (the 11 facts about keccak that cannot be proved). -/
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

end UniVerify.Instance

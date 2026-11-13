import UsddVerify.Usdd.Tx
import UsddVerify.Usdd.Sanity.Zero

/-!
# One closed instance: a concrete state and a concrete call (audit 4, fix 5 and fix 6)

Written by hand (not generated). The theorems of USDD about the supply invariant take three
kinds of hypotheses: the start invariant `Inv`, the state fact `NoDelegation1` (used by `permit`
only) and the hypothesis on keccak `Sep (callKeys message)`. The auditors found that none of
them was ever shown to hold for one concrete state and one concrete call. This file does that,
as far as Lean can go.

The state: `sState C []`, one account at the contract `C`, every storage word 0.
The call: `m0`, `allowance(K, K)` sent by the address `HOLDER`, where `K` is the
address word of that caller. So the three mapping keys of the call are the one word `K`.

What is PROVED with no hypothesis:
- `inv_start`: the start invariant holds in that state (sum of balances 0, total supply 0).
- `noDelegation1_of_emptyHash`, `noDelegation1_sState`, `noDelegation1_before_pectra`:
  `NoDelegation1` holds in every state where the account at address 1 has the hash of the empty
  code, so in every state `sState C kvs`, and before Pectra in every state.
- `callKeys_m0`: the keys of the call are `[K, K, K]`.
- The slot facts of `Sep` that are about given slots only, computed by the kernel with the real
  keccak: `allow_ne_total`, `nonce_ne_total`, `allow_ne_nonce`, `ward_ne_total`.

What can NOT be proved in Lean: the rest of `Sep`. Each remaining fact says that one given slot
is the balance slot `keccak(a, 2)` of NO address word `a`, or of no other one: a statement over
2^160 values of keccak. keccak is a real, computable function here (not opaque), but no proof
can run it 2^160 times, and no shorter argument is known (it is preimage and collision
resistance of keccak for these inputs). So `Sep` for this call is REDUCED to the smallest list:
`KeyFacts`, 5 named facts, and `sep_m0_iff` proves that `Sep (callKeys m0)` is exactly that
list (both directions). The facts: slot 1 (the total supply), the allowance slot of `(K, K)`,
the nonce slot of `K`, the `wards` slot of `K` are the balance slot of no address, and no
other address has the balance slot of `K`.

- `supply_m0`: the closed instance of `supply_preserved`. Every run of the call `m0` from the
  state `sState C []` that ends with no error ends in a state where the invariant holds. Its
  only hypotheses are the fork and `KeyFacts`; every other hypothesis of `supply_preserved`
  (the start invariant, the size of the call data, the selector) is discharged here.

Fork: `supply_m0` is stated for Berlin <= fork < Glamsterdam (the one-counter gas meter is the
one EthLib runs only before Glamsterdam).
-/

set_option autoImplicit false

namespace UsddVerify.Instance

open UsdtVerify
open TokenKit
open UsddVerify UsddVerify.Sanity

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm

variable {fork : Fork}

/-- The one key word of the instance: the address of the secp256k1 private key `0x11...11` (32
bytes `0x11`). The key is public on purpose, so that a signature of `permit` can be given
(`PermitRun.lean`). -/
abbrev K : U256 := 0x19e7e376e7c213b7e7e7e46cc70a5dd086daff2a

/-- The address with the word `K`. -/
def HOLDER : Address := toAddressMasked K

/-- Computed by the kernel: the word of `HOLDER` is `K`. -/
theorem holder_toU256 : HOLDER.toU256 = K := by decide +kernel

/-- The call `allowance(K, K)` from `HOLDER` to `C`. -/
abbrev m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    Message fork :=
  sMsg b t C HOLDER CODE (data2 SEL_allowance K K)

/-- The mapping keys of the call `m0` are the one word `K`, three times. -/
theorem callKeys_m0 (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    callKeys (m0 b t C) = [K, K, K] := by
  have hc : (m0 b t C).caller.toU256 = K := holder_toU256
  have h1 : loadWord (m0 b t C).data 4 32 = K := Witness.arg1_data2 size_SEL_allowance _ _
  have h2 : loadWord (m0 b t C).data 36 32 = K := Witness.arg2_data2 size_SEL_allowance _ _
  have hm : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) K = K := by
    decide
  unfold callKeys
  rw [hc, h1, h2, hm]

/-! ## The part of `Sep` that the kernel computes -/

/-- Computed by the kernel: the allowance slot of `(K, K)` is not slot 1. -/
theorem allow_ne_total : mapSlot K (mapSlot K 3) ≠ (1 : U256) := by decide +kernel

/-- Computed by the kernel: the nonce slot of `K` is not slot 1. -/
theorem nonce_ne_total : mapSlot K 4 ≠ (1 : U256) := by decide +kernel

/-- Computed by the kernel: the allowance slot of `(K, K)` is not the nonce slot of `K`. -/
theorem allow_ne_nonce : mapSlot K (mapSlot K 3) ≠ mapSlot K 4 := by decide +kernel

/-- Computed by the kernel: the `wards` slot of `K` is not slot 1. -/
theorem ward_ne_total : mapSlot K 0 ≠ (1 : U256) := by decide +kernel

/-! ## The part of `Sep` that stays a hypothesis: 5 named facts -/

/-- The facts about keccak that `Sep` asks for the call `m0` and that Lean cannot prove: each
is a statement over the 2^160 address words. NOT proved; this is the whole list. -/
structure KeyFacts : Prop where
  /-- Slot 1 (the total supply) is the balance slot of no address. -/
  total : Supply.NotBal 2 1
  /-- No other address word has the balance slot of `K`. -/
  uniq : Supply.UniqBal 2 K
  /-- The allowance slot of `(K, K)` is the balance slot of no address. -/
  allow : Supply.NotBal 2 (mapSlot K (mapSlot K 3))
  /-- The nonce slot of `K` is the balance slot of no address. -/
  nonce : Supply.NotBal 2 (mapSlot K 4)
  /-- The `wards` slot of `K` is the balance slot of no address. -/
  ward : Supply.NotBal 2 (mapSlot K 0)

theorem mem3 {x : U256} (h : x ∈ [K, K, K]) : x = K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at h
  exact h

/-- `Sep` for the three keys `[K, K, K]` is exactly `KeyFacts`: the list cannot be made
shorter, and nothing else is hidden in `Sep`. -/
theorem sep_iff : Sep [K, K, K] ↔ KeyFacts := by
  constructor
  · intro h
    exact {
    total := h.total
    uniq := h.uniq K (by simp)
    allow := (h.allow K (by simp) K (by simp)).1
    nonce := (h.nonce K (by simp)).1
    ward := (h.ward K (by simp)).1
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
    nonce := fun x hx => by
      rw [mem3 hx]
      refine ⟨h.nonce, nonce_ne_total, fun o ho s hs => ?_⟩
      rw [mem3 ho, mem3 hs]
      exact allow_ne_nonce
    ward := fun x hx => by
      rw [mem3 hx]
      exact ⟨h.ward, ward_ne_total⟩
    }

/-- `Sep` of the call `m0` is exactly `KeyFacts`. -/
theorem sep_m0_iff (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    Sep (callKeys (m0 b t C)) ↔ KeyFacts := by
  rw [callKeys_m0]
  exact sep_iff

/-! ## The start invariant and `NoDelegation1` -/

/-- The start invariant holds in the state with all-zero storage. -/
theorem inv_start (C : Address) : Inv C (sState C []) :=
  inv_zeroBase C _ (fun k => by
    simp [sState, State.TransactionState.ofBlock, State.TransactionState.getStorage,
      State.State.getStorage, State.StorageMap.slot, slotMap])

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

/-- THE CLOSED INSTANCE of `supply_preserved`: the call `m0` (`allowance(K, K)` from
`HOLDER`) from the state with all-zero storage. Every run that ends with no error ends
in a state where the invariant holds. The only hypotheses left are the fork range and
`KeyFacts` (the 5 facts about keccak that cannot be proved). -/
theorem supply_m0 (hfork : .berlin ≤ fork) (_hglam : fork < .glamsterdam) (keys : KeyFacts)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    {substate : Substate} {gas bound : Nat} {runChild : MessageRunner fork Nat bound}
    {evm s : Evm fork Nat}
    (start : At CODE (m0 b t C) 0 [] .empty gas (sState C []) substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv C s.state := by
  have hdata : (m0 b t C).data = data2 SEL_allowance K K := rfl
  have hsz : (m0 b t C).data.size = 68 := by
    rw [hdata]
    exact size_data2 size_SEL_allowance _ _
  have hsl : selector (m0 b t C).data = selector SEL_allowance := by
    rw [hdata]
    exact selector_data2 size_SEL_allowance _ _
  exact supply_preserved hfork (by rw [hsz]; decide) (by rw [hsl]; decide)
    ((sep_m0_iff b t C).mpr keys) (inv_start C) start hrun hok

end UsddVerify.Instance

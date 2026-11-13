import BnbVerify.Bnb.Map
import EthLib.Execution.Proofs.Evm.Machine.Memory

/-!
# Calls that reach no function body: the nonpayable revert and the fallback

The parts below keep their own headers:

- The nonpayable revert
- The fallback: a call that names no function
-/

section

/-!
## The nonpayable revert

Every entry of the selector table starts with the same eleven bytes, a copy per function:
`JUMPDEST CALLVALUE ISZERO PUSH2 (entry + 11) JUMPI PUSH1 0 DUP1 REVERT`.
With a nonzero call value the JUMPI falls through and the run reverts with no output.

- `valueRevert`: the block at any of the 15 destinations of the table.
- `spec`: from pc 0, a call whose selector is the key of entry `i` of the table and whose value
  is not 0 reverts, with no output, the state and substate unchanged, and `84 + 22 * (i + 1)`
  gas spent.
-/

namespace BnbVerify.Nonpayable

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The destinations of the selector table, the entry points of the 15 functions. -/
def DESTS : List Nat := ENTRIES.map (·.2.toNat)

/-- At each entry point, a call with a nonzero value reverts with no output for 25 gas. -/
theorem valueRevert (hfork : .berlin ≤ fork) {e : Nat} (he : e ∈ DESTS)
    (hv : message.value ≠ 0) {x : U256} {gas : Nat} (hg : 25 ≤ gas) :
    Gas.SpecG fork (At CODE message e [x] MEM0 gas state substate)
      (Halted true .empty (gas - 25) state substate) := by
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have hc : isZero message.value = 0 := by
    unfold isZero
    split
    · contradiction
    · rfl
  simp only [DESTS, ENTRIES, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step unR 0x15 instruction_iszero
    step pushAnyR 2
    step jumpi0R hc
    step pushR 1 (0 : U256)
    step dupR 0
    refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
    rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
    refine ⟨hr, he, ?_, ?_, hs, hss⟩
    · rw [ho]; simp [memoryReadBytes]
    · rw [hgas, hz]; gas_ok

/-- The table tests `i + 1` entries for the key of entry `i`, and goes to its destination. -/
theorem table_entry : ∀ i : Fin 15,
    tested (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) ENTRIES = i.val + 1 ∧
      branch (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) 52 (entrySize 4 2) ENTRIES =
        ENTRIES[i].2.toNat := by
  decide +kernel

/-- The nonpayable revert of every function, from Berlin.

The call data is not empty and has a size below `2^256`, its selector is the key of entry `i` of
the table (`ENTRIES`, in the order of the bytecode; see docs/MAP.md), and the call value is not 0.

Then the run reverts with empty output, before any read of storage: the state and substate are
the ones the frame started with, and the run pays `84 + 22 * (i + 1)` gas: 59 for the prelude,
22 for each entry tested, and 25 at the entry. -/
theorem spec (hfork : .berlin ≤ fork) (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (i : Fin 15)
    (hsel : selector message.data = ENTRIES[i].1.toNat) (hv : message.value ≠ 0) {gas : Nat}
    (hg : 84 + 22 * (i.val + 1) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (84 + 22 * (i.val + 1))) state substate) := by
  obtain ⟨ht, hb⟩ := table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := valueRevert (state := state) (substate := substate) hfork
    (e := ENTRIES[i].2.toNat) (List.mem_map.2 ⟨ENTRIES[i], List.getElem_mem _, rfl⟩) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 59 - 22 * (i.val + 1))
    (by omega)
  refine Gas.SpecG.seq h1 (h2.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

end BnbVerify.Nonpayable

end

section

/-!
## The fallback: a call that names no function

The BNB contract (Solidity 0.4.12) has the payable fallback `function() payable {}`. Read off the
bytecode:

- At 5, `CALLDATASIZE ISZERO PUSH2 0x00d9 JUMPI` sends a call with no call data to 217.
- The selector table (52 to 216) falls through to 217 when no entry has the selector.
- At 217, `JUMPDEST PUSH2 0x00e0 JUMPDEST JUMPDEST JUMP`, then at 224 `JUMPDEST STOP`: the run
  ends with success and no output.

Neither path reads the call value: a call that names no function succeeds with any value (the
contract accepts ETH), writes nothing and logs nothing.

- `spec_unknown`: a call data that is not empty whose selector (its first four bytes, zeros past
  its end) is no key of the table ⇒ STOP, no output, state and substate unchanged, gas 404
  (`59 + 22 * 15` through the table, then 15).
- `spec_empty`: no call data ⇒ STOP, no output, state and substate unchanged, gas 51.
-/

namespace BnbVerify.Fallback

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The block at 217: `JUMPDEST PUSH2 224 JUMPDEST JUMPDEST JUMP`, then `JUMPDEST STOP`. -/
theorem stop217 {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {gas : Nat} (hg : 15 ≤ gas) :
    Gas.SpecG fork (At CODE message 217 rest M gas state substate)
      (Halted false .empty (gas - 15) state substate) := by
  step jumpdestR
  step pushR 2 (224 : U256)
  step jumpdestR
  step jumpdestR
  step jumpR
  step jumpdestR
  step Gas.reshapeG (g' := gas - 15) rfl rfl (by gas_ok)
  exact Gas.stopG (by code_fact) (by code_fact)

/-- A call data that is not empty whose selector is no key of the table: the table falls through
to 217 and the run stops with success and no output, for any call value. -/
theorem spec_unknown (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256)
    (hunk : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 404 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 404) state substate) := by
  have hne : ∀ e ∈ ENTRIES, e.1 ≠ BitVec.ofNat 256 (selector message.data) := by
    intro e he heq
    exact hunk (List.mem_map.mpr ⟨e, he, heq⟩)
  have ht := tested_of_forall_ne hne
  have hb := branch_of_forall_ne (pc := 52) (size := entrySize 4 2) hne
  have hlen : ENTRIES.length = 15 := rfl
  rw [hlen] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq (h1.seq (repc (pc' := 217) (by decide))) ?_
  refine (stop217 (by simp) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- A call with no call data: the prelude jumps to 217 and the run stops with success and no
output, for any call value. -/
theorem spec_empty (hsize : message.data.size = 0)
    {gas : Nat} (hg : 51 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false .empty (gas - 51) state substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1R 0x60
  step push1R 0x40
  step Gas.mstoreG (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step Gas.reshapeG rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step unR 0x15 instruction_iszero
  step pushR 2 0x00d9
  step jumpiR (isZero_size_empty hsize)
  refine (repc (pc' := 217) (by decide)).seq ?_
  refine (stop217 (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end BnbVerify.Fallback

end

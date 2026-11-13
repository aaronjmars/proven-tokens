import ShibVerify.Shib.Map
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

Every entry of the selector table starts with the same twelve bytes, a copy per function:
`JUMPDEST CALLVALUE DUP1 ISZERO PUSH2 (entry + 12) JUMPI PUSH1 0 DUP1 REVERT`.
With a nonzero call value the JUMPI falls through and the run reverts with no output.

- `valueRevert`: the block at any of the 12 destinations of the table.
- `spec` / `runFrame_spec`: from pc 0, a call whose selector is the key of entry `i` of the table
  and whose value is not 0 reverts, with no output, the state and substate unchanged, and
  `90 + 22 * (i + 1)` gas spent.
-/

namespace ShibVerify.Nonpayable

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The destinations of the selector table, the entry points of the 12 functions. -/
def DESTS : List Nat := ENTRIES.map (·.2.toNat)

/-- At each entry point, a call with a nonzero value reverts with no output for 28 gas. -/
theorem valueRevert (hfork : .berlin ≤ fork) {e : Nat} (he : e ∈ DESTS)
    (hv : message.value ≠ 0) {x : U256} {gas : Nat} (hg : 28 ≤ gas) :
    Gas.SpecG fork (At CODE message e [x] MEM0 gas state substate)
      (Halted true .empty (gas - 28) state substate) := by
  have hz : extendMemory MEM0.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have hc : isZero message.value = 0 := by
    unfold isZero
    split
    · contradiction
    · rfl
  simp only [DESTS, ENTRIES, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    step jumpdestR
    step Gas.callvalueG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
    step dupR 0
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
theorem table_entry : ∀ i : Fin 12,
    tested (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) ENTRIES = i.val + 1 ∧
      branch (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) 54 (entrySize 4 2) ENTRIES =
        ENTRIES[i].2.toNat := by
  decide +kernel

/-- The nonpayable revert of every function, from Berlin.

The call data has `4 ≤ size < 2^256`, its selector is the key of entry `i` of the table
(`ENTRIES`, in the order of the bytecode; see docs/MAP.md), and the call value is not 0.

Then the run reverts with empty output, before any read of storage: the state and substate are
the ones the frame started with, and the run pays `90 + 22 * (i + 1)` gas: 62 for the prelude,
22 for each entry tested, and 28 at the entry. -/
theorem spec (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (i : Fin 12)
    (hsel : selector message.data = ENTRIES[i].1.toNat) (hv : message.value ≠ 0) {gas : Nat}
    (hg : 90 + 22 * (i.val + 1) ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - (90 + 22 * (i.val + 1))) state substate) := by
  obtain ⟨ht, hb⟩ := table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  have h2 := valueRevert (state := state) (substate := substate) hfork
    (e := ENTRIES[i].2.toNat) (List.mem_map.2 ⟨ENTRIES[i], List.getElem_mem _, rfl⟩) hv
    (x := BitVec.ofNat 256 (selector message.data)) (gas := gas - 62 - 22 * (i.val + 1))
    (by omega)
  refine Gas.SpecG.seq h1 (h2.consequence (fun _ h => h) ?_)
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

end ShibVerify.Nonpayable

end

section

/-!
## The fallback: a call that names no function

TokenMintERC20Token (Solidity 0.5.0) has no fallback function. Read off the bytecode:

- At 5, `PUSH1 4 CALLDATASIZE LT PUSH2 0x00ba JUMPI` sends a call with fewer than 4 bytes of call
  data to 186.
- The selector table (54 to 185) falls through to 186 when no entry has the selector.
- At 186, `JUMPDEST PUSH1 0 DUP1 REVERT`: the run reverts with no output.

Neither path checks the call value: a call with value that names no function also reverts.

- `spec_unknown`: 4 bytes or more whose first four are no key of the table ⇒ REVERT, no output,
  state and substate unchanged, gas 333 (`62 + 22 * 12` through the table, then 7).
- `spec_short`: fewer than 4 bytes ⇒ REVERT, no output, state and substate unchanged, gas 46.
-/

namespace ShibVerify.Fallback

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The block at 186: `JUMPDEST PUSH1 0 DUP1 REVERT`, a revert with no output. -/
theorem revert186 (hfork : .berlin ≤ fork) {rest : List U256} (hrest : rest.length ≤ 16)
    {M : ByteArray} {gas : Nat} (hg : 7 ≤ gas) :
    Gas.SpecG fork (At CODE message 186 rest M gas state substate)
      (Halted true .empty (gas - 7) state substate) := by
  have hz : extendMemory M.size [((0 : U256), (0 : U256))] = ⟨0, 0⟩ := by
    simp [extendMemory]
  step jumpdestR
  step pushR 1 (0 : U256)
  step dupR 0
  refine (Gas.revertG (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) (by rw [hz]; gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, ?_, hs, hss⟩
  · rw [ho]; simp [memoryReadBytes]
  · rw [hgas, hz]; gas_ok

/-- A call of 4 bytes or more whose selector is no key of the table: the table falls through to
186 and the run reverts with no output, for any call value. -/
theorem spec_unknown (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256)
    (hunk : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 333 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 333) state substate) := by
  have hne : ∀ e ∈ ENTRIES, e.1 ≠ BitVec.ofNat 256 (selector message.data) := by
    intro e he heq
    exact hunk (List.mem_map.mpr ⟨e, he, heq⟩)
  have ht := tested_of_forall_ne hne
  have hb := branch_of_forall_ne (pc := 54) (size := entrySize 4 2) hne
  have hlen : ENTRIES.length = 12 := rfl
  rw [hlen] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  refine Gas.SpecG.seq (h1.seq (repc (pc' := 186) (by decide))) ?_
  refine (revert186 hfork (by simp) (by omega)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; omega, hs, hss⟩

/-- A call with fewer than 4 bytes of call data: the prelude jumps to 186 and the run reverts
with no output, for any call value. -/
theorem spec_short (hfork : .berlin ≤ fork) (hsize : message.data.size < 4)
    {gas : Nat} (hg : 46 ≤ gas) :
    Gas.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted true .empty (gas - 46) state substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1R 0x80
  step push1R 0x40
  step Gas.mstoreG (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step Gas.reshapeG rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1R 0x04
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binR 0x10 (instruction_of_stackOnlyStep rfl)
  step pushR 2 0x00ba
  step jumpiR (by
    have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
    rw [ite_eq_left hsize]
    decide)
  refine (repc (pc' := 186) (by decide)).seq ?_
  refine (revert186 hfork (by simp) (by gas_ok)).consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  exact ⟨hr, he, ho, by rw [hgas]; gas_ok, hs, hss⟩

end ShibVerify.Fallback

end

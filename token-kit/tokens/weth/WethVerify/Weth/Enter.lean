import TokenKit.Evm.Rules
import TokenKit.Evm.Stack
import WethVerify.Weth.Steps
import WethVerify.Weth.Map

/-!
# From pc 0 to the entry of a function, or to the fallback

Every run of `CODE` from pc 0 goes one of three ways, by its call data:

- `enter`: 4 bytes or more whose selector is the key of entry `i` of the selector table: the run
  goes to the destination of that entry, with the selector on the stack, for
  `62 + 22 * (i + 1)` gas.
- `enterOther`: 4 bytes or more whose selector is no key of the table: the table falls through
  to the fallback at 175, with the selector on the stack, for `62 + 22 * 11 = 304` gas.
- `enterShort`: fewer than 4 bytes: the prelude jumps to the fallback at 175 with an empty
  stack, for 39 gas.

In each case the memory is the one of the prelude: two zero words and the free memory pointer
0x60, as `memW`. The fallback of WETH9 is payable and runs the code of `deposit()`; no entry
checks the size of the call data.

The key, the destination and the gas of `enter` are numerals, with the equations to the table as
side goals (closed by `decide` where the rule is used).
-/

namespace WethVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The memory of the prelude as words. -/
theorem MEM0_eq : MEM0 = memW [0, 0, 96] := memW_initW 0x60

/-- The table tests `i + 1` entries for the key of entry `i`, and goes to its destination. -/
theorem table_entry : ∀ i : Fin 11,
    tested (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) ENTRIES = i.val + 1 ∧
      branch (BitVec.ofNat 256 (ENTRIES[i].1.toNat)) 54 (entrySize 4 2) ENTRIES =
        ENTRIES[i].2.toNat := by
  decide +kernel

theorem enter (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (i : Fin 11) {key dest N : Nat} (hkey : ENTRIES[i].1.toNat = key)
    (hdest : ENTRIES[i].2.toNat = dest) (hN : 62 + 22 * (i.val + 1) = N)
    (hsel : selector message.data = key) {gas : Nat} (hg : N ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message dest [BitVec.ofNat 256 (selector message.data)]
        (memW [0, 0, 96]) (gas - N) state substate) := by
  subst hkey hdest hN
  obtain ⟨ht, hb⟩ := table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  exact Gas.Triple.seqL h1 (restate rfl rfl MEM0_eq (by omega) rfl rfl)

/-- A call of 4 bytes or more whose selector is no key of the table reaches the fallback at 175
with the selector on the stack. -/
theorem enterOther (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} (hg : 304 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 175 [BitVec.ofNat 256 (selector message.data)]
        (memW [0, 0, 96]) (gas - 304) state substate) := by
  have hne : ∀ e ∈ ENTRIES, e.1 ≠ BitVec.ofNat 256 (selector message.data) := by
    intro e he heq
    exact hsel (List.mem_map.mpr ⟨e, he, heq⟩)
  have ht := tested_of_forall_ne hne
  have hb := branch_of_forall_ne (pc := 54) (size := entrySize 4 2) hne
  have hlen : ENTRIES.length = 11 := rfl
  rw [hlen] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  exact Gas.Triple.seqL h1 (restate (by decide) rfl MEM0_eq (by omega) rfl rfl)

/-- A call with fewer than 4 bytes of call data reaches the fallback at 175 with an empty
stack. -/
theorem enterShort (hsize : message.data.size < 4) {gas : Nat} (hg : 39 ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 175 [] (memW [0, 0, 96]) (gas - 39) state substate) := by
  have hext : extendMemory ByteArray.empty.size [((BitVec.ofNat 256 (0x40 : UInt8).toNat : U256),
      (32 : U256))] = ⟨9, 96⟩ := by decide
  step push1R 0x60
  step push1R 0x40
  step Gas.mstoreG (by code_fact) (by code_fact) (by simp only [hext]; omega)
  step Gas.reshapeG rfl (by rw [hext]) (show _ = gas - 18 by simp only [hext]; omega)
  step push1R 0x04
  step Gas.calldatasizeG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  step binR 0x10 (instruction_of_stackOnlyStep rfl)
  step pushR 2 0x00af
  step jumpiR (by
    have h4 : (BitVec.ofNat 256 (UInt8.toNat 4) : U256).toNat = 4 := by decide
    simp only [lessThan, h4, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show message.data.size < 2 ^ 256 by omega)]
    rw [ite_eq_left hsize]
    decide)
  exact restate (by decide) rfl MEM0_eq (by gas_ok) rfl rfl

end WethVerify

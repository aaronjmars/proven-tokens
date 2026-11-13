import TokenKit.Evm.Rules
import TokenKit.Evm.Stack
import BnbVerify.Bnb.Steps
import BnbVerify.Bnb.Spec.Dispatch

/-!
# From pc 0 to the entry of a function

- `enter`: a call whose selector is the key of entry `i` of the selector table runs from pc 0 to
  the destination of that entry, with the selector on the stack and the memory of the prelude
  (two zero words and the free memory pointer 0x60, as `memW`), for `59 + 22 * (i + 1)` gas.

The key, the destination and the gas are numerals, with the equations to the table as side goals
(closed by `decide` where the rule is used).
-/

namespace BnbVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

theorem enter (hsize : 1 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (i : Fin 15) {key dest N : Nat} (hkey : ENTRIES[i].1.toNat = key)
    (hdest : ENTRIES[i].2.toNat = dest) (hN : 59 + 22 * (i.val + 1) = N)
    (hsel : selector message.data = key) {gas : Nat} (hg : N ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message dest [BitVec.ofNat 256 (selector message.data)]
        (memW [0, 0, 96]) (gas - N) state substate) := by
  subst hkey hdest hN
  obtain ⟨ht, hb⟩ := Nonpayable.table_entry i
  rw [← hsel] at ht hb
  have h1 := dispatch (state := state) (substate := substate) hsize hsize' (gas := gas)
    (by rw [ht]; omega)
  rw [ht, hb] at h1
  exact Gas.Triple.seqL h1 (restate rfl rfl (memW_initW 96) (by omega) rfl rfl)

end BnbVerify

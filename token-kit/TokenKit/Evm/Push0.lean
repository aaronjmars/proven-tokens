import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Precompile
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# PUSH0 (EIP-3855, from Shapella) in the `At` form of the logic mode

Moved from the local library of ENA (`Ena/Lib.lean`), which keeps its copy under the same names:
a project imports this file or its local copy, not both. The generators use `push0L` and
`toBerlin` with the configuration key `min_fork` ("shapella").

- `toBerlin`, `toParis`: Shapella is after Berlin and Paris.
- `push0GA`, `push0L`: PUSH0 pushes 0 for 2 gas.
-/

namespace TokenKit

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- Shapella is after Berlin: the rules of the shared library that ask for Berlin hold from
Shapella. -/
theorem toBerlin (h : Fork.shapella ≤ fork) : Fork.berlin ≤ fork := Nat.le_trans (by decide) h

/-- Shapella is after Paris. -/
theorem toParis (h : Fork.shapella ≤ fork) : Fork.paris ≤ fork := Nat.le_trans (by decide) h

/-- PUSH0 (EIP-3855, from Shapella) pushes the word 0, for 2 gas, over the steps from frames
that are monotone in gas and never abort with less gas. (The EthLib of the build box has the
rule for PUSH1 to PUSH32 only; a later EthLib has this rule as `Logic.push0GA`.) -/
theorem push0GA (hfork : .shapella ≤ fork) {stack : List U256} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x5f) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareGA fork
      (Logic.At code message pc stack memory gas state substate returnData)
      (Logic.At code message (pc + 1) ((0 : U256) :: stack) memory (gas - 2) state substate
        returnData) := by
  apply Logic.At.ruleGA hlt hbyte
    (ofByte_of_decode (op := .push 0) rfl (by simpa [Op.since] using hfork))
    (instruction_push 0) (runMono_pushN 0) (noAbort_pushN 0)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
  rw [pushN_of_length_lt (by rw [hst]; exact hstack)]
  simp only [Fin.val_zero, ↓reduceIte, OPCODE_PUSH0, BASE]
  rw [charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc],
    by simp [hst, pushData, bufferRead, EthLib.Base.bytesToNat], hmem, by simp [hg], hrun, herr,
    hout, hs, hss, hrd⟩

/-- PUSH0 (EIP-3855, from Shapella) pushes the word 0, for 2 gas. -/
theorem push0L (hfork : .shapella ≤ fork) {stack : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x5f) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) ((0 : U256) :: stack) memory (gas - 2) state substate) :=
  liftAt fun _ => (push0GA hfork hlt hbyte hgas hstack).toG

end TokenKit

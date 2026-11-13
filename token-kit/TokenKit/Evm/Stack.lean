import UsdtVerify.Evm.GasRules
import UsdtVerify.Evm.Steps

/-!
# Stack rules with the stack after the step spelled out

- `swap1K` .. `swap16K`: SWAPn with the two words exchanged in an explicit stack (the rule
  `Gas.swapG` states the stack after the step with `List.set`).
- `foldK`: replace the word on top of the stack by an equal one (a numeral, for an operation on
  numerals).
- `haltGas`: a specification to a halt with an equal gas.

Generated once by `scripts/gen_paths.py`'s companion snippet; nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

theorem swap1K {a0 a1 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (0 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: rest) memory gas state substate)
      (At code message (pc + 1) (a1 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 0 hlt hbyte rfl hgas

theorem swap2K {a0 a1 a2 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (1 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: rest) memory gas state substate)
      (At code message (pc + 1) (a2 :: a1 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 1 hlt hbyte rfl hgas

theorem swap3K {a0 a1 a2 a3 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (2 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: rest) memory gas state substate)
      (At code message (pc + 1) (a3 :: a1 :: a2 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 2 hlt hbyte rfl hgas

theorem swap4K {a0 a1 a2 a3 a4 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (3 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: rest) memory gas state substate)
      (At code message (pc + 1) (a4 :: a1 :: a2 :: a3 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 3 hlt hbyte rfl hgas

theorem swap5K {a0 a1 a2 a3 a4 a5 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (4 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: rest) memory gas state substate)
      (At code message (pc + 1) (a5 :: a1 :: a2 :: a3 :: a4 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 4 hlt hbyte rfl hgas

theorem swap6K {a0 a1 a2 a3 a4 a5 a6 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (5 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: rest) memory gas state substate)
      (At code message (pc + 1) (a6 :: a1 :: a2 :: a3 :: a4 :: a5 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 5 hlt hbyte rfl hgas

theorem swap7K {a0 a1 a2 a3 a4 a5 a6 a7 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (6 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest) memory gas state substate)
      (At code message (pc + 1) (a7 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 6 hlt hbyte rfl hgas

theorem swap8K {a0 a1 a2 a3 a4 a5 a6 a7 a8 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (7 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest) memory gas state substate)
      (At code message (pc + 1) (a8 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 7 hlt hbyte rfl hgas

theorem swap9K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (8 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: rest) memory gas state substate)
      (At code message (pc + 1) (a9 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 8 hlt hbyte rfl hgas

theorem swap10K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (9 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: rest) memory gas state substate)
      (At code message (pc + 1) (a10 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 9 hlt hbyte rfl hgas

theorem swap11K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (10 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: rest) memory gas state substate)
      (At code message (pc + 1) (a11 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 10 hlt hbyte rfl hgas

theorem swap12K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (11 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: rest) memory gas state substate)
      (At code message (pc + 1) (a12 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 11 hlt hbyte rfl hgas

theorem swap13K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (12 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: rest) memory gas state substate)
      (At code message (pc + 1) (a13 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 12 hlt hbyte rfl hgas

theorem swap14K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (13 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: rest) memory gas state substate)
      (At code message (pc + 1) (a14 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 13 hlt hbyte rfl hgas

theorem swap15K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (14 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: rest) memory gas state substate)
      (At code message (pc + 1) (a15 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 14 hlt hbyte rfl hgas

theorem swap16K {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = (0x90 + (15 : Fin 16).val).toUInt8) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a16 :: rest) memory gas state substate)
      (At code message (pc + 1) (a16 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: a0 :: rest) memory (gas - 3) state substate) :=
  Gas.swapG 15 hlt hbyte rfl hgas

/-- Replace the word on top of the stack by an equal one. -/
theorem foldK {x y : U256} {rest : List U256} (h : x = y) :
    Gas.HoareG fork (At code message pc (x :: rest) memory gas state substate)
      (At code message pc (y :: rest) memory gas state substate) :=
  Gas.reshapeG (by rw [h]) rfl rfl

/-- EQ of a word with itself is 1. -/
theorem equal_self (x : U256) : equal x x = 1 := if_pos rfl

/-- A specification to a halt, with an equal gas. -/
theorem haltGas {P : Evm fork Nat → Prop} {rev : Bool} {out : ByteArray} {g g' : Nat}
    {st : State.TransactionState} {ss : Substate}
    (h : Gas.SpecG fork P (Halted rev out g st ss)) (hg : g = g') :
    Gas.SpecG fork P (Halted rev out g' st ss) := hg ▸ h

end TokenKit

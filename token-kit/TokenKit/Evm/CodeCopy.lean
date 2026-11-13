import TokenKit.Evm.Opt
import TokenKit.Evm.Env08
import TokenKit.Evm.Note
import TokenKit.Evm.TopByte

/-!
# CODECOPY of any number of bytes into a raw memory, and NUMBER

Solidity 0.5 with ABIEncoderV2 (UNI: `safe96(n, "message")`, `sub96(a, b, "message")`) copies the
text of an error message from the code to memory before the check that may use it, on every
path. `codecopyK` of Evm/Env08.lean is for one word; this file has the rule for any numeral
size, with the copied bytes as the term `copied code f k` (Evm/Note.lean), and the lemmas that
carry the known words of a raw memory over such a write. The generator uses them with
`paths.code_copy = true`.

- `codecopyRK`: CODECOPY with the size of the memory, its growth and the three operands as
  numerals.
- `size_copiedC`, `load_rawC`, `read_rawC`: the size of the copied bytes, and a known word or a
  range of bytes that a write of copied bytes leaves alone.
- `numberL`: NUMBER pushes the number of the block of the message.
- `logSubOne`, `logOneK`: the substate after a LOG1 and the rule of LOG1 of bytes inside the
  memory; `logFourZK`: LOG4 of no bytes, for any offset; `logOne`, `logs_logSubOne`: a log with
  one topic, for the readable corollaries.
- `logStuckW`: a LOG in a static frame is stuck (for a LOG before the first SSTORE of a path).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- CODECOPY, with the size of the memory, its growth and the three operands as numerals: the
bytes `copied code f k` are written at `o`. It pays 3, 3 a word and the growth of memory. -/
theorem codecopyRK {start offset size : U256} {rest : List U256} {sz c n o f k w : Nat}
    {m' : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x39) (hsz : memory.size = sz)
    (hext : extendMemory sz [(start, size)] = ⟨c, n⟩) (ho : start.toNat = o)
    (hf : offset.toNat = f) (hk : size.toNat = k) (hw : wordCount k = w)
    (hmem : memoryWrite (memoryExtend memory n) o (copied code f k) = m')
    (hgas : 3 + 3 * w + c ≤ gas) :
    Logic.HoareG fork
      (At code message pc (start :: offset :: size :: rest) memory gas state substate)
      (At code message (pc + 1) rest m' (gas - (3 + 3 * w + c)) state substate) := by
  subst hsz ho hf hk hw hmem
  have h := codecopyL (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (rest := rest) (start := start) (offset := offset)
    (size := size) (memory := memory) (gas := gas) hlt hbyte (by rw [hext]; exact hgas)
  rw [hext] at h
  exact h

/-- The copied bytes are as many as asked for. -/
theorem size_copiedC (data : ByteArray) (f k : Nat) : (copied data f k).size = k := by
  simp [ByteArray.size, bufferRead_length]

/-- A write of copied bytes at `o` leaves the known word at `a`, when the two do not overlap. -/
theorem load_rawC {m data : ByteArray} {sz n o f k a : Nat} {w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz)
    (hfit : o + k ≤ sz + n) (ha : a + 32 ≤ sz) (hd : a + 32 ≤ o ∨ o + k ≤ a) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (copied data f k)) a 32) 0 32 =
      w := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_copiedC, hs]; exact hfit)
      (by rw [size_copiedC]; exact hd),
    memoryReadBytes_memoryExtend (by omega)]
  exact h

/-- A read of bytes that a write of copied bytes does not touch. -/
theorem read_rawC {m data : ByteArray} {sz n o f k a j : Nat} (hs : m.size = sz)
    (hfit : o + k ≤ sz + n) (ha : a + j ≤ sz) (hd : a + j ≤ o ∨ o + k ≤ a) :
    memoryReadBytes (memoryWrite (memoryExtend m n) o (copied data f k)) a j =
      memoryReadBytes m a j := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_copiedC, hs]; exact hfit)
      (by rw [size_copiedC]; exact hd),
    memoryReadBytes_memoryExtend (by omega)]

/-- NUMBER runs the read of the number of the block. -/
theorem instruction_number : instruction (Meter := Nat) fork .number =
    some (readFrame OPCODE_NUMBER fun evm => BitVec.ofNat 256 evm.message.blockEnv.number) := by
  first
    | rfl
    | simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
        environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- NUMBER pushes the number of the block of the message, for 2 gas. -/
theorem numberL {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x43)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.number :: stack) memory
        (gas - 2) state substate) :=
  liftAt fun _ => Logic.push_of_readFrameG hlt hbyte
    (ofByte_of_decode (op := .number) rfl (Fork.frontier_le _)) instruction_number
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- The substate after a LOG1 of the contract `target`: one more log, with one topic. -/
abbrev logSubOne (substate : Substate) (target : Address) (t1 : U256) (data : ByteArray) :
    Substate :=
  { substate with
    logs := substate.logs.push
      { address := target
        topics := [U256.toBeBytes t1]
        data := data } }

/-- LOG1 of bytes inside the memory. -/
theorem logOneK {start size t1 : U256} {rest : List U256} {sz o k c : Nat} {d : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa1) (hstatic : message.isStatic = false)
    (hsz : memory.size = sz) (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hcost : logCost 1 size = c) (hdata : memoryReadBytes memory o k = d) (hgas : c ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: size :: t1 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - c) state
        (logSubOne substate message.currentTarget t1 d)) := by
  subst hsz ho hk hcost hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 1) (byte := 0xa1) (start := start)
    (size := size) (words := [t1]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero]
  rfl

/-- LOG4 of no bytes: any offset, any memory, 1875 gas. -/
theorem logFourZK {start t1 t2 t3 t4 : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa4) (hstatic : message.isStatic = false)
    (hgas : 1875 ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: (0 : U256) :: t1 :: t2 :: t3 :: t4 :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest memory (gas - 1875) state
        (logSub4 substate message.currentTarget t1 t2 t3 t4 .empty)) := by
  have hext : extendMemory memory.size [(start, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_length_eq_zero _ _
  have hcost : logCost (4 : Fin 5).val (0 : U256) = 1875 := by decide
  have h0 : (0 : U256).toNat = 0 := by decide
  have hd : memoryReadBytes memory start.toNat (0 : U256).toNat = ByteArray.empty := by
    rw [h0]
    simp [memoryReadBytes]
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 4) (byte := 0xa4) (start := start)
    (size := 0) (words := [t1, t2, t3, t4]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext, hcost]; exact hgas)
  rw [hext, hcost] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero, hd]
  rfl

/-- A LOG in a static frame is `Stuck`, at any fork and any gas: EthLib's `logStep` ends with
`writeInStaticContext` (or with an earlier error), never with a frame. The generator uses it
(`paths.log_before_sstore`) for a LOG that comes before the first SSTORE of a path. -/
theorem logStuckW {n : Fin 5} {byte : UInt8} {stack : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (hdec : Op.decode byte = some (.log n))
    (hbad : message.isStatic = true) :
    Gas.HoareG fork (At code message pc stack memory gas state substate) Gas.Stuck := by
  refine Gas.At.stuck hlt hbyte (ofByte_of_decode hdec (Fork.frontier_le _)) (instruction_log n)
    (fun low hm _ _ _ => ?_) (by cases n using Fin.cases <;> rfl)
  rcases h : logStep n.val low with e | b
  · exact .inl ⟨e, rfl⟩
  · exact absurd h (logStep_ne_ok_of_isStatic (by rw [hm]; exact hbad))

/-- A log of the contract `C` with one topic. -/
abbrev logOne (C : Address) (t1 : U256) (d : ByteArray) : Blocks.Log :=
  { address := C
    topics := [U256.toBeBytes t1]
    data := d }

/-- The logs after a LOG1. -/
theorem logs_logSubOne (ss : Substate) (C : Address) (t1 : U256) (d : ByteArray) :
    (logSubOne ss C t1 d).logs = ss.logs.push (logOne C t1 d) := rfl

end TokenKit

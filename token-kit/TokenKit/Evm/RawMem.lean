import TokenKit.Evm.Mem
import TokenKit.Evm.Rules
import TokenKit.Evm.Logic

/-!
# Known words of a raw memory

A memory of words (`memW`) covers the code that writes whole words at multiples of 32. Old
Solidity writes words at other offsets (the `0x1901` prefix of an EIP-712 digest at 0x180, then
the domain separator at 0x182), and from there on the memory is a raw term: a chain of
`memoryWrite (memoryExtend m n) o (wordBytes v)`. The generator (`paths.raw_words` of
gen_paths.py) keeps, for such a memory, its size and the words it is known to hold: a fact
`loadWord (memoryReadBytes m o 32) 0 32 = v` per offset. The lemmas here carry those facts over
a write and turn them into the bytes that KECCAK256 and LOG read.

- `wordBytes_loadWord`: 32 bytes are the bytes of the word they spell.
- `load_rawW`, `load_rawW_self`: the known word at `a` after a write of a word at `o`.
- `readWord_raw`, `read0_raw`: the bytes of one known word, and of the two known words at 0
  and 32 (the input of the hash of a mapping slot).
- `read_rawW`, `read4_raw`: a read of bytes that a write leaves, and the 128 bytes of four
  known words.
- `keccakK`: KECCAK256 of bytes inside the memory, with the bytes as a side goal.
- `timestampL`: TIMESTAMP pushes the time stamp of the block of the message.

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

/-- 32 bytes are the bytes of the word they spell. -/
theorem wordBytes_loadWord {b : ByteArray} (hb : b.size = 32) :
    wordBytes (loadWord b 0 32) = b := by
  have h32 : bufferRead b 0 32 = b.data.toList := by
    have h := bufferRead_zero_size b
    rwa [hb] at h
  have hlen : b.data.toList.length = 32 := by
    rw [Array.length_toList, ByteArray.size_data, hb]
  have hlt : bytesToNat b.data.toList < 2 ^ 256 := by
    have h := bytesToNat_lt b.data.toList
    rw [hlen] at h
    rwa [show (256 : Nat) ^ 32 = 2 ^ 256 by decide] at h
  have hv : (loadWord b 0 32).toNat = bytesToNat b.data.toList := by
    rw [loadWord, h32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have bytes : (wordBytes (loadWord b 0 32)).data.toList =
      natToBytes 32 (loadWord b 0 32).toNat := EthLib.Base.U256.toList_toBeBytes _
  have hback := natToBytes_bytesToNat b.data.toList
  rw [hlen] at hback
  apply ByteArray.ext
  apply Array.ext'
  rw [bytes, hv, hback]

/-- A write of a word at `o` leaves the known word at `a`, when the two do not overlap. -/
theorem load_rawW {m : ByteArray} {sz n o a : Nat} {v w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (ha : a + 32 ≤ sz) (hd : a + 32 ≤ o ∨ o + 32 ≤ a) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (wordBytes v)) a 32) 0 32 = w := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit)
      (by rw [size_wordBytes]; exact hd),
    memoryReadBytes_memoryExtend (by omega)]
  exact h

/-- The word at `o` after a write of a word at `o`. -/
theorem load_rawW_self {m : ByteArray} {sz n o : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (wordBytes v)) o 32) 0 32 = v :=
  loadWord_memoryWrite_wordBytes v (by rw [size_memoryExtend, hs]; exact hfit)

/-- The 32 bytes at `a` of a memory with a known word there. -/
theorem readWord_raw {m : ByteArray} {sz a : Nat} {w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz) (ha : a + 32 ≤ sz) :
    memoryReadBytes m a 32 = wordBytes w := by
  rw [← h, wordBytes_loadWord (size_memoryReadBytes (by omega))]

/-- A read of `j + k` bytes is the read of the first `j` and then of the next `k`. -/
theorem memoryReadBytes_add {m : ByteArray} {s j k : Nat} (hfit : s + (j + k) ≤ m.size)
    (hj : 0 < j) (hk : 0 < k) :
    memoryReadBytes m s (j + k) = memoryReadBytes m s j ++ memoryReadBytes m (s + j) k := by
  have f1 : s + j ≤ m.size := by omega
  have f2 : s + j + k ≤ m.size := by omega
  apply eq_of_byteAt
  · rw [ByteArray.size_append, size_memoryReadBytes hfit, size_memoryReadBytes f1,
      size_memoryReadBytes f2]
  · intro i
    rw [byteAt_append, size_memoryReadBytes f1, byteAt_memoryReadBytes hfit,
      byteAt_memoryReadBytes f1, byteAt_memoryReadBytes f2]
    by_cases h : i < j
    · rw [if_pos h, if_pos (by omega), if_pos h]
    · rw [if_neg h]
      by_cases h' : i < j + k
      · rw [if_pos h', if_pos (by omega), show s + j + (i - j) = s + i by omega]
      · rw [if_neg h', if_neg (by omega)]

/-- The 64 bytes at 0 of a memory with known words at 0 and at 32. -/
theorem read0_raw {m : ByteArray} {sz : Nat} {a b : U256}
    (h0 : loadWord (memoryReadBytes m 0 32) 0 32 = a)
    (h1 : loadWord (memoryReadBytes m 32 32) 0 32 = b) (hs : m.size = sz) (hfit : 64 ≤ sz) :
    memoryReadBytes m 0 64 = wordBytes a ++ wordBytes b := by
  rw [← readWord_raw h0 hs (by omega), ← readWord_raw h1 hs (by omega)]
  exact memoryReadBytes_add (s := 0) (j := 32) (k := 32) (by omega) (by omega) (by omega)

/-- A read of bytes that a write of a word does not touch. -/
theorem read_rawW {m : ByteArray} {sz n o a k : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (ha : a + k ≤ sz) (hd : a + k ≤ o ∨ o + 32 ≤ a) :
    memoryReadBytes (memoryWrite (memoryExtend m n) o (wordBytes v)) a k =
      memoryReadBytes m a k := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit)
      (by rw [size_wordBytes]; exact hd),
    memoryReadBytes_memoryExtend (by omega)]

/-- The 128 bytes at `a` of a memory with four known words there (the input of ECRECOVER). -/
theorem read4_raw {m : ByteArray} {sz a : Nat} {w0 w1 w2 w3 : U256}
    (h0 : loadWord (memoryReadBytes m a 32) 0 32 = w0)
    (h1 : loadWord (memoryReadBytes m (a + 32) 32) 0 32 = w1)
    (h2 : loadWord (memoryReadBytes m (a + 64) 32) 0 32 = w2)
    (h3 : loadWord (memoryReadBytes m (a + 96) 32) 0 32 = w3)
    (hs : m.size = sz) (hfit : a + 128 ≤ sz) :
    memoryReadBytes m a 128 =
      wordBytes w0 ++ wordBytes w1 ++ wordBytes w2 ++ wordBytes w3 := by
  have e3 := memoryReadBytes_add (m := m) (s := a) (j := 96) (k := 32) (by omega) (by omega)
    (by omega)
  have e2 := memoryReadBytes_add (m := m) (s := a) (j := 64) (k := 32) (by omega) (by omega)
    (by omega)
  have e1 := memoryReadBytes_add (m := m) (s := a) (j := 32) (k := 32) (by omega) (by omega)
    (by omega)
  rw [← readWord_raw h0 hs (by omega), ← readWord_raw h1 hs (by omega),
    ← readWord_raw h2 hs (by omega), ← readWord_raw h3 hs (by omega)]
  exact e3.trans (congrArg (· ++ memoryReadBytes m (a + 96) 32)
    (e2.trans (congrArg (· ++ memoryReadBytes m (a + 64) 32) e1)))

/-- KECCAK256 of bytes inside the memory: the bytes are a side goal. -/
theorem keccakK {start size : U256} {rest : List U256} {sz o k c : Nat} {d : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) (hsz : memory.size = sz)
    (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hcost : keccak256Cost (BitVec.ofNat 256 k) = c) (hdata : memoryReadBytes memory o k = d) (hgas : c ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (At code message (pc + 1) (keccak d :: rest) memory (gas - c) state substate) := by
  have hsize : BitVec.ofNat 256 k = size := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← hk]
    exact Nat.mod_eq_of_lt size.isLt
  rw [hsize] at hcost
  subst hsz ho hk hcost hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.keccak256G (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (start := start) (size := size) (memory := memory)
    (gas := gas) hlt hbyte (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (Gas.reshapeG ?_ ?_ ?_)
  · show _ :: rest = _ :: rest
    rw [memoryExtend_zero]
  · exact memoryExtend_zero memory
  · rfl

/-- TIMESTAMP runs the read of the time stamp of the block. -/
theorem instruction_timestamp : instruction (Meter := Nat) fork .timestamp =
    some (readFrame OPCODE_TIMESTAMP fun evm => evm.message.blockEnv.timestamp) := by
  first
    | rfl
    | simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
        environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse]

/-- TIMESTAMP pushes the time stamp of the block of the message, for 2 gas. -/
theorem timestampL {stack : List U256} (hlt : pc < code.size) (hbyte : code[pc] = 0x42)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (message.blockEnv.timestamp :: stack) memory (gas - 2) state
        substate) :=
  liftAt fun _ => Logic.push_of_readFrameG hlt hbyte
    (ofByte_of_decode (op := .timestamp) rfl (Fork.frontier_le _)) instruction_timestamp
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

end TokenKit

import WbtcVerify.Wbtc.CallOut

/-!
# The bubble after a failed call, exactly, and the head words of a message read from memory

Nothing here is about one token.

What is proved:

- `loadWord_read_sub`: a word of a range read from memory is the word of the memory at that
  place. `selector_read`: the selector of such a range, from its first four bytes.
  `byteAt_rawW_other`, `byteAt_rawW_self`: the bytes of a memory after a word was written.
- `bubble_out`: RETURNDATACOPY of the whole return data to memory 0, then a read of the same
  range, gives the return data back, and the second growth of memory costs nothing.
- `bubble_spec`: the code that solc puts after a call whose failure it passes on
  (`ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY RETURNDATASIZE
  PUSH1 0 REVERT`), from a frame with the flag 0 on top (the call failed) and enough gas: the
  frame REVERTS, its output is EXACTLY the return data of the failed call, state and substate
  are those of the frame, and the gas is exact:
  `38 + 3 * words(return data) + growth of memory to hold the return data`.

Assumed: the fork is from Byzantium; one counter of gas; the size of the memory is a multiple of
32; the return data are below 2^256 bytes.

Not covered: the same code with too little gas (it then ends with an error: the kit's
`bubble_no_ok` covers every gas in the form "no run ends with no error").
-/

namespace TokenKit

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## Words and selector of a range read from memory -/

/-- The word at `off` of the `k` bytes read from memory at `a` is the word of the memory at
`a + off`. -/
theorem loadWord_read_sub {m : ByteArray} {a k off : Nat} (hfit : a + k ≤ m.size)
    (hoff : off + 32 ≤ k) :
    loadWord (memoryReadBytes m a k) off 32 = loadWord (memoryReadBytes m (a + off) 32) 0 32 := by
  unfold loadWord bufferRead
  refine congrArg _ (congrArg _ ?_)
  apply List.map_congr_left
  intro i hi
  have hi' : i < 32 := List.mem_range.mp hi
  have e1 := byteAt_memoryReadBytes hfit (off + i)
  rw [if_pos (show off + i < k from by omega)] at e1
  have e2 := byteAt_memoryReadBytes (memory := m) (start := a + off) (size := 32) (by omega)
    (0 + i)
  rw [if_pos (show 0 + i < 32 from by omega)] at e2
  rw [e1, e2]
  congr 1
  omega

/-- The selector of a range of at least 4 bytes read from memory, from its first four bytes. -/
theorem selector_read {m : ByteArray} {a k : Nat} {b0 b1 b2 b3 : UInt8} (hfit : a + k ≤ m.size)
    (hk : 4 ≤ k) (h0 : byteAt m (a + 0) = b0) (h1 : byteAt m (a + 1) = b1)
    (h2 : byteAt m (a + 2) = b2) (h3 : byteAt m (a + 3) = b3) :
    selector (memoryReadBytes m a k) = bytesToNat [b0, b1, b2, b3] := by
  have e : ∀ j, j < 4 → byteAt (memoryReadBytes m a k) j = byteAt m (a + j) := by
    intro j hj
    rw [byteAt_memoryReadBytes hfit, if_pos (show j < k from by omega)]
  unfold selector
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), h0, h1, h2, h3]

/-- A byte outside a word written to a grown memory is the byte of the memory before. -/
theorem byteAt_rawW_other {m : ByteArray} {sz n o : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) {j : Nat} (hj : j < o ∨ o + 32 ≤ j) :
    byteAt (memoryWrite (memoryExtend m n) o (wordBytes v)) j = byteAt m j := by
  rw [byteAt_memoryWrite (by rw [size_wordBytes, size_memoryExtend]; omega)]
  split
  · rename_i h
    rw [size_wordBytes] at h
    exact absurd h (by omega)
  · exact byteAt_memoryExtend _ _ _

/-- A byte of a word written to a grown memory. -/
theorem byteAt_rawW_self {m : ByteArray} {sz n o : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) {i : Nat} (hi : i < 32) :
    byteAt (memoryWrite (memoryExtend m n) o (wordBytes v)) (o + i) = byteAt (wordBytes v) i := by
  rw [byteAt_memoryWrite (by rw [size_wordBytes, size_memoryExtend]; omega)]
  split
  · congr 1
    omega
  · rename_i h
    rw [size_wordBytes] at h
    exact absurd h (by omega)

/-! ## The bubble -/

/-- The whole return data copied to memory 0 and read back are the return data, and the second
growth of memory costs nothing. -/
theorem bubble_out {rd : ByteArray} {Z N : U256} (hZ : Z.toNat = 0) (hN : N.toNat = rd.size)
    (hmod : memory.size % 32 = 0) :
    memoryReadBytes
        (memoryExtend
          (memoryWrite (memoryExtend memory (extendMemory memory.size [(Z, N)]).expandBy) Z.toNat
            (memoryReadBytes rd Z.toNat N.toNat))
          (extendMemory
            (memoryWrite (memoryExtend memory (extendMemory memory.size [(Z, N)]).expandBy)
              Z.toNat (memoryReadBytes rd Z.toNat N.toNat)).size [(Z, N)]).expandBy)
        Z.toNat N.toNat = rd ∧
      (extendMemory
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(Z, N)]).expandBy) Z.toNat
          (memoryReadBytes rd Z.toNat N.toNat)).size [(Z, N)]).cost = 0 := by
  rw [hZ, hN, memoryReadBytes_whole]
  by_cases hn : rd.size = 0
  · have hrd : rd = ByteArray.empty := ByteArray.size_eq_zero_iff.mp hn
    have hNz : N = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hN, hn]
      rfl
    subst hNz
    simp only [extendMemory_of_length_eq_zero]
    refine ⟨?_, trivial⟩
    rw [hn]
    simp [memoryReadBytes, hrd]
  · have hNz : N ≠ 0 := by
      intro h
      apply hn
      rw [← hN, h]
      rfl
    have hs1 := size_memoryExtend_extendMemory (memory := memory) (start := Z) hmod hNz
    rw [hZ, hN, Nat.zero_add] at hs1
    generalize memoryExtend memory (extendMemory memory.size [(Z, N)]).expandBy = M1 at hs1 ⊢
    have hle : rd.size ≤ M1.size := by
      rw [hs1]
      exact Nat.le_trans (le_ceil32 _) (Nat.le_max_right _ _)
    have hs2 : (memoryWrite M1 0 rd).size = M1.size := size_memoryWrite (by omega)
    have he2 : extendMemory (memoryWrite M1 0 rd).size [(Z, N)] = ⟨0, 0⟩ :=
      extendMemory_of_le (by rw [hZ, hN, hs2]; omega)
    rw [he2]
    refine ⟨?_, rfl⟩
    show memoryReadBytes (memoryExtend (memoryWrite M1 0 rd) 0) 0 rd.size = rd
    rw [memoryExtend_zero]
    exact memoryReadBytes_memoryWrite (by omega)

/-- The bubble with the words 0 and the size of the return data named, so that the rules can be
chained. See `bubble_spec`. -/
theorem bubble_specZN (hfork : .byzantium ≤ fork) {rest : List U256} {rd : ByteArray}
    {Z N : U256} (hZ : BitVec.ofNat 256 (0x00 : UInt8).toNat = Z)
    (hN : BitVec.ofNat 256 rd.size = N) (hNn : N.toNat = rd.size)
    (hlt : pc + 15 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (b6 : code[pc + 6]'(by omega) = 0x57) (b7 : code[pc + 7]'(by omega) = 0x3d)
    (b8 : code[pc + 8]'(by omega) = 0x60) (b9 : code[pc + 9]'(by omega) = 0x00)
    (b10 : code[pc + 10]'(by omega) = 0x80) (b11 : code[pc + 11]'(by omega) = 0x3e)
    (b12 : code[pc + 12]'(by omega) = 0x3d) (b13 : code[pc + 13]'(by omega) = 0x60)
    (b14 : code[pc + 14]'(by omega) = 0x00) (b15 : code[pc + 15]'(by omega) = 0xfd)
    (hrest : rest.length + 4 < STACK_LIMIT) (hmod : memory.size % 32 = 0)
    (hgas : 38 + 3 * wordCount N.toNat + (extendMemory memory.size [(Z, N)]).cost ≤ gas) :
    Logic.SpecG fork (Logic.At code message pc (0 :: rest) memory gas state substate rd)
      (Halted true rd
        (gas - (38 + 3 * wordCount N.toNat + (extendMemory memory.size [(Z, N)]).cost))
        state substate) := by
  have hZ0 : Z.toNat = 0 := by rw [← hZ]; rfl
  obtain ⟨hout, hc2⟩ := bubble_out (memory := memory) (rd := rd) hZ0 hNn hmod
  have hz1 : isZero (0 : U256) = 1 := by decide
  have hz2 : isZero (1 : U256) = 0 := by decide
  have hlim : STACK_LIMIT = 1024 := rfl
  rw [hlim] at hrest
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b0
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz1]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (by omega) b1 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b2
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz2]
  -- PUSH2
  refine Logic.SpecG.seq (Logic.pushG (n := 2) (by decide) (by omega)
    (by rw [b3]; decide) (by decide) rfl (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- JUMPI, not taken
  refine Logic.SpecG.seq (Logic.jumpi_zeroG (pc := pc + 6) (by omega) b6 (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 7) hfork (by omega) b7 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH1 0
  refine Logic.SpecG.seq (Logic.push1G (pc := pc + 8) (by omega) b8 b9 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hZ]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (pc := pc + 10) (by omega) b10 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- RETURNDATACOPY
  refine Logic.SpecG.seq (returndatacopyG (pc := pc + 11) hfork (by omega) b11
    (by rw [hZ0]; omega) (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 12) hfork (by omega) b12 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH1 0
  refine Logic.SpecG.seq (Logic.push1G (pc := pc + 13) (by omega) b13 b14 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hZ]
  -- REVERT
  refine Logic.SpecG.consequence (Logic.revertG (pc := pc + 15) hfork (by omega) b15
    (by rw [hc2]; exact Nat.zero_le _)) (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hg, hs, hss⟩
  refine ⟨hr, he, ho.trans hout, hg.trans ?_, hs, hss⟩
  rw [hc2]
  omega

/-- THE BUBBLE, exactly. From the frame after a call that failed (flag 0 on top, the return data
`rd` of the failed call), with enough gas, the code
`ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY RETURNDATASIZE
PUSH1 0 REVERT` reverts the frame with output `rd`: the caller of the frame gets the return data
of the failed call, byte for byte. State and substate are those of the frame (the caller of the
frame then drops them, as for any revert). -/
theorem bubble_spec (hfork : .byzantium ≤ fork) {rest : List U256} {rd : ByteArray}
    (hsize : rd.size < 2 ^ 256) (hlt : pc + 15 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (b6 : code[pc + 6]'(by omega) = 0x57) (b7 : code[pc + 7]'(by omega) = 0x3d)
    (b8 : code[pc + 8]'(by omega) = 0x60) (b9 : code[pc + 9]'(by omega) = 0x00)
    (b10 : code[pc + 10]'(by omega) = 0x80) (b11 : code[pc + 11]'(by omega) = 0x3e)
    (b12 : code[pc + 12]'(by omega) = 0x3d) (b13 : code[pc + 13]'(by omega) = 0x60)
    (b14 : code[pc + 14]'(by omega) = 0x00) (b15 : code[pc + 15]'(by omega) = 0xfd)
    (hrest : rest.length + 4 < STACK_LIMIT) (hmod : memory.size % 32 = 0)
    (hgas : 38 + 3 * wordCount rd.size +
      (extendMemory memory.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost ≤ gas) :
    Logic.SpecG fork (Logic.At code message pc (0 :: rest) memory gas state substate rd)
      (Halted true rd
        (gas - (38 + 3 * wordCount rd.size +
          (extendMemory memory.size [((0 : U256), BitVec.ofNat 256 rd.size)]).cost))
        state substate) := by
  have hNn : (BitVec.ofNat 256 rd.size : U256).toNat = rd.size := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsize
  have h := bubble_specZN (fork := fork) (message := message) (memory := memory) (gas := gas)
    (state := state) (substate := substate) hfork (rest := rest) (rd := rd) rfl rfl hNn hlt
    b0 b1 b2 b3 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 hrest hmod (by rw [hNn]; exact hgas)
  rw [hNn] at h
  exact h

end TokenKit

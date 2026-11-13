import UsdtVerify.Evm.GasRules
import EthLib.Execution.Proofs.Evm.Machine.Memory
import EthLib.Execution.Proofs.Evm.Instructions.MemoryData

/-!
# Memory as a list of words

Solidity code keeps its memory word aligned on the paths that do not build a revert string: two
scratch words at 0 and 32 (the input of the mapping hash), the free memory pointer at 64, a zero
word at 96, and the words it returns or logs from 128.

- `memW l`: the memory that holds the words of `l`, 32 bytes each.
- `size_memW3`, `size_memW5`: its size for 3 and 5 words.
- `memW_write0`, `memW_write32`, `memW_write64`, `memW_write128`, `memW_ext128`: a write of a
  word at an aligned offset gives `memW` of the list with that word replaced (or appended, with a
  zero word before it, for the write at 128 into a memory of 96 bytes).
- `memW_load64`, `memW_read0`, `memW_read128`: the reads that the code makes.
- `size_rawW`, `load64_rawW`: for a write at an offset that is not aligned (a revert string): its
  size, and the word at 64 that it leaves alone.

Nothing here is about one token: the lemmas are about `memoryWrite`, `memoryExtend` and
`memoryReadBytes` only.
-/

namespace TokenKit

open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm

/-- The memory that holds the words of a list, 32 bytes each. -/
def memW : List U256 → ByteArray
  | [] => .empty
  | w :: ws => wordBytes w ++ memW ws

theorem memW_cons (w : U256) (ws : List U256) : memW (w :: ws) = wordBytes w ++ memW ws := rfl

theorem size_memW_cons (w : U256) (ws : List U256) :
    (memW (w :: ws)).size = 32 + (memW ws).size := by
  rw [memW_cons, ByteArray.size_append, size_wordBytes]

theorem size_memW_nil : (memW []).size = 0 := rfl

theorem size_memW3 (a b c : U256) : (memW [a, b, c]).size = 96 := by
  simp only [size_memW_cons, size_memW_nil]

theorem size_memW5 (a b c d e : U256) : (memW [a, b, c, d, e]).size = 160 := by
  simp only [size_memW_cons, size_memW_nil]

theorem byteAt_memW_cons (w : U256) (ws : List U256) (i : Nat) :
    byteAt (memW (w :: ws)) i =
      if i < 32 then byteAt (wordBytes w) i else byteAt (memW ws) (i - 32) := by
  rw [memW_cons, byteAt_append, size_wordBytes]

theorem byteAt_memW_nil (i : Nat) : byteAt (memW []) i = 0 :=
  byteAt_of_size_le (by rw [size_memW_nil]; omega)

/-- Every byte of the zero word is zero. -/
theorem byteAt_wordBytes_zero (i : Nat) : byteAt (wordBytes 0) i = 0 := by
  by_cases h : i < 32
  · have key : ∀ j, j < 32 → byteAt (wordBytes 0) j = 0 := by decide
    exact key i h
  · exact byteAt_of_size_le (by rw [size_wordBytes]; omega)

/-- Close a goal about one byte of two memories: split every `if`, then arithmetic. -/
macro "mem_bytes" : tactic => `(tactic| (
  simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero, byteAt_memoryExtend,
    byteAt_append, size_wordBytes]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega)))

theorem memW_write0 (a v : U256) (l : List U256) :
    memoryWrite (memoryExtend (memW (a :: l)) 0) 0 (wordBytes v) = memW (v :: l) := by
  rw [memoryExtend_zero]
  have hv := size_wordBytes v
  have hs := size_memW_cons a l
  have hfit : 0 + (wordBytes v).size ≤ (memW (a :: l)).size := by omega
  apply eq_of_byteAt
  · rw [size_memoryWrite hfit, hs, size_memW_cons]
  · intro i
    rw [byteAt_memoryWrite hfit, hv]
    mem_bytes

theorem memW_write32 (a b v : U256) (l : List U256) :
    memoryWrite (memoryExtend (memW (a :: b :: l)) 0) 32 (wordBytes v) = memW (a :: v :: l) := by
  rw [memoryExtend_zero]
  have hv := size_wordBytes v
  have hs : (memW (a :: b :: l)).size = 64 + (memW l).size := by
    simp only [size_memW_cons]; omega
  have hfit : 32 + (wordBytes v).size ≤ (memW (a :: b :: l)).size := by omega
  apply eq_of_byteAt
  · rw [size_memoryWrite hfit]; simp only [size_memW_cons]
  · intro i
    rw [byteAt_memoryWrite hfit, hv]
    mem_bytes

theorem memW_write64 (a b c v : U256) (l : List U256) :
    memoryWrite (memW (a :: b :: c :: l)) 64 (wordBytes v) = memW (a :: b :: v :: l) := by
  have hv := size_wordBytes v
  have hs : (memW (a :: b :: c :: l)).size = 96 + (memW l).size := by
    simp only [size_memW_cons]; omega
  have hfit : 64 + (wordBytes v).size ≤ (memW (a :: b :: c :: l)).size := by omega
  apply eq_of_byteAt
  · rw [size_memoryWrite hfit]; simp only [size_memW_cons]
  · intro i
    rw [byteAt_memoryWrite hfit, hv]
    mem_bytes

/-- A write past the first word is a write into the words after it. -/
theorem memW_peel (w : U256) (ws : List U256) (o : Nat) (x : ByteArray)
    (h : o + x.size ≤ (memW ws).size) :
    memoryWrite (memW (w :: ws)) (32 + o) x = memW (w :: []) ++ memoryWrite (memW ws) o x := by
  have hs := size_memW_cons w ws
  have hfit : 32 + o + x.size ≤ (memW (w :: ws)).size := by omega
  have h1 : (memW (w :: [])).size = 32 := by rw [size_memW_cons, size_memW_nil]
  apply eq_of_byteAt
  · rw [size_memoryWrite hfit, ByteArray.size_append, size_memoryWrite h, h1, hs]
  · intro i
    rw [byteAt_memoryWrite hfit, byteAt_append, h1, byteAt_memoryWrite h]
    simp only [byteAt_memW_cons, byteAt_memW_nil]
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega)

theorem memW_one_append (w : U256) (ws : List U256) : memW (w :: []) ++ memW ws = memW (w :: ws) := by
  apply eq_of_byteAt
  · rw [ByteArray.size_append]; simp only [size_memW_cons, size_memW_nil]
  · intro i
    rw [byteAt_append]
    simp only [byteAt_memW_cons, byteAt_memW_nil, size_memW_cons, size_memW_nil]
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega)

theorem memW_set0 (a v : U256) (l : List U256) :
    memoryWrite (memW (a :: l)) 0 (wordBytes v) = memW (v :: l) := by
  have h := memW_write0 a v l
  rwa [memoryExtend_zero] at h

theorem memW_write128 (a b c d e v : U256) :
    memoryWrite (memoryExtend (memW [a, b, c, d, e]) 0) 128 (wordBytes v) =
      memW [a, b, c, d, v] := by
  rw [memoryExtend_zero]
  show memoryWrite (memW [a, b, c, d, e]) (32 + (32 + (32 + (32 + 0)))) (wordBytes v) = _
  rw [memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_set0, memW_one_append, memW_one_append, memW_one_append, memW_one_append]

/-- Two zero words after a memory of words change no byte. -/
theorem byteAt_memW_grow2 (l : List U256) (i : Nat) :
    byteAt (memW (l ++ [0, 0])) i = byteAt (memW l) i := by
  induction l generalizing i with
  | nil =>
    rw [byteAt_memW_nil, List.nil_append]
    simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero]
    repeat' split
    all_goals rfl
  | cons w ws ih => rw [List.cons_append, byteAt_memW_cons, byteAt_memW_cons, ih]

/-- A memory of words, grown by two words. -/
theorem memW_grow2 (a b c : U256) :
    memoryExtend (memW [a, b, c]) 64 = memW [a, b, c, 0, 0] := by
  apply eq_of_byteAt
  · rw [size_memoryExtend, size_memW3, size_memW5]
  · intro i
    rw [byteAt_memoryExtend]
    exact (byteAt_memW_grow2 [a, b, c] i).symm

/-- The write at 128 into a memory of 96 bytes: the memory grows by two words. -/
theorem memW_ext128 (a b c v : U256) :
    memoryWrite (memoryExtend (memW [a, b, c]) 64) 128 (wordBytes v) = memW [a, b, c, 0, v] := by
  rw [memW_grow2]
  have h := memW_write128 a b c 0 0 v
  rwa [memoryExtend_zero] at h

/-- The free memory pointer: the word at 64. -/
theorem memW_load64 (a b c : U256) (l : List U256) :
    loadWord (memoryReadBytes (memW (a :: b :: c :: l)) 64 32) 0 32 = c := by
  have hs : (memW (a :: b :: c :: l)).size = 96 + (memW l).size := by
    simp only [size_memW_cons]; omega
  have h := loadWord_memoryWrite_wordBytes (memory := memW (a :: b :: c :: l)) (start := 64) c
    (by omega)
  rwa [memW_write64] at h

/-- The input of the mapping hash: the two words at 0 and 32. -/
theorem memW_read0 (a b : U256) (l : List U256) :
    memoryReadBytes (memW (a :: b :: l)) 0 64 = wordBytes a ++ wordBytes b := by
  have hs : (memW (a :: b :: l)).size = 64 + (memW l).size := by
    simp only [size_memW_cons]; omega
  have hfit : 0 + 64 ≤ (memW (a :: b :: l)).size := by omega
  apply eq_of_byteAt
  · rw [size_memoryReadBytes hfit, ByteArray.size_append, size_wordBytes, size_wordBytes]
  · intro i
    rw [byteAt_memoryReadBytes hfit]
    have ha : ∀ j, 32 ≤ j → byteAt (wordBytes a) j = 0 := fun j hj =>
      byteAt_of_size_le (by rw [size_wordBytes]; exact hj)
    have hb : ∀ j, 32 ≤ j → byteAt (wordBytes b) j = 0 := fun j hj =>
      byteAt_of_size_le (by rw [size_wordBytes]; exact hj)
    simp only [byteAt_memW_cons, byteAt_append, size_wordBytes]
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega) | (rw [hb _ (by omega)])

/-- The word that the code returns or logs: the word at 128. -/
theorem memW_read128 (a b c d e : U256) :
    memoryReadBytes (memW [a, b, c, d, e]) 128 32 = wordBytes e := by
  have h := memoryReadBytes_memoryWrite (memory := memW [a, b, c, d, e]) (start := 128)
    (value := wordBytes e) (by rw [size_wordBytes, size_memW5]; decide)
  have hw := memW_write128 a b c d e e
  rw [memoryExtend_zero] at hw
  rw [hw, size_wordBytes] at h
  exact h

/-- The memory after the prelude: two zero words and the free memory pointer 0x80. -/
theorem memW_init :
    memoryWrite (memoryExtend .empty 96) 64 (wordBytes 0x80) = memW [0, 0, 0x80] := by
  have h0 : memoryExtend ByteArray.empty 96 = memW [0, 0, 0] := by
    have hz : ∀ j, byteAt ByteArray.empty j = 0 := fun j => byteAt_of_size_le (Nat.zero_le _)
    apply eq_of_byteAt
    · rw [size_memoryExtend, size_memW3]; rfl
    · intro i
      rw [byteAt_memoryExtend, hz]
      simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero]
      repeat' split
      all_goals rfl
  rw [h0, memW_write64]

/-! ## A free memory pointer at 0x60 (Solidity before 0.4.22): the word returned is at 96 -/

theorem size_memW4 (a b c d : U256) : (memW [a, b, c, d]).size = 128 := by
  simp only [size_memW_cons, size_memW_nil]

theorem memW_write96 (a b c d v : U256) :
    memoryWrite (memoryExtend (memW [a, b, c, d]) 0) 96 (wordBytes v) = memW [a, b, c, v] := by
  rw [memoryExtend_zero]
  show memoryWrite (memW [a, b, c, d]) (32 + (32 + (32 + 0))) (wordBytes v) = _
  rw [memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_peel _ _ _ _ (by simp only [size_memW_cons, size_memW_nil, size_wordBytes]; omega),
    memW_set0, memW_one_append, memW_one_append, memW_one_append]

/-- One zero word after a memory of words changes no byte. -/
theorem byteAt_memW_grow1 (l : List U256) (i : Nat) :
    byteAt (memW (l ++ [0])) i = byteAt (memW l) i := by
  induction l generalizing i with
  | nil =>
    rw [byteAt_memW_nil, List.nil_append]
    simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero]
    repeat' split
    all_goals rfl
  | cons w ws ih => rw [List.cons_append, byteAt_memW_cons, byteAt_memW_cons, ih]

/-- A memory of words, grown by one word. -/
theorem memW_grow1 (a b c : U256) :
    memoryExtend (memW [a, b, c]) 32 = memW [a, b, c, 0] := by
  apply eq_of_byteAt
  · rw [size_memoryExtend, size_memW3, size_memW4]
  · intro i
    rw [byteAt_memoryExtend]
    exact (byteAt_memW_grow1 [a, b, c] i).symm

/-- The write at 96 into a memory of 96 bytes: the memory grows by one word. -/
theorem memW_ext96 (a b c v : U256) :
    memoryWrite (memoryExtend (memW [a, b, c]) 32) 96 (wordBytes v) = memW [a, b, c, v] := by
  rw [memW_grow1]
  have h := memW_write96 a b c 0 v
  rwa [memoryExtend_zero] at h

/-- The word that the code returns or logs: the word at 96. -/
theorem memW_read96 (a b c d : U256) :
    memoryReadBytes (memW [a, b, c, d]) 96 32 = wordBytes d := by
  have h := memoryReadBytes_memoryWrite (memory := memW [a, b, c, d]) (start := 96)
    (value := wordBytes d) (by rw [size_wordBytes, size_memW4]; decide)
  have hw := memW_write96 a b c d d
  rw [memoryExtend_zero] at hw
  rw [hw, size_wordBytes] at h
  exact h

/-- The memory after a prelude that writes the free memory pointer `w` at 64. -/
theorem memW_initW (w : U256) :
    memoryWrite (memoryExtend .empty 96) 64 (wordBytes w) = memW [0, 0, w] := by
  have h0 : memoryExtend ByteArray.empty 96 = memW [0, 0, 0] := by
    have hz : ∀ j, byteAt ByteArray.empty j = 0 := fun j => byteAt_of_size_le (Nat.zero_le _)
    apply eq_of_byteAt
    · rw [size_memoryExtend, size_memW3]; rfl
    · intro i
      rw [byteAt_memoryExtend, hz]
      simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero]
      repeat' split
      all_goals rfl
  rw [h0, memW_write64]

/-! ## Writes that are not aligned -/

/-- The size after a write of a word, the memory grown by `n` bytes first. -/
theorem size_rawW {m : ByteArray} {sz n o : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) :
    (memoryWrite (memoryExtend m n) o (wordBytes v)).size = sz + n := by
  rw [size_memoryWrite (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit),
    size_memoryExtend, hs]

/-- A read within a memory is the same read after the memory grows. -/
theorem memoryReadBytes_memoryExtend {m : ByteArray} {s k n : Nat} (hfit : s + k ≤ m.size) :
    memoryReadBytes (memoryExtend m n) s k = memoryReadBytes m s k := by
  have hfit' : s + k ≤ (memoryExtend m n).size := by rw [size_memoryExtend]; omega
  apply eq_of_byteAt
  · rw [size_memoryReadBytes hfit, size_memoryReadBytes hfit']
  · intro i
    rw [byteAt_memoryReadBytes hfit, byteAt_memoryReadBytes hfit', byteAt_memoryExtend]

/-- A write of a word from 96 on leaves the word at 64. -/
theorem load64_rawW {m : ByteArray} {sz n o : Nat} {v w : U256}
    (h : loadWord (memoryReadBytes m 64 32) 0 32 = w) (hs : m.size = sz) (h96 : 96 ≤ sz)
    (hfit : o + 32 ≤ sz + n) (hd : 96 ≤ o) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m n) o (wordBytes v)) 64 32) 0 32 = w := by
  rw [memoryReadBytes_memoryWrite_of_disjoint
      (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit) (.inl (by omega)),
    memoryReadBytes_memoryExtend (by omega)]
  exact h

/-! ## Any aligned word

The lemmas above fix the shape of the memory (3 or 5 words, the free memory pointer 0x80). The
ones below are for any list of words and any aligned offset; a token compiled with the free
memory pointer at 0x60 (solc 0.4) uses them. Every side goal is closed by `rfl`. -/

/-- The word number `i` of a list, 0 past its end. -/
def wordAt : List U256 → Nat → U256
  | [], _ => 0
  | w :: _, 0 => w
  | _ :: ws, i + 1 => wordAt ws i

/-- The list with the word number `i` set to `v`, grown with zero words when `i` is past its
end. -/
def setW : List U256 → Nat → U256 → List U256
  | [], 0, v => [v]
  | [], i + 1, v => 0 :: setW [] i v
  | _ :: ws, 0, v => v :: ws
  | w :: ws, i + 1, v => w :: setW ws i v

theorem wordAt_nil (i : Nat) : wordAt [] i = 0 := by cases i <;> rfl

theorem wordAt_of_le : ∀ (ws : List U256) (i : Nat), ws.length ≤ i → wordAt ws i = 0
  | [], i, _ => wordAt_nil i
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: ws, i + 1, h => wordAt_of_le ws i (by simpa using h)

theorem wordAt_setW : ∀ (ws : List U256) (i : Nat) (v : U256) (j : Nat),
    wordAt (setW ws i v) j = if j = i then v else wordAt ws j
  | [], 0, v, 0 => rfl
  | [], 0, v, j + 1 => by
    show wordAt [] j = _
    rw [if_neg (by omega), wordAt_nil, wordAt_nil]
  | [], i + 1, v, 0 => by
    show (0 : U256) = _
    rw [if_neg (by omega), wordAt_nil]
  | [], i + 1, v, j + 1 => by
    show wordAt (setW [] i v) j = _
    rw [wordAt_setW [] i v j, wordAt_nil, wordAt_nil]
    by_cases h : j = i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  | w :: ws, 0, v, 0 => rfl
  | w :: ws, 0, v, j + 1 => by
    show wordAt ws j = _
    rw [if_neg (by omega)]
    rfl
  | w :: ws, i + 1, v, 0 => by
    show w = _
    rw [if_neg (by omega)]
    rfl
  | w :: ws, i + 1, v, j + 1 => by
    show wordAt (setW ws i v) j = _
    rw [wordAt_setW ws i v j]
    by_cases h : j = i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
      rfl

theorem size_memW (ws : List U256) : (memW ws).size = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [size_memW_cons, ih, List.length_cons]; omega

/-- The size of a memory of words, as a numeral. -/
theorem size_memWn {n : Nat} (ws : List U256) (h : 32 * ws.length = n) : (memW ws).size = n := by
  rw [size_memW, h]

/-- A byte of a memory of words is a byte of one of its words. -/
theorem byteAt_memW (ws : List U256) (k : Nat) :
    byteAt (memW ws) k = byteAt (wordBytes (wordAt ws (k / 32))) (k % 32) := by
  induction ws generalizing k with
  | nil => rw [byteAt_memW_nil, wordAt_nil, byteAt_wordBytes_zero]
  | cons w ws ih =>
    rw [byteAt_memW_cons]
    by_cases h : k < 32
    · rw [if_pos h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rw [if_neg h, ih]
      have h1 : k / 32 = (k - 32) / 32 + 1 := by omega
      have h2 : (k - 32) % 32 = k % 32 := by omega
      rw [h1, h2]
      rfl

/-- A write of a word at the aligned offset `32 * i`, the memory grown by `n` bytes first, gives
the memory of the list with the word number `i` set. -/
theorem memW_set {ws ws' : List U256} {o n : Nat} {v : U256} (i : Nat) (ho : o = 32 * i)
    (hs : setW ws i v = ws') (hn : 32 * ws.length + n = 32 * ws'.length)
    (hi : decide (i < ws'.length) = true) :
    memoryWrite (memoryExtend (memW ws) n) o (wordBytes v) = memW ws' := by
  subst ho hs
  have hi' := of_decide_eq_true hi
  have hv := size_wordBytes v
  have hsz : (memoryExtend (memW ws) n).size = 32 * (setW ws i v).length := by
    rw [size_memoryExtend, size_memW, hn]
  have hfit : 32 * i + (wordBytes v).size ≤ (memoryExtend (memW ws) n).size := by
    rw [hsz, hv]; omega
  apply eq_of_byteAt
  · rw [size_memoryWrite hfit, hsz, size_memW]
  · intro k
    rw [byteAt_memoryWrite hfit, hv, byteAt_memoryExtend, byteAt_memW, byteAt_memW, wordAt_setW]
    by_cases hk : 32 * i ≤ k ∧ k < 32 * i + 32
    · rw [if_pos hk, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg hk, if_neg (by omega)]

/-- The bytes of the word number `i`. -/
theorem memW_readWord {ws : List U256} {o : Nat} {v : U256} (i : Nat) (ho : o = 32 * i)
    (hi : decide (i < ws.length) = true) (hv : wordAt ws i = v) :
    memoryReadBytes (memW ws) o 32 = wordBytes v := by
  subst ho hv
  have hi' := of_decide_eq_true hi
  have hfit : 32 * i + 32 ≤ (memW ws).size := by rw [size_memW]; omega
  apply eq_of_byteAt
  · rw [size_memoryReadBytes hfit, size_wordBytes]
  · intro k
    rw [byteAt_memoryReadBytes hfit]
    by_cases hk : k < 32
    · rw [if_pos hk, byteAt_memW]
      have e1 : (32 * i + k) / 32 = i := by omega
      have e2 : (32 * i + k) % 32 = k := by omega
      rw [e1, e2]
    · rw [if_neg hk]
      exact (byteAt_of_size_le (by rw [size_wordBytes]; omega)).symm

/-- MLOAD of the word number `i`. -/
theorem memW_load {ws : List U256} {o : Nat} {v : U256} (i : Nat) (ho : o = 32 * i)
    (hi : decide (i < ws.length) = true) (hv : wordAt ws i = v) :
    loadWord (memoryReadBytes (memW ws) o 32) 0 32 = v := by
  have hr := memW_readWord i ho hi hv
  subst ho
  have hi' := of_decide_eq_true hi
  have hfit : 32 * i + 32 ≤ (memW ws).size := by rw [size_memW]; omega
  have h := loadWord_memoryWrite_wordBytes (memory := memW ws) (start := 32 * i) v hfit
  have h2 := memoryReadBytes_memoryWrite (memory := memW ws) (start := 32 * i)
    (value := wordBytes v) (by rw [size_wordBytes]; exact hfit)
  rw [size_wordBytes] at h2
  rw [h2] at h
  rw [hr]
  exact h

theorem wordAt_drop : ∀ (ws : List U256) (i j : Nat), wordAt (ws.drop i) j = wordAt ws (i + j)
  | ws, 0, j => by rw [List.drop_zero, Nat.zero_add]
  | [], i + 1, j => by rw [List.drop_nil, wordAt_nil, wordAt_nil]
  | w :: ws, i + 1, j => by
    rw [List.drop_succ_cons, wordAt_drop ws i j]
    have e : i + 1 + j = (i + j) + 1 := by omega
    rw [e]
    rfl

theorem wordAt_take : ∀ (ws : List U256) (m j : Nat), j < m → wordAt (ws.take m) j = wordAt ws j
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | [], m + 1, j, _ => by rw [List.take_nil]
  | w :: ws, m + 1, 0, _ => rfl
  | w :: ws, m + 1, j + 1, h => by
    rw [List.take_succ_cons]
    show wordAt (ws.take m) j = wordAt ws j
    exact wordAt_take ws m j (by omega)

/-- The bytes of the words number `i` to `i + out.length - 1`. -/
theorem memW_readWords {ws out : List U256} {o k : Nat} (i : Nat) (ho : o = 32 * i)
    (hk : k = 32 * out.length) (hi : decide (i + out.length ≤ ws.length) = true)
    (hout : (ws.drop i).take out.length = out) :
    memoryReadBytes (memW ws) o k = memW out := by
  subst ho hk
  have hi' := of_decide_eq_true hi
  have hfit : 32 * i + 32 * out.length ≤ (memW ws).size := by rw [size_memW]; omega
  apply eq_of_byteAt
  · rw [size_memoryReadBytes hfit, size_memW]
  · intro k
    rw [byteAt_memoryReadBytes hfit, byteAt_memW, byteAt_memW]
    by_cases hk : k < 32 * out.length
    · rw [if_pos hk]
      have e1 : (32 * i + k) / 32 = i + k / 32 := by omega
      have e2 : (32 * i + k) % 32 = k % 32 := by omega
      have e3 : wordAt out (k / 32) = wordAt ws (i + k / 32) := by
        rw [← hout, wordAt_take _ _ _ (by omega), wordAt_drop]
      rw [e1, e2, e3]
    · rw [if_neg hk, wordAt_of_le out _ (by omega), byteAt_wordBytes_zero]

/-- The memory after the first write of a prelude: two zero words and the free memory pointer. -/
theorem memW_init_fp (fp : U256) :
    memoryWrite (memoryExtend .empty 96) 64 (wordBytes fp) = memW [0, 0, fp] := by
  have h0 : memoryExtend ByteArray.empty 96 = memW [0, 0, 0] := by
    have hz : ∀ j, byteAt ByteArray.empty j = 0 := fun j => byteAt_of_size_le (Nat.zero_le _)
    apply eq_of_byteAt
    · rw [size_memoryExtend, size_memW3]; rfl
    · intro i
      rw [byteAt_memoryExtend, hz]
      simp only [byteAt_memW_cons, byteAt_memW_nil, byteAt_wordBytes_zero]
      repeat' split
      all_goals rfl
  rw [h0, memW_write64]

end TokenKit

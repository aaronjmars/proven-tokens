import TokenKit.Evm.RawMem

/-!
# The first byte of a word of a raw memory

Solidity 0.8 packs a signature `r ++ s ++ v` as 65 bytes: `v` is written as a word whose first
byte it is, and the next allocation starts one byte later, so later writes cover the other 31
bytes of that word. The code then reads the word back and takes its first byte (BYTE 0). The
generator (`paths.top_bytes` of gen_paths.py) keeps, for a raw memory, a fact
`TopBytes m a n w` per such offset: the `n` bytes of the memory from `a` are the first `n` bytes
of the word `w` (the same holds for the two bytes `0x19 0x01` of an EIP-712 digest).

- `top_of_word`: a write that covers a known word but not its first bytes leaves those bytes.
- `top_rawW`: a write that does not cover the bytes leaves the fact.
- `readWords_one`, `readWords_cons`: the bytes of known words in a row, as a memory of words.
- `readTop_raw`: the known first bytes of a word and then the bytes after them (`topBytes`).
- `getByte0_raw`: BYTE 0 of the word read at `a` is BYTE 0 of `w`.
- `getByte0_eq`: BYTE 0 of a word is its first byte.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The `n` bytes of the memory `m` from `a` are the first `n` bytes of the word `w`. -/
def TopBytes (m : ByteArray) (a n : Nat) (w : U256) : Prop :=
  ∀ i, i < n → byteAt m (a + i) = byteAt (wordBytes w) i

/-- The first `n` bytes of a word, then other bytes: what a hash reads when its range starts
with the first bytes of a known word. -/
def topBytes (n : Nat) (w : U256) (d : ByteArray) : ByteArray :=
  (wordBytes w).extract 0 n ++ d

/-- A write of a word at `o` that starts `n` bytes or more after the known word at `a` leaves
its first `n` bytes. -/
theorem top_of_word {m : ByteArray} {sz k o a n : Nat} {v w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + k) (ha : a + 32 ≤ sz) (hd : a + n ≤ o) (hn : n ≤ 32) :
    TopBytes (memoryWrite (memoryExtend m k) o (wordBytes v)) a n w := by
  intro i hi
  rw [byteAt_memoryWrite (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit),
    if_neg (by omega), byteAt_memoryExtend, ← readWord_raw h hs ha,
    byteAt_memoryReadBytes (by omega), if_pos (by omega)]

/-- A write of a word at `o` that does not cover the bytes leaves the fact. -/
theorem top_rawW {m : ByteArray} {sz k o a n : Nat} {v w : U256} (h : TopBytes m a n w)
    (hs : m.size = sz) (hfit : o + 32 ≤ sz + k) (ha : a + n ≤ sz)
    (hd : a + n ≤ o ∨ o + 32 ≤ a) :
    TopBytes (memoryWrite (memoryExtend m k) o (wordBytes v)) a n w := by
  intro i hi
  rw [byteAt_memoryWrite (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit),
    if_neg (by rw [size_wordBytes]; omega), byteAt_memoryExtend]
  exact h i hi

/-- The 32 bytes of one known word, as a memory of one word. -/
theorem readWords_one {m : ByteArray} {sz a : Nat} {w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz) (ha : a + 32 ≤ sz) :
    memoryReadBytes m a 32 = memW [w] := by
  rw [readWord_raw h hs ha]
  show wordBytes w = wordBytes w ++ ByteArray.empty
  rw [ByteArray.append_empty]

/-- A known word and then the bytes of the words after it. -/
theorem readWords_cons {m : ByteArray} {sz a k : Nat} {w : U256} {ws : List U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w)
    (hr : memoryReadBytes m (a + 32) k = memW ws) (hs : m.size = sz) (hfit : a + 32 + k ≤ sz)
    (hk : 0 < k) : memoryReadBytes m a (32 + k) = memW (w :: ws) := by
  rw [memoryReadBytes_add (by omega) (by decide) hk, hr, readWord_raw h hs (by omega)]
  rfl

/-- The known first `n` bytes of a word and then the bytes after them. -/
theorem readTop_raw {m d : ByteArray} {sz a n k : Nat} {w : U256} (h : TopBytes m a n w)
    (hr : memoryReadBytes m (a + n) k = d) (hs : m.size = sz) (hfit : a + n + k ≤ sz)
    (hn : 0 < n) (hk : 0 < k) (hn32 : n ≤ 32) :
    memoryReadBytes m a (n + k) = topBytes n w d := by
  unfold topBytes
  rw [memoryReadBytes_add (by omega) hn hk, hr]
  congr 1
  apply eq_of_byteAt
  · rw [size_memoryReadBytes (by omega), ByteArray.size_extract, size_wordBytes]
    omega
  · intro i
    rw [byteAt_memoryReadBytes (by omega), byteAt_extract, size_wordBytes, Nat.zero_add]
    by_cases hi : i < n
    · rw [if_pos hi, if_pos (by omega)]
      exact h i hi
    · rw [if_neg hi, if_neg (by omega)]

/-- BYTE 0 of a word is its first byte. -/
theorem getByte0_eq (x : U256) :
    getByte 0 x = BitVec.ofNat 256 (byteAt (wordBytes x) 0).toNat := by
  have hl : (wordBytes x).data.toList = natToBytes 32 x.toNat :=
    EthLib.Base.U256.toList_toBeBytes _
  have hlen : (natToBytes 32 x.toNat).length = 32 := natToBytes_length _ _
  obtain ⟨b, rest, hbr⟩ : ∃ b rest, natToBytes 32 x.toNat = b :: rest := by
    cases hc : natToBytes 32 x.toNat with
    | nil => rw [hc] at hlen; simp at hlen
    | cons b rest => exact ⟨b, rest, rfl⟩
  have hrl : rest.length = 31 := by
    rw [hbr] at hlen
    simpa using hlen
  have hx : x.toNat < 256 ^ 32 := by
    have := x.isLt
    rwa [show (256 : Nat) ^ 32 = 2 ^ 256 by decide]
  have hv : x.toNat = b.toNat * 256 ^ 31 + bytesToNat rest := by
    have h := bytesToNat_natToBytes_of_lt hx
    rw [hbr, bytesToNat_cons, hrl] at h
    exact h.symm
  have hr : bytesToNat rest < 256 ^ 31 := by
    have h := bytesToNat_lt rest
    rwa [hrl] at h
  have hb : byteAt (wordBytes x) 0 = b := by
    have hsz : (wordBytes x).size = 32 := size_wordBytes x
    unfold byteAt
    rw [dif_pos (by rw [hsz]; decide), ByteArray.getElem_eq_getElem_data]
    have : (wordBytes x).data[0]'(by rw [ByteArray.size_data, hsz]; decide) =
        (wordBytes x).data.toList[0]'(by
          rw [Array.length_toList, ByteArray.size_data, hsz]; decide) := by
      simp
    rw [this]
    simp [hl, hbr]
  have hdiv : x.toNat / 2 ^ 248 = b.toNat := by
    rw [hv, show (256 : Nat) ^ 31 = 2 ^ 248 by decide] at *
    have hb8 : b.toNat < 256 := b.toNat_lt
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by decide : 0 < 2 ^ 248),
      Nat.div_eq_of_lt (by rwa [show (256 : Nat) ^ 31 = 2 ^ 248 by decide] at hr), Nat.zero_add]
  rw [hb]
  apply BitVec.eq_of_toNat_eq
  have h0 : ¬((0 : U256).toNat ≥ 32) := by decide
  have hb8 : b.toNat < 256 := b.toNat_lt
  unfold getByte
  rw [if_neg h0, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    show (0 : U256).toNat = 0 by decide, Nat.shiftRight_eq_div_pow,
    show (31 - 0) * 8 = 248 by decide, hdiv, Nat.mod_eq_of_lt (by omega),
    show (0xff : U256).toNat = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- BYTE 0 of the word read at `a` is BYTE 0 of the word whose first bytes the memory holds
there. -/
theorem getByte0_raw {m : ByteArray} {sz a n : Nat} {w : U256} (h : TopBytes m a n w)
    (hs : m.size = sz) (ha : a + 32 ≤ sz) (hn : 0 < n) :
    getByte 0 (loadWord (memoryReadBytes m a 32) 0 32) = getByte 0 w := by
  have h0 := h 0 hn
  rw [Nat.add_zero] at h0
  rw [getByte0_eq, getByte0_eq, wordBytes_loadWord (size_memoryReadBytes (by omega)),
    byteAt_memoryReadBytes (by omega), if_pos (by decide), Nat.add_zero, h0]

end TokenKit

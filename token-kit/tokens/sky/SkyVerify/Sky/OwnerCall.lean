import SkyVerify.Sky.Permit
import TokenKit.Evm.Tail

/-!
# SKY: the STATICCALL that `permit` makes to the owner (ERC-1271), with its call data

Hand-written, for audit 4 (SKY-1). Three parts.

- The call data. `erc1271Input dg r s vw` is the 196 bytes of
  `isValidSignature(bytes32 digest, bytes signature)` for a signature of 65 bytes: the selector
  `0x1626ba7e`, the digest, the offset 64, the length 65, `r`, `s`, the byte `v` (the first byte
  of the word `vw`) and 31 zero bytes. `code_data` and `copy_data` prove that the bytes the code
  of `permit` builds in the memory, and then copies, are these bytes, for every layout of the
  memory (the free memory pointer `F` is a parameter).
- `staticcall_sent`: `staticcall_kept` of TokenKit/Evm/StaticCall.lean, with one more fact. When
  the flag pushed is not 0, a message was sent as EthLib's `CallSends` says, the real runner ran
  it to a frame with no error, and the return data `out` is the output of that frame.
- `OwnerCall`: these facts in plain terms for the call of `permit`: who is called, with which
  call data, which gas, in which state, and that `out` is the output of that run.

Nothing is assumed on the code of the owner.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

/-! ## Bytes of a memory after a write of a word -/

/-- A byte of the memory after a write of a word (the memory grown by `n` bytes first). -/
theorem byteAt_rawW {m : ByteArray} {sz n o : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (i : Nat) :
    byteAt (memoryWrite (memoryExtend m n) o (wordBytes v)) i =
      if o ≤ i ∧ i < o + 32 then byteAt (wordBytes v) (i - o) else byteAt m i := by
  rw [byteAt_memoryWrite (by rw [size_memoryExtend, size_wordBytes, hs]; exact hfit),
    size_wordBytes, byteAt_memoryExtend]

/-- A byte outside the word written is the byte of before. -/
theorem byteAt_rawW_miss {m : ByteArray} {sz n o i : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (h : i < o ∨ o + 32 ≤ i) :
    byteAt (memoryWrite (memoryExtend m n) o (wordBytes v)) i = byteAt m i := by
  rw [byteAt_rawW hs hfit, if_neg (by omega)]

/-- A byte inside the word written is a byte of the word. -/
theorem byteAt_rawW_hit {m : ByteArray} {sz n o i : Nat} {v : U256} (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (h1 : o ≤ i) (h2 : i < o + 32) :
    byteAt (memoryWrite (memoryExtend m n) o (wordBytes v)) i = byteAt (wordBytes v) (i - o) := by
  rw [byteAt_rawW hs hfit, if_pos ⟨h1, h2⟩]

/-- A byte of a word read from the memory is a byte of the memory. -/
theorem byteAt_wordOf {m : ByteArray} {a j : Nat} (h : a + 32 ≤ m.size) (hj : j < 32) :
    byteAt (wordBytes (loadWord (memoryReadBytes m a 32) 0 32)) j = byteAt m (a + j) := by
  rw [wordBytes_loadWord (size_memoryReadBytes h), byteAt_memoryReadBytes h, if_pos hj]

/-- A read of `k` bytes inside the memory is the string `b` of `k` bytes when each byte is. -/
theorem read_eq_of_bytes {m b : ByteArray} {s k : Nat} (hfit : s + k ≤ m.size)
    (hb : b.size = k) (h : ∀ j, j < k → byteAt m (s + j) = byteAt b j) :
    memoryReadBytes m s k = b := by
  apply eq_of_byteAt (by rw [size_memoryReadBytes hfit, hb])
  intro i
  rw [byteAt_memoryReadBytes hfit]
  by_cases hi : i < k
  · rw [if_pos hi]
    exact h i hi
  · rw [if_neg hi]
    exact (byteAt_of_size_le (by omega)).symm

/-! ## The first 4 bytes and the last 28 bytes of a word -/

/-- A byte of a string, from its list of bytes. -/
theorem byteAt_toList (b : ByteArray) (j : Nat) : byteAt b j = (b.data.toList[j]?).getD 0 := by
  rw [byteAt_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-- The 32 bytes of a word: 4 bytes of its high part, then 28 bytes. -/
theorem wordBytes_toList (w : U256) :
    (wordBytes w).data.toList = natToBytes 4 (w.toNat / 256 ^ 28) ++ natToBytes 28 w.toNat := by
  rw [← natToBytes_add 4 28]
  exact U256.toList_toBeBytes w

/-- The bytes written on `len` bytes depend on the number modulo `256 ^ len` only. -/
theorem natToBytes_mod (len n : Nat) : natToBytes len (n % 256 ^ len) = natToBytes len n := by
  have h := natToBytes_bytesToNat (natToBytes len n)
  rw [natToBytes_length, bytesToNat_natToBytes] at h
  exact h

/-- Two words with the same high 32 bits have the same first 4 bytes. -/
theorem byteAt_wordBytes_lo {w w' : U256} (h : w.toNat / 256 ^ 28 = w'.toNat / 256 ^ 28)
    {j : Nat} (hj : j < 4) : byteAt (wordBytes w) j = byteAt (wordBytes w') j := by
  rw [byteAt_toList, byteAt_toList, wordBytes_toList, wordBytes_toList, h,
    List.getElem?_append_left (by rw [natToBytes_length]; exact hj),
    List.getElem?_append_left (by rw [natToBytes_length]; exact hj)]

/-- Two words with the same low 224 bits have the same last 28 bytes. -/
theorem byteAt_wordBytes_hi {w w' : U256} (h : w.toNat % 256 ^ 28 = w'.toNat % 256 ^ 28)
    {j : Nat} (hj : 4 ≤ j) : byteAt (wordBytes w) j = byteAt (wordBytes w') j := by
  have e : natToBytes 28 w.toNat = natToBytes 28 w'.toNat := by
    rw [← natToBytes_mod, h, natToBytes_mod]
  rw [byteAt_toList, byteAt_toList, wordBytes_toList, wordBytes_toList, e,
    List.getElem?_append_right (by rw [natToBytes_length]; exact hj),
    List.getElem?_append_right (by rw [natToBytes_length]; exact hj), natToBytes_length,
    natToBytes_length]

/-- The ERC-1271 magic value as a word: `0x1626ba7e` and then 28 zero bytes. -/
abbrev MAGIC_1271 : U256 :=
  (10019309979067222254582373821846632475949454479833780424560900009889672200192 : U256)

/-- The low 224 bits: `2 ^ 224 - 1`. -/
abbrev MASK_224 : U256 :=
  (26959946667150639794667015087019630673637144422540572481103610249215 : U256)

/-- The word that the code writes over the selector place: the selector, then the low 224 bits
of the word `X` that was there. -/
theorem magicOr_toNat (X : U256) :
    (bitwiseOr MAGIC_1271 (bitwiseAnd MASK_224 X)).toNat =
      2 ^ 224 * 371636862 + X.toNat % 2 ^ 224 := by
  have hm : MASK_224.toNat = 2 ^ 224 - 1 := by decide
  have hM : MAGIC_1271.toNat = 2 ^ 224 * 371636862 := by decide
  show (MAGIC_1271 ||| (MASK_224 &&& X)).toNat = _
  rw [BitVec.toNat_or, BitVec.toNat_and, hm, hM, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 224)) 371636862]

/-- Its first 4 bytes are the bytes of the selector. -/
theorem magicOr_lo (X : U256) {j : Nat} (hj : j < 4) :
    byteAt (wordBytes (bitwiseOr MAGIC_1271 (bitwiseAnd MASK_224 X))) j =
      byteAt (wordBytes MAGIC_1271) j := by
  apply byteAt_wordBytes_lo _ hj
  have h := magicOr_toNat X
  have hM : MAGIC_1271.toNat = 2 ^ 224 * 371636862 := by decide
  have h2 : (256 : Nat) ^ 28 = 2 ^ 224 := by decide
  rw [h2]
  omega

/-- Its last 28 bytes are the bytes of `X`. -/
theorem magicOr_hi (X : U256) {j : Nat} (hj : 4 ≤ j) :
    byteAt (wordBytes (bitwiseOr MAGIC_1271 (bitwiseAnd MASK_224 X))) j =
      byteAt (wordBytes X) j := by
  apply byteAt_wordBytes_hi _ hj
  have h := magicOr_toNat X
  have h2 : (256 : Nat) ^ 28 = 2 ^ 224 := by decide
  rw [h2]
  omega

/-! ## The call data of `isValidSignature(bytes32,bytes)` -/

/-- The call data that `permit` sends to the owner: the selector `0x1626ba7e` of
`isValidSignature(bytes32,bytes)`, the digest `dg`, the offset 64 of the bytes, their length 65,
then the 65 bytes of the signature (`r`, `s`, and the byte `v`, the first byte of the word `vw`)
and 31 zero bytes. 196 bytes. -/
def erc1271Input (dg r s vw : U256) : ByteArray :=
  (wordBytes MAGIC_1271).extract 0 4 ++ (wordBytes dg ++ (wordBytes (64 : U256) ++
    (wordBytes (65 : U256) ++ (wordBytes r ++ (wordBytes s ++
      ((wordBytes vw).extract 0 1 ++ (wordBytes (0 : U256)).extract 0 31))))))

/-- A read of 196 bytes, in the 8 parts of the call data. -/
theorem read196 {P : ByteArray} {a : Nat} (h : a + 196 ≤ P.size) :
    memoryReadBytes P a 196 = memoryReadBytes P a 4 ++ (memoryReadBytes P (a + 4) 32 ++
      (memoryReadBytes P (a + 36) 32 ++ (memoryReadBytes P (a + 68) 32 ++
        (memoryReadBytes P (a + 100) 32 ++ (memoryReadBytes P (a + 132) 32 ++
          (memoryReadBytes P (a + 164) 1 ++ memoryReadBytes P (a + 165) 31)))))) := by
  have e1 : memoryReadBytes P a 196 = memoryReadBytes P a 4 ++ memoryReadBytes P (a + 4) 192 :=
    memoryReadBytes_add (j := 4) (k := 192) (by omega) (by decide) (by decide)
  have e2 : memoryReadBytes P (a + 4) 192 =
      memoryReadBytes P (a + 4) 32 ++ memoryReadBytes P (a + 36) 160 := by
    have t := memoryReadBytes_add (m := P) (s := a + 4) (j := 32) (k := 160) (by omega)
      (by decide) (by decide)
    rwa [show a + 4 + 32 = a + 36 from by omega] at t
  have e3 : memoryReadBytes P (a + 36) 160 =
      memoryReadBytes P (a + 36) 32 ++ memoryReadBytes P (a + 68) 128 := by
    have t := memoryReadBytes_add (m := P) (s := a + 36) (j := 32) (k := 128) (by omega)
      (by decide) (by decide)
    rwa [show a + 36 + 32 = a + 68 from by omega] at t
  have e4 : memoryReadBytes P (a + 68) 128 =
      memoryReadBytes P (a + 68) 32 ++ memoryReadBytes P (a + 100) 96 := by
    have t := memoryReadBytes_add (m := P) (s := a + 68) (j := 32) (k := 96) (by omega)
      (by decide) (by decide)
    rwa [show a + 68 + 32 = a + 100 from by omega] at t
  have e5 : memoryReadBytes P (a + 100) 96 =
      memoryReadBytes P (a + 100) 32 ++ memoryReadBytes P (a + 132) 64 := by
    have t := memoryReadBytes_add (m := P) (s := a + 100) (j := 32) (k := 64) (by omega)
      (by decide) (by decide)
    rwa [show a + 100 + 32 = a + 132 from by omega] at t
  have e6 : memoryReadBytes P (a + 132) 64 =
      memoryReadBytes P (a + 132) 32 ++ memoryReadBytes P (a + 164) 32 := by
    have t := memoryReadBytes_add (m := P) (s := a + 132) (j := 32) (k := 32) (by omega)
      (by decide) (by decide)
    rwa [show a + 132 + 32 = a + 164 from by omega] at t
  have e7 : memoryReadBytes P (a + 164) 32 =
      memoryReadBytes P (a + 164) 1 ++ memoryReadBytes P (a + 165) 31 := by
    have t := memoryReadBytes_add (m := P) (s := a + 164) (j := 1) (k := 31) (by omega)
      (by decide) (by decide)
    rwa [show a + 164 + 1 = a + 165 from by omega] at t
  rw [e1, e2, e3, e4, e5, e6, e7]

/-- The memory after the code of `permit` built the call data (pc 3580 to 3660), for every
layout: `F` is the free memory pointer and `sz` the size of the memory `M` before. The ten
writes are the ones of the generated segments (`Paths.permitCodeA_ends` and the like), given as
equations so that one lemma serves the four layouts. The 196 bytes at `F + 32` are
`erc1271Input`. `htop`: the byte at 224 of `M` is the first byte of `vw`. -/
theorem code_data {M P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : ByteArray} {F sz : Nat}
    {dg sR sS vw fpn : U256}
    (hs : M.size = sz) (htop : TopBytes M 224 1 vw) (hF : 256 ≤ F) (hfit : F + 133 ≤ sz)
    (e1 : P1 = memoryWrite (memoryExtend M 0) (F + 36) (wordBytes dg))
    (e2 : P2 = memoryWrite (memoryExtend P1 0) (F + 68) (wordBytes (64 : U256)))
    (e3 : P3 = memoryWrite (memoryExtend P2 0) (F + 100) (wordBytes (65 : U256)))
    (e4 : P4 = memoryWrite (memoryExtend P3 32) (F + 132) (wordBytes sR))
    (e5 : P5 = memoryWrite (memoryExtend P4 32) (F + 164) (wordBytes sS))
    (e6 : P6 = memoryWrite (memoryExtend P5 32) (F + 196)
      (wordBytes (loadWord (memoryReadBytes P5 224 32) 0 32)))
    (e7 : P7 = memoryWrite (memoryExtend P6 0) (F + 197) (wordBytes (0 : U256)))
    (e8 : P8 = memoryWrite (memoryExtend P7 0) F (wordBytes (196 : U256)))
    (e9 : P9 = memoryWrite (memoryExtend P8 0) 64 (wordBytes fpn))
    (e10 : P10 = memoryWrite (memoryExtend P9 0) (F + 32)
      (wordBytes (bitwiseOr MAGIC_1271 (bitwiseAnd MASK_224
        (loadWord (memoryReadBytes P9 (F + 32) 32) 0 32))))) :
    P10.size = sz + 96 ∧ memoryReadBytes P10 (F + 32) 196 = erc1271Input dg sR sS vw := by
  have s1 : P1.size = sz := by rw [e1]; exact size_rawW hs (by omega)
  have s2 : P2.size = sz := by rw [e2]; exact size_rawW s1 (by omega)
  have s3 : P3.size = sz := by rw [e3]; exact size_rawW s2 (by omega)
  have s4 : P4.size = sz + 32 := by rw [e4]; exact size_rawW s3 (by omega)
  have s5 : P5.size = sz + 64 := by rw [e5]; exact (size_rawW s4 (by omega)).trans (by omega)
  have s6 : P6.size = sz + 96 := by rw [e6]; exact (size_rawW s5 (by omega)).trans (by omega)
  have s7 : P7.size = sz + 96 := by rw [e7]; exact size_rawW s6 (by omega)
  have s8 : P8.size = sz + 96 := by rw [e8]; exact size_rawW s7 (by omega)
  have s9 : P9.size = sz + 96 := by rw [e9]; exact size_rawW s8 (by omega)
  have s10 : P10.size = sz + 96 := by rw [e10]; exact size_rawW s9 (by omega)
  -- the bytes that each write keeps
  have L1 : ∀ i, (i < F + 36 ∨ F + 36 + 32 ≤ i) → byteAt P1 i = byteAt M i := fun i h => by
    rw [e1]; exact byteAt_rawW_miss hs (by omega) h
  have L2 : ∀ i, (i < F + 68 ∨ F + 68 + 32 ≤ i) → byteAt P2 i = byteAt P1 i := fun i h => by
    rw [e2]; exact byteAt_rawW_miss s1 (by omega) h
  have L3 : ∀ i, (i < F + 100 ∨ F + 100 + 32 ≤ i) → byteAt P3 i = byteAt P2 i := fun i h => by
    rw [e3]; exact byteAt_rawW_miss s2 (by omega) h
  have L4 : ∀ i, (i < F + 132 ∨ F + 132 + 32 ≤ i) → byteAt P4 i = byteAt P3 i := fun i h => by
    rw [e4]; exact byteAt_rawW_miss s3 (by omega) h
  have L5 : ∀ i, (i < F + 164 ∨ F + 164 + 32 ≤ i) → byteAt P5 i = byteAt P4 i := fun i h => by
    rw [e5]; exact byteAt_rawW_miss s4 (by omega) h
  have L6 : ∀ i, (i < F + 196 ∨ F + 196 + 32 ≤ i) → byteAt P6 i = byteAt P5 i := fun i h => by
    rw [e6]; exact byteAt_rawW_miss s5 (by omega) h
  have L7 : ∀ i, (i < F + 197 ∨ F + 197 + 32 ≤ i) → byteAt P7 i = byteAt P6 i := fun i h => by
    rw [e7]; exact byteAt_rawW_miss s6 (by omega) h
  have L8 : ∀ i, (i < F ∨ F + 32 ≤ i) → byteAt P8 i = byteAt P7 i := fun i h => by
    rw [e8]; exact byteAt_rawW_miss s7 (by omega) h
  have L9 : ∀ i, (i < 64 ∨ 64 + 32 ≤ i) → byteAt P9 i = byteAt P8 i := fun i h => by
    rw [e9]; exact byteAt_rawW_miss s8 (by omega) h
  have L10 : ∀ i, (i < F + 32 ∨ F + 32 + 32 ≤ i) → byteAt P10 i = byteAt P9 i := fun i h => by
    rw [e10]; exact byteAt_rawW_miss s9 (by omega) h
  -- the bytes that each write puts
  have H1 : ∀ i, F + 36 ≤ i → i < F + 36 + 32 →
      byteAt P1 i = byteAt (wordBytes dg) (i - (F + 36)) := fun i h1 h2 => by
    rw [e1]; exact byteAt_rawW_hit hs (by omega) h1 h2
  have H2 : ∀ i, F + 68 ≤ i → i < F + 68 + 32 →
      byteAt P2 i = byteAt (wordBytes (64 : U256)) (i - (F + 68)) := fun i h1 h2 => by
    rw [e2]; exact byteAt_rawW_hit s1 (by omega) h1 h2
  have H3 : ∀ i, F + 100 ≤ i → i < F + 100 + 32 →
      byteAt P3 i = byteAt (wordBytes (65 : U256)) (i - (F + 100)) := fun i h1 h2 => by
    rw [e3]; exact byteAt_rawW_hit s2 (by omega) h1 h2
  have H4 : ∀ i, F + 132 ≤ i → i < F + 132 + 32 →
      byteAt P4 i = byteAt (wordBytes sR) (i - (F + 132)) := fun i h1 h2 => by
    rw [e4]; exact byteAt_rawW_hit s3 (by omega) h1 h2
  have H5 : ∀ i, F + 164 ≤ i → i < F + 164 + 32 →
      byteAt P5 i = byteAt (wordBytes sS) (i - (F + 164)) := fun i h1 h2 => by
    rw [e5]; exact byteAt_rawW_hit s4 (by omega) h1 h2
  have H6 : ∀ i, F + 196 ≤ i → i < F + 196 + 32 →
      byteAt P6 i = byteAt (wordBytes (loadWord (memoryReadBytes P5 224 32) 0 32))
        (i - (F + 196)) := fun i h1 h2 => by
    rw [e6]; exact byteAt_rawW_hit s5 (by omega) h1 h2
  have H7 : ∀ i, F + 197 ≤ i → i < F + 197 + 32 →
      byteAt P7 i = byteAt (wordBytes (0 : U256)) (i - (F + 197)) := fun i h1 h2 => by
    rw [e7]; exact byteAt_rawW_hit s6 (by omega) h1 h2
  have H10 : ∀ i, F + 32 ≤ i → i < F + 32 + 32 →
      byteAt P10 i = byteAt (wordBytes (bitwiseOr MAGIC_1271 (bitwiseAnd MASK_224
        (loadWord (memoryReadBytes P9 (F + 32) 32) 0 32)))) (i - (F + 32)) := fun i h1 h2 => by
    rw [e10]; exact byteAt_rawW_hit s9 (by omega) h1 h2
  -- the bytes of the memory before the last write
  have Rdg : ∀ i, F + 36 ≤ i → i < F + 68 →
      byteAt P9 i = byteAt (wordBytes dg) (i - (F + 36)) := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), L7 i (by omega), L6 i (by omega), L5 i (by omega),
      L4 i (by omega), L3 i (by omega), L2 i (by omega), H1 i h1 (by omega)]
  have R64 : ∀ i, F + 68 ≤ i → i < F + 100 →
      byteAt P9 i = byteAt (wordBytes (64 : U256)) (i - (F + 68)) := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), L7 i (by omega), L6 i (by omega), L5 i (by omega),
      L4 i (by omega), L3 i (by omega), H2 i h1 (by omega)]
  have R65 : ∀ i, F + 100 ≤ i → i < F + 132 →
      byteAt P9 i = byteAt (wordBytes (65 : U256)) (i - (F + 100)) := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), L7 i (by omega), L6 i (by omega), L5 i (by omega),
      L4 i (by omega), H3 i h1 (by omega)]
  have Rr : ∀ i, F + 132 ≤ i → i < F + 164 →
      byteAt P9 i = byteAt (wordBytes sR) (i - (F + 132)) := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), L7 i (by omega), L6 i (by omega), L5 i (by omega),
      H4 i h1 (by omega)]
  have Rs : ∀ i, F + 164 ≤ i → i < F + 196 →
      byteAt P9 i = byteAt (wordBytes sS) (i - (F + 164)) := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), L7 i (by omega), L6 i (by omega),
      H5 i h1 (by omega)]
  have Rv : byteAt P9 (F + 196) = byteAt (wordBytes vw) 0 := by
    rw [L9 _ (by omega), L8 _ (by omega), L7 _ (by omega), H6 _ (Nat.le_refl _) (by omega),
      Nat.sub_self, byteAt_wordOf (by rw [s5]; omega) (by decide), L5 _ (by omega),
      L4 _ (by omega), L3 _ (by omega), L2 _ (by omega), L1 _ (by omega)]
    exact htop 0 (by decide)
  have Rz : ∀ i, F + 197 ≤ i → i < F + 229 → byteAt P9 i = 0 := fun i h1 h2 => by
    rw [L9 i (by omega), L8 i (by omega), H7 i h1 (by omega), byteAt_wordBytes_zero]
  -- the last write keeps every byte from `F + 36` on, and puts the selector before
  have T : ∀ i, F + 36 ≤ i → byteAt P10 i = byteAt P9 i := fun i h => by
    by_cases hc : i < F + 32 + 32
    · rw [H10 i (by omega) hc, magicOr_hi _ (by omega),
        byteAt_wordOf (by rw [s9]; omega) (by omega)]
      congr 1
      omega
    · exact L10 i (.inr (by omega))
  have T0 : ∀ j, j < 4 → byteAt P10 (F + 32 + j) = byteAt (wordBytes MAGIC_1271) j :=
    fun j hj => by
      rw [H10 _ (by omega) (by omega), Nat.add_sub_cancel_left, magicOr_lo _ hj]
  have f10 : F + 32 + 196 ≤ P10.size := by rw [s10]; omega
  refine ⟨s10, ?_⟩
  have A0 : memoryReadBytes P10 (F + 32) 4 = (wordBytes MAGIC_1271).extract 0 4 :=
    read_eq_of_bytes (by omega) (by simp [ByteArray.size_extract, size_wordBytes])
      fun j hj => by
        rw [T0 j hj, byteAt_extract, size_wordBytes,
          if_pos (Nat.lt_min.mpr ⟨by omega, by omega⟩), Nat.zero_add]
  have A1 : memoryReadBytes P10 (F + 32 + 4) 32 = wordBytes dg :=
    read_eq_of_bytes (by omega) (size_wordBytes _) fun j hj => by
      rw [T _ (by omega), Rdg _ (by omega) (by omega)]
      congr 1
      omega
  have A2 : memoryReadBytes P10 (F + 32 + 36) 32 = wordBytes (64 : U256) :=
    read_eq_of_bytes (by omega) (size_wordBytes _) fun j hj => by
      rw [T _ (by omega), R64 _ (by omega) (by omega)]
      congr 1
      omega
  have A3 : memoryReadBytes P10 (F + 32 + 68) 32 = wordBytes (65 : U256) :=
    read_eq_of_bytes (by omega) (size_wordBytes _) fun j hj => by
      rw [T _ (by omega), R65 _ (by omega) (by omega)]
      congr 1
      omega
  have A4 : memoryReadBytes P10 (F + 32 + 100) 32 = wordBytes sR :=
    read_eq_of_bytes (by omega) (size_wordBytes _) fun j hj => by
      rw [T _ (by omega), Rr _ (by omega) (by omega)]
      congr 1
      omega
  have A5 : memoryReadBytes P10 (F + 32 + 132) 32 = wordBytes sS :=
    read_eq_of_bytes (by omega) (size_wordBytes _) fun j hj => by
      rw [T _ (by omega), Rs _ (by omega) (by omega)]
      congr 1
      omega
  have A6 : memoryReadBytes P10 (F + 32 + 164) 1 = (wordBytes vw).extract 0 1 :=
    read_eq_of_bytes (by omega) (by simp [ByteArray.size_extract, size_wordBytes])
      fun j hj => by
        obtain rfl : j = 0 := by omega
        rw [T _ (by omega), show F + 32 + 164 + 0 = F + 196 from by omega, Rv, byteAt_extract,
          size_wordBytes, if_pos (by decide)]
  have A7 : memoryReadBytes P10 (F + 32 + 165) 31 = (wordBytes (0 : U256)).extract 0 31 :=
    read_eq_of_bytes (by omega) (by simp [ByteArray.size_extract, size_wordBytes])
      fun j hj => by
        rw [T _ (by omega), Rz _ (by omega) (by omega), byteAt_extract]
        split
        · exact (byteAt_wordBytes_zero _).symm
        · rfl
  rw [read196 f10, A0, A1, A2, A3, A4, A5, A6, A7]
  rfl

/-! ## The copy of the call data -/

/-- The state of the copy loop of `permit` (pc 3660 to 3681) after `k` words: the memory `Q` has
grown by `32 * k` bytes from `sz0`, its bytes below `G` are those of the memory `Q0` at the
start, and its bytes from `G` on, below `32 * k` and below 196, are the bytes of `Q0` from `S`
on. -/
def CopyInv (Q0 : ByteArray) (S G sz0 k : Nat) (Q : ByteArray) : Prop :=
  Q.size = sz0 + 32 * k ∧ (∀ i, i < G → byteAt Q i = byteAt Q0 i) ∧
    (∀ j, j < 32 * k → j < 196 → byteAt Q (G + j) = byteAt Q0 (S + j))

/-- One word of the copy. -/
theorem copy_step {Q0 Q : ByteArray} {S G sz0 k : Nat} (hSG : S + 196 = G) (hG : G ≤ sz0)
    (inv : CopyInv Q0 S G sz0 k Q) :
    CopyInv Q0 S G sz0 (k + 1) (memoryWrite (memoryExtend Q 32) (G + 32 * k)
      (wordBytes (loadWord (memoryReadBytes Q (S + 32 * k) 32) 0 32))) := by
  obtain ⟨hs, hlow, hhi⟩ := inv
  have fit : G + 32 * k + 32 ≤ sz0 + 32 * k + 32 := by omega
  refine ⟨(size_rawW hs fit).trans (by omega), fun i hi => ?_, fun j hj hj' => ?_⟩
  · rw [byteAt_rawW_miss hs fit (.inl (by omega))]
    exact hlow i hi
  · by_cases hc : j < 32 * k
    · rw [byteAt_rawW_miss hs fit (.inl (by omega))]
      exact hhi j hc hj'
    · rw [byteAt_rawW_hit hs fit (by omega) (by omega),
        byteAt_wordOf (by rw [hs]; omega) (by omega),
        show S + 32 * k + (G + j - (G + 32 * k)) = S + j from by omega]
      exact hlow _ (by omega)

/-- The memory after the copy loop of `permit` (pc 3660 to 3681), for every layout: the seven
words copied from `S` to `G` (`S + 196 = G`), then a zero word written after them. The eight
writes are the ones of the generated segments (`Paths.permitCopyA_ends` and the like). The 196
bytes at `G` are the 196 bytes that were at `S`. -/
theorem copy_data {Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : ByteArray} {S G sz0 : Nat}
    (hs : Q0.size = sz0) (hSG : S + 196 = G) (hG : G + 4 ≤ sz0)
    (e1 : Q1 = memoryWrite (memoryExtend Q0 32) G
      (wordBytes (loadWord (memoryReadBytes Q0 S 32) 0 32)))
    (e2 : Q2 = memoryWrite (memoryExtend Q1 32) (G + 32)
      (wordBytes (loadWord (memoryReadBytes Q1 (S + 32) 32) 0 32)))
    (e3 : Q3 = memoryWrite (memoryExtend Q2 32) (G + 64)
      (wordBytes (loadWord (memoryReadBytes Q2 (S + 64) 32) 0 32)))
    (e4 : Q4 = memoryWrite (memoryExtend Q3 32) (G + 96)
      (wordBytes (loadWord (memoryReadBytes Q3 (S + 96) 32) 0 32)))
    (e5 : Q5 = memoryWrite (memoryExtend Q4 32) (G + 128)
      (wordBytes (loadWord (memoryReadBytes Q4 (S + 128) 32) 0 32)))
    (e6 : Q6 = memoryWrite (memoryExtend Q5 32) (G + 160)
      (wordBytes (loadWord (memoryReadBytes Q5 (S + 160) 32) 0 32)))
    (e7 : Q7 = memoryWrite (memoryExtend Q6 32) (G + 192)
      (wordBytes (loadWord (memoryReadBytes Q6 (S + 192) 32) 0 32)))
    (e8 : Q8 = memoryWrite (memoryExtend Q7 0) (G + 196) (wordBytes (0 : U256))) :
    Q8.size = sz0 + 224 ∧ memoryReadBytes Q8 G 196 = memoryReadBytes Q0 S 196 := by
  have c0 : CopyInv Q0 S G sz0 0 Q0 := ⟨hs, fun _ _ => rfl, fun j hj => absurd hj (by omega)⟩
  have c1 : CopyInv Q0 S G sz0 1 Q1 := by
    rw [e1]; exact copy_step (k := 0) hSG (by omega) c0
  have c2 : CopyInv Q0 S G sz0 2 Q2 := by
    rw [e2]; exact copy_step (k := 1) hSG (by omega) c1
  have c3 : CopyInv Q0 S G sz0 3 Q3 := by
    rw [e3]; exact copy_step (k := 2) hSG (by omega) c2
  have c4 : CopyInv Q0 S G sz0 4 Q4 := by
    rw [e4]; exact copy_step (k := 3) hSG (by omega) c3
  have c5 : CopyInv Q0 S G sz0 5 Q5 := by
    rw [e5]; exact copy_step (k := 4) hSG (by omega) c4
  have c6 : CopyInv Q0 S G sz0 6 Q6 := by
    rw [e6]; exact copy_step (k := 5) hSG (by omega) c5
  have c7 : CopyInv Q0 S G sz0 7 Q7 := by
    rw [e7]; exact copy_step (k := 6) hSG (by omega) c6
  obtain ⟨h7, -, hhi⟩ := c7
  have fit : G + 196 + 32 ≤ sz0 + 32 * 7 + 0 := by omega
  rw [e8]
  refine ⟨(size_rawW h7 fit).trans (by omega), ?_⟩
  apply read_eq_of_bytes (by rw [size_rawW h7 fit]; omega) (size_memoryReadBytes (by omega))
  intro j hj
  rw [byteAt_rawW_miss h7 fit (.inl (by omega)), hhi j (by omega) hj,
    byteAt_memoryReadBytes (by omega), if_pos hj]

/-! ## The STATICCALL, with the message that was sent -/

/-- `staticcall_kept` of the kit, with one more fact (the last one). When the flag pushed is not
0, a message was sent: the state holds a code `calleeCode` for the address called, the call
follows a route (the code itself, or the code of an EIP-7702 delegate), the caller frame and the
message are the ones of EthLib's `CallSends`, the real runner ran the message to a frame `child`
with no error, and the return data `out` is the output of `child`. -/
theorem staticcall_sent {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {asked to inputStart inputSize outputStart outputSize : U256} {rest : List U256}
    {rd : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfa)
    {bound : Nat} {evm s : Evm fork Nat}
    (start : Logic.At code message pc
      (asked :: to :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s) :
    s.error ≠ none ∨
    ∃ (flag : U256) (out : ByteArray) (g : Nat) (st : State.TransactionState) (ss : Substate)
        (after : Evm fork Nat),
      (flag = 0 ∨ flag = 1) ∧
      Logic.At code message (pc + 1) (flag :: rest)
        (memoryWrite (memoryExtend memory (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat (out.extract 0 (min outputSize.toNat out.size)))
        g st ss out after ∧
      g ≤ gas ∧
      State.TransactionState.SameOutside [] state st ∧ st.parent = state.parent ∧
      ss.logs = substate.logs ∧
      (∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after
          within' = .ok s) ∧
      ss.accountsToDelete = substate.accountsToDelete ∧
      ss.refundCounter = substate.refundCounter ∧
      (flag ≠ 0 → ∃ (calleeCode : ByteArray) (route : Route) (caller : Evm fork Nat)
          (msg : Message fork) (child : Evm fork Nat),
        state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok calleeCode ∧
        Routes fork state calleeCode route ∧
        CallSends .staticcall message memory gas state substate asked to inputStart inputSize
          outputStart outputSize calleeCode route caller msg ∧
        Ran (processRunner fork bound) caller msg child ∧
        child.error = none ∧ child.output = out) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  rcases staticcall_route_outcome hberlin hglam hlt hbyte start within hrun with
    herr | ⟨g, st, ss, after, hat, hle, hso, hpar, hq, w, h⟩ |
    ⟨calleeCode, route, caller, msg, child, after, g, hcode, hroute, hsend, hran, -, hat, hle, w,
      h⟩
  · exact .inl herr
  · refine .inr ⟨0, .empty, g, st, ss, after, .inl rfl, ?_, hle, hso, hpar,
      congrArg Prod.fst hq, ⟨w, h⟩, congrArg (fun p => p.2.1) hq, congrArg (fun p => p.2.2) hq,
      fun hne => absurd rfl hne⟩
    rw [memoryWrite_empty_extract]
    exact hat
  · have hmsg := staticMessage_of_callSends hcode hroute hsend
    obtain ⟨so, par⟩ := static_ran hparis hran hmsg
    obtain ⟨i1, i2, i3⟩ := static_ran_incorporate hran hmsg
    obtain ⟨so0, par0, q0⟩ := callSends_state hsend
    refine .inr ⟨if child.error.isNone then 1 else 0, child.output, g,
      (incorporateChild fork caller child).state, (incorporateChild fork caller child).substate,
      after, ?_, hat, hle, ?_, ?_, i1.trans (congrArg Prod.fst q0), ⟨w, h⟩,
      i2.trans (congrArg (fun p => p.2.1) q0), i3.trans (congrArg (fun p => p.2.2) q0), ?_⟩
    · split
      · exact .inr rfl
      · exact .inl rfl
    · rw [state_incorporateChild]
      intro address hmem
      obtain ⟨x, y, z⟩ := so0 address hmem
      obtain ⟨x', y', z'⟩ := so address hmem
      exact ⟨x'.trans x, fun k => (y' k).trans (y k), fun k => (z' k).trans (z k)⟩
    · rw [state_incorporateChild]
      exact par.trans par0
    · intro hne
      refine ⟨calleeCode, route, caller, msg, child, hcode, hroute, hsend, hran, ?_, rfl⟩
      cases he : child.error with
      | none => rfl
      | some e =>
        rw [he] at hne
        exact absurd rfl hne

/-- The STATICCALL of `permit` to the owner, in plain terms. In the state `st`, with the
substate `ss` and `gc` gas left (the word that the GAS opcode pushed), the code called the
address `ow` and the call returned the flag 1 with the return data `out`:

- the state holds a code `calleeCode` at `ow`, and the call ran this code, or the code of its
  EIP-7702 delegate (`route`);
- the message `msg` that was sent: its sender is the token, its target is `ow`, its call data
  is `data`, no value, static, one level deeper, the same block and transaction; its gas is the
  gas of `messageCallGas` for `gc` asked and `gc` left (all but one 64th of what is left after
  the access cost); the 15 fields of the message are all given;
- the frame `caller` it was sent from has the state `st` with the reads of the call recorded,
  and the substate `ss` with `ow` (and the delegate) accessed;
- EthLib's real runner ran `msg` from `caller` to a frame `child` with no error, and `out` is
  the output of `child`.

So `out` is not free: it is what the code at `ow` returns for `data` in this state. -/
def OwnerCall (fork : Fork) (bound : Nat) (m : Message fork) (st : State.TransactionState)
    (ss : Substate) (gc : Nat) (ow : U256) (data out : ByteArray) : Prop :=
  ∃ (calleeCode : ByteArray) (route : Route) (caller : Evm fork Nat) (msg : Message fork)
      (child : Evm fork Nat),
    st.getCode (st.getAccount (toAddressMasked ow)).codeHash = .ok calleeCode ∧
    Routes fork st calleeCode route ∧
    caller.state = (routeState (st.recordAccountRead (toAddressMasked ow)) route).recordAccountRead
      m.currentTarget ∧
    caller.substate = routeSub { ss with
      accessedAddresses := ss.accessedAddresses.insert (toAddressMasked ow) } route ∧
    msg.gas = (messageCallGas fork 0 (BitVec.ofNat 256 gc).toNat gc 0
      (callBaseCost fork (decide (toAddressMasked ow ∉ ss.accessedAddresses)) +
        routeCost fork (ss.accessedAddresses.insert (toAddressMasked ow)) route)).subCall ∧
    msg.caller = m.currentTarget ∧
    msg.currentTarget = toAddressMasked ow ∧
    msg.target = some (toAddressMasked ow) ∧
    msg.codeAddress = some (routeAddr (toAddressMasked ow) route) ∧
    msg.code = routeCode calleeCode route ∧
    msg.data = data ∧
    msg.value = 0 ∧
    msg.isStatic = true ∧
    msg.depth = m.depth + 1 ∧
    msg.blockEnv = m.blockEnv ∧ msg.txEnv = m.txEnv ∧
    msg.reservoir = 0 ∧ msg.shouldTransferValue = true ∧
    msg.disablePrecompiles = route.isSome ∧
    Ran (processRunner fork bound) caller msg child ∧
    child.error = none ∧ child.output = out

/-- `OwnerCall` from the facts of `staticcall_sent`, for a call whose input is inside the memory
and whose output range is empty. -/
theorem ownerCall_of_sends {bound : Nat} {m : Message fork} {mem : ByteArray} {gc : Nat}
    {st : State.TransactionState} {ss : Substate} {ow i isz o : U256} {calleeCode : ByteArray}
    {route : Route} {caller : Evm fork Nat} {msg : Message fork} {child : Evm fork Nat}
    {data out : ByteArray}
    (hfit : i.toNat + isz.toNat ≤ mem.size)
    (hdata : memoryReadBytes mem i.toNat isz.toNat = data)
    (hcode : st.getCode (st.getAccount (toAddressMasked ow)).codeHash = .ok calleeCode)
    (hroute : Routes fork st calleeCode route)
    (hsend : CallSends .staticcall m mem gc st ss (BitVec.ofNat 256 gc) ow i isz o (0 : U256)
      calleeCode route caller msg)
    (hran : Ran (processRunner fork bound) caller msg child) (herr : child.error = none)
    (hout : child.output = out) :
    OwnerCall fork bound m st ss gc ow data out := by
  have e : extendMemory mem.size [(i, isz), (o, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_eq_zero _ _ fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inr (ceil32_le (ceil32_mod mem.size) (Nat.le_trans hfit (le_ceil32 mem.size)))
      · rw [List.mem_singleton.mp hp]
        exact .inl rfl
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hsend
  rw [e] at c3 c11
  rw [memoryExtend_zero] at c11
  exact ⟨calleeCode, route, caller, msg, child, hcode, hroute, c1, c2, c3,
    c5.trans (if_neg (by decide)), c6.trans (if_pos (.inr rfl)),
    c7.trans (congrArg some (if_pos (.inr rfl))), c8, c9, c11.trans hdata,
    c12.trans (if_neg (by decide)), by simpa using c15, c14, c16, c17, c4, c13.trans (by decide), c10,
    hran, herr, hout⟩

end SkyVerify

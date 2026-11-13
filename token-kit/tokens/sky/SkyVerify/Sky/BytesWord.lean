import SkyVerify.Sky.PermitBytes

/-!
# Words and memory growth for a signature of any length

Hand-written. The code of `permit(owner, spender, value, deadline, bytes signature)` for a
signature whose length is not 65 works at memory offsets that depend on the length. This file
holds what the proofs of that route need:

- `W n`: the word of a natural number, with the sums and differences that the code computes;
- the rounding of a length to whole words (`and (not 31) (len + 31)`), as a natural number;
- the growth of the memory for one word and for a copy, with the price as a difference of
  `memoryGasCost`;
- `bytes_copy_any`: the CALLDATACOPY of the signature and the jump to pc 2287, for any length,
  with exact gas (`copyCost`).
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Blocks SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

/-! ## Words of natural numbers -/

/-- The word of a natural number. -/
abbrev W (n : Nat) : U256 := BitVec.ofNat 256 n

theorem W_toNat {n : Nat} (h : n < 2 ^ 128) : (W n).toNat = n := by
  show (BitVec.ofNat 256 n).toNat = n
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (Nat.pow_lt_pow_right (by decide) (by decide)))

theorem W_self (x : U256) : W x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 256 x.toNat).toNat = x.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem W_add (a b : Nat) : add (W a) (W b) = W (a + b) := by
  show BitVec.ofNat 256 a + BitVec.ofNat 256 b = BitVec.ofNat 256 (a + b)
  exact (BitVec.ofNat_add a b).symm

theorem W_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 128) : sub (W a) (W b) = W (a - b) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 256 a - BitVec.ofNat 256 b).toNat = (BitVec.ofNat 256 (a - b)).toNat
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : b % 2 ^ 256 = b := Nat.mod_eq_of_lt (by omega)
  have h3 : (a - b) % 2 ^ 256 = a - b := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

/-- The mask that clears the low 5 bits: `not 31`. -/
abbrev NOT31 : U256 :=
  (115792089237316195423570985008687907853269984665640564039457584007913129639904 : U256)

/-- A sum with `not 31` is a difference with 32. -/
theorem W_add_not31 {a : Nat} (h : 32 ≤ a) (ha : a < 2 ^ 128) : add (W a) NOT31 = W (a - 32) := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 256 a + NOT31).toNat = (BitVec.ofNat 256 (a - 32)).toNat
  have hn : NOT31.toNat = 2 ^ 256 - 32 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hn]
  have h1 : a % 2 ^ 256 = a := Nat.mod_eq_of_lt (by omega)
  have h3 : (a - 32) % 2 ^ 256 = a - 32 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h3]
  omega

/-- The low 5 bits and the other bits of a word add up to the word. -/
theorem and31_add (x : U256) : (x &&& (31 : U256)) + (x &&& NOT31) = x := by
  have hn : NOT31 = ~~~(31 : U256) := by decide
  have hdis : (x &&& (31 : U256)) &&& (x &&& NOT31) = 0 := by
    rw [hn]
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases x[i] <;> cases (31 : U256)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdis, hn]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_or]
  cases x[i] <;> cases (31 : U256)[i] <;> rfl

/-- `and` with `not 31` rounds a number down to a multiple of 32. -/
theorem W_floor {n : Nat} (hn : n < 2 ^ 128) : bitwiseAnd (W n) NOT31 = W (n / 32 * 32) := by
  apply BitVec.eq_of_toNat_eq
  have hs := congrArg BitVec.toNat (and31_add (W n))
  have h31 : (W n &&& (31 : U256)).toNat = n % 32 := by
    rw [BitVec.toNat_and, W_toNat hn]
    exact Nat.and_two_pow_sub_one_eq_mod n 5
  have hle : (W n &&& NOT31).toNat ≤ n := by
    rw [BitVec.toNat_and, W_toNat hn]
    exact Nat.and_le_left
  rw [BitVec.toNat_add, h31, W_toNat hn] at hs
  have hlt : n % 32 + (W n &&& NOT31).toNat < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hs
  show (W n &&& NOT31).toNat = (W (n / 32 * 32)).toNat
  rw [W_toNat (by omega)]
  omega

theorem W_floor' {n : Nat} (hn : n < 2 ^ 128) : bitwiseAnd NOT31 (W n) = W (n / 32 * 32) := by
  rw [← W_floor hn]
  exact BitVec.and_comm _ _

/-! ## The growth of the memory -/

/-- The size of a memory after the write of a word, as a given number. -/
theorem sizeW {m : ByteArray} {sz n o : Nat} {v : U256} (s' : Nat) (hs : m.size = sz)
    (hfit : o + 32 ≤ sz + n) (he : sz + n = s') :
    (memoryWrite (memoryExtend m n) o (wordBytes v)).size = s' :=
  (size_rawW hs hfit).trans he

/-- `readWords_cons` with the offset of the next word as a given number. -/
theorem readWords_consA {m : ByteArray} {sz a a' k : Nat} {w : U256} {ws : List U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w)
    (hr : memoryReadBytes m a' k = memW ws) (ha : a' = a + 32) (hs : m.size = sz)
    (hfit : a + 32 + k ≤ sz) (hk : 0 < k) : memoryReadBytes m a (32 + k) = memW (w :: ws) := by
  subst ha
  exact readWords_cons h hr hs hfit hk

/-- `readTop_raw` with the offset after the first bytes as a given number. -/
theorem readTopA {m d : ByteArray} {sz a a' n k : Nat} {w : U256} (h : TopBytes m a n w)
    (hr : memoryReadBytes m a' k = d) (ha : a' = a + n) (hs : m.size = sz)
    (hfit : a + n + k ≤ sz) (hn : 0 < n) (hk : 0 < k) (hn32 : n ≤ 32) :
    memoryReadBytes m a (n + k) = topBytes n w d := by
  subst ha
  exact readTop_raw h hr hs hfit hn hk hn32

/-- A word inside the memory: no growth. -/
theorem ext0 {sz o : Nat} {start : U256} (ho : start.toNat = o) (h : o + 32 ≤ sz) :
    extendMemory sz [(start, (32 : U256))] = ⟨0, 0⟩ := by
  have h32 : (32 : U256).toNat = 32 := by decide
  exact extendMemory_of_le (by rw [ho, h32]; exact h)

/-- A word that ends past the memory: the memory grows by `n` bytes to `s'`, the end of the word
rounded up to 32. The price is the difference of the two memory prices. -/
theorem extN {sz s' n o : Nat} {start : U256} (ho : start.toNat = o) (hmod : sz % 32 = 0)
    (hs : s' = sz + n) (hn : 0 < n) (h1 : o + 32 ≤ s') (h2 : s' < o + 64) (h3 : s' % 32 = 0) :
    extendMemory sz [(start, (32 : U256))] = ⟨memoryGasCost s' - memoryGasCost sz, n⟩ := by
  have h32 : (32 : U256).toNat = 32 := by decide
  have e := extendMemory_of_lt (size := sz) (start := start) (length := (32 : U256)) hmod
    (by decide) (by rw [ho, h32]; omega)
  have hc : ceil32 (start.toNat + (32 : U256).toNat) = s' := by
    rw [ho, h32]
    unfold ceil32 WORD_BYTES
    split <;> omega
  rw [hc] at e
  rw [e]
  congr 1
  omega

/-- A range of `k` bytes that starts at the end of the memory: the memory grows by `k` rounded
up to 32 (`n`). -/
theorem extAppend {sz k n : Nat} {start size : U256} (ho : start.toNat = sz)
    (hk : size.toNat = k) (hmod : sz % 32 = 0) (hn : n % 32 = 0) (h1 : k ≤ n) (h2 : n < k + 32) :
    extendMemory sz [(start, size)] = ⟨memoryGasCost (sz + n) - memoryGasCost sz, n⟩ := by
  by_cases h0 : k = 0
  · have hz : size = 0 := BitVec.eq_of_toNat_eq (by rw [hk, h0]; rfl)
    have n0 : n = 0 := by omega
    rw [hz, extendMemory_of_length_eq_zero, n0, Nat.add_zero, Nat.sub_self]
  · have hz : size ≠ 0 := fun e => h0 (by rw [← hk, e]; rfl)
    have e := extendMemory_of_lt (size := sz) (start := start) (length := size) hmod hz
      (by rw [ho, hk]; omega)
    have hc : ceil32 (start.toNat + size.toNat) = sz + n := by
      rw [ho, hk]
      unfold ceil32 WORD_BYTES
      split <;> omega
    rw [hc] at e
    rw [e]
    congr 1
    omega

/-! ## The length of the signature -/

/-- The facts on the length `L` of the signature and on `c`, the length rounded up to 32, that
the proofs of the route use. -/
structure LenC (L c : Nat) : Prop where
  small : L < 2 ^ 64
  mod : c % 32 = 0
  le : L ≤ c
  lt : c < L + 32

/-- The length rounded up to 32. -/
abbrev ceilLen (L : Nat) : Nat := (L + 31) / 32 * 32

theorem lenC_ceil {L : Nat} (h : L < 2 ^ 64) : LenC L (ceilLen L) :=
  ⟨h, by unfold ceilLen; omega, by unfold ceilLen; omega, by unfold ceilLen; omega⟩

/-- The check of the decoder on the length word bounds the length. -/
theorem len_small {len : U256}
    (h : isZero (greaterThan len (18446744073709551615 : U256)) ≠ 0) : len.toNat < 2 ^ 64 := by
  unfold isZero greaterThan at h
  have h64 : (18446744073709551615 : U256).toNat = 2 ^ 64 - 1 := by decide
  rw [h64] at h
  by_cases hc : len.toNat > 2 ^ 64 - 1
  · rw [if_pos hc] at h
    exact absurd rfl h
  · omega

/-- The free memory pointer after the allocation of the signature: 160 and the rounded length. -/
theorem sigFree_W {L c : Nat} (h : LenC L c) : sigFree (W L) = W (c + 160) := by
  obtain ⟨hs, hm, hle, hlt⟩ := h
  show add (128 : U256) (bitwiseAnd (add (63 : U256) (bitwiseAnd NOT31 (add (W L) (31 : U256))))
    NOT31) = W (c + 160)
  rw [show add (W L) (31 : U256) = W (L + 31) from W_add L 31, W_floor' (by omega),
    show add (63 : U256) (W ((L + 31) / 32 * 32)) = W (63 + (L + 31) / 32 * 32) from W_add 63 _,
    W_floor (by omega),
    show add (128 : U256) (W ((63 + (L + 31) / 32 * 32) / 32 * 32)) =
      W (128 + (63 + (L + 31) / 32 * 32) / 32 * 32) from W_add 128 _]
  congr 1
  omega

/-- The rounding of the length that the encoder computes. -/
theorem ceil_W {L c : Nat} (h : LenC L c) :
    bitwiseAnd NOT31 (add (31 : U256) (W L)) = W c := by
  obtain ⟨hs, hm, hle, hlt⟩ := h
  rw [show add (31 : U256) (W L) = W (31 + L) from W_add 31 L, W_floor' (by omega)]
  congr 1
  omega

/-! ## The copy of the signature to memory, for any length -/

/-- The memory at pc 2287 for a signature of `L` bytes read from `f` of the call data: the free
memory pointer `nf`, the length at 128, the bytes from 160, and a zero word after them. `c` is
the length rounded up to 32. -/
abbrev bytesMemAny (data : ByteArray) (f L c : Nat) (nf : U256) : ByteArray :=
  memoryWrite (memoryExtend
    (memoryWrite (memoryExtend
      (memW [(0 : U256), (0 : U256), nf, (0 : U256), W L]) c) 160
      (copied data f L)) 32) (L + 160) (wordBytes (0 : U256))

/-- What the code after pc 2287 uses of the memory `M` with a signature of `L` bytes that the
call data holds from `f`: the size, the free memory pointer, the zero word at 96, the length at
128, the bytes of the signature from 160, and zero bytes after them up to the rounded length. -/
structure SigMem (M data : ByteArray) (f L c : Nat) : Prop where
  size : M.size = c + 192
  fp : loadWord (memoryReadBytes M 64 32) 0 32 = W (c + 160)
  w96 : loadWord (memoryReadBytes M 96 32) 0 32 = (0 : U256)
  w128 : loadWord (memoryReadBytes M 128 32) 0 32 = W L
  sig : ∀ j, j < L → byteAt M (160 + j) = byteAt data (f + j)
  pad : ∀ j, L ≤ j → j < c → byteAt M (160 + j) = 0

theorem bytesMemAny_sigMem (data : ByteArray) (f : Nat) {L c : Nat} (h : LenC L c) :
    SigMem (bytesMemAny data f L c (W (c + 160))) data f L c := by
  obtain ⟨hs, hm, hle, hlt⟩ := h
  have s0 := size_memW5 (0 : U256) (0 : U256) (W (c + 160)) (0 : U256) (W L)
  have s1 := size_rawC (data := data) (f := f) (k := L) (n := c) (o := 160) s0 (by omega)
  have fit : L + 160 + 32 ≤ 160 + c + 32 := by omega
  have word : ∀ {i a : Nat} {w : U256}, a = 32 * i → decide (i < 5) = true →
      wordAt [(0 : U256), (0 : U256), W (c + 160), (0 : U256), W L] i = w →
      loadWord (memoryReadBytes (bytesMemAny data f L c (W (c + 160))) a 32) 0 32 = w := by
    intro i a w ha hi hv
    have hi' : i < 5 := of_decide_eq_true hi
    exact load_rawW (load_rawC (memW_load i ha hi hv) s0 (by omega) (by omega) (.inl (by omega)))
      s1 fit (by omega) (.inl (by omega))
  refine ⟨(size_rawW s1 fit).trans (by omega), word (i := 2) rfl rfl rfl,
    word (i := 3) rfl rfl rfl, word (i := 4) rfl rfl rfl, fun j hj => ?_, fun j h1 h2 => ?_⟩
  · rw [byteAt_rawW_miss s1 fit (.inl (by omega)),
      byteAt_memoryWrite (by rw [size_memoryExtend, size_copied_data, s0]; omega),
      if_pos ⟨by omega, by rw [size_copied_data]; omega⟩, byteAt_copied, if_pos (by omega)]
    congr 1
    omega
  · rw [byteAt_rawW_hit s1 fit (by omega) (by omega), byteAt_wordBytes_zero]

/-- The gas from the CALLDATACOPY of the signature to pc 2287: 84 for the opcodes, 3 for each
word copied, and the growth of the memory from 160 bytes to `c + 192`. For 65 bytes it is 105. -/
def copyCost (c : Nat) : Nat :=
  84 + 3 * (c / 32) + (memoryGasCost (c + 192) - memoryGasCost 160)

/-- The CALLDATACOPY of the bytes of the signature, the zero word after them, the return of the
decoder to pc 761 and the jump to pc 2287, for a signature of any length `L`. -/
theorem bytes_copy_any {p deadline value spender owner size sel nf : U256} {gas L c : Nat}
    {state : State.TransactionState} {substate : Substate} (h : LenC L c)
    (hg : copyCost c ≤ gas) :
    Logic.HoareG fork (At CODE message 4293 [(160 : U256), add p (32 : U256), W L,
        (128 : U256), nf, W L, (18446744073709551615 : U256), p, (0 : U256), deadline,
        value, spender, owner, (4 : U256), size, (761 : U256), (558 : U256), sel]
        (memW [(0 : U256), (0 : U256), nf, (0 : U256), W L]) gas state substate)
      (At CODE message 2287 [(128 : U256), deadline, value, spender, owner, (558 : U256), sel]
        (bytesMemAny message.data (add p (32 : U256)).toNat L c nf) (gas - copyCost c) state
        substate) := by
  obtain ⟨hs, hm, hle, hlt⟩ := h
  unfold copyCost at hg ⊢
  have m1 := memoryGasCost_mono (show 160 ≤ 160 + c by omega)
  have m2 := memoryGasCost_mono (show 160 + c ≤ c + 192 by omega)
  have s0 := size_memW5 (0 : U256) (0 : U256) nf (0 : U256) (W L)
  have hL : (W L).toNat = L := W_toNat (by omega)
  have hw : wordCount L = c / 32 := by
    unfold wordCount ceil32 WORD_BYTES
    split <;> omega
  step calldatacopyK (by code_fact) (by code_fact) s0 (n := c) (extAppend (by decide +kernel) hL (by decide) hm hle hlt) (o := 160) (by decide +kernel) (f := (add p (32 : U256)).toNat) rfl (k := L) hL (w := c / 32) hw rfl (by omega)
  step pushR 1 (0 : U256)
  at_pc 4296
  step pushR 1 (32 : U256)
  at_pc 4298
  step dupR 4
  step dupR 3
  step binR 0x01 instruction_add
  step binR 0x01 instruction_add
  step foldK (y := W (L + 160)) (by
    rw [show add (128 : U256) (W L) = W (128 + L) from W_add 128 L,
      show add (W (128 + L)) (32 : U256) = W (128 + L + 32) from W_add _ 32]
    congr 1
    omega)
  step mstoreK (by code_fact) (by code_fact) (size_rawC s0 (by omega)) (n := 32) (extN (s' := c + 192) (W_toNat (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (o := L + 160) (W_toNat (by omega)) rfl (by gas_ok)
  step dupR 0
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step swap3K (by code_fact) (by code_fact) (by gas_ok)
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step swap3K (by code_fact) (by code_fact) (by gas_ok)
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step swap4K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step jumpR
  at_pc 761
  step jumpdestR
  step pushR 2 (2287 : U256)
  at_pc 765
  step jumpR
  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)

end SkyVerify

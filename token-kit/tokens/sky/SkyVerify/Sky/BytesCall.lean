import SkyVerify.Sky.BytesGen
import SkyVerify.Sky.BytesLoop
import SkyVerify.Sky.PermitBytes1271

/-!
# SKY: `permit` with a signature as bytes of any length: the call to the owner (ERC-1271)

Hand-written, over the symbolic segments of Sky/BytesGen.lean (made by `scripts/symgen.py`) and
the copy routine of Sky/BytesLoop.lean. For a signature whose length word is not 65 the code
skips ECRECOVER and asks the owner contract. This file proves that part from the EXTCODESIZE of
the owner (pc 3580) to the end, for a signature of any length `L` (`c` is `L` rounded up to 32):

- `erc1271Bytes`: the call data of `isValidSignature(bytes32,bytes)` for a digest and the bytes
  of a signature of any length;
- `EncMem`: what the code uses of the memory at pc 3580 (`F` is the free memory pointer);
- `encMem`, `enc_chain`: the memory after the code built the call data, with the fact that the
  bytes it sends are `erc1271Bytes` of the digest and of the bytes of the signature;
- `encoder`: the code from pc 3586 to the GAS before the STATICCALL (pc 3681), exact gas
  `encCost F c`;
- `PermitByContractAny`, `permit_contract_any`: from pc 3580 to the end, in the strong form
  (`OwnerCall`: the target, the call data, the gas, the static flag, and the answer of the run
  of the code of the owner is the magic value).
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

/-! ## Words and bytes of a memory -/

/-- The word of the memory `M` at `a`. -/
abbrev mw (M : ByteArray) (a : Nat) : U256 := loadWord (memoryReadBytes M a 32) 0 32

/-- Two memories with the same 32 bytes at `a` hold the same word there. -/
theorem mw_congr {M M' : ByteArray} {a : Nat} (h : a + 32 ≤ M.size) (h' : a + 32 ≤ M'.size)
    (hb : ∀ j, j < 32 → byteAt M' (a + j) = byteAt M (a + j)) : mw M' a = mw M a := by
  have e : memoryReadBytes M' a 32 = memoryReadBytes M a 32 :=
    read_eq_of_bytes h' (size_memoryReadBytes h) (fun j hj => by
      rw [byteAt_memoryReadBytes h, if_pos hj]
      exact hb j hj)
  show loadWord (memoryReadBytes M' a 32) 0 32 = loadWord (memoryReadBytes M a 32) 0 32
  rw [e]

/-- A byte of a known word of the memory. -/
theorem mw_byte {M : ByteArray} {a j : Nat} {w : U256} (h : a + 32 ≤ M.size) (hw : mw M a = w)
    (hj : j < 32) : byteAt M (a + j) = byteAt (wordBytes w) j := by
  rw [← hw]
  exact (byteAt_wordOf h hj).symm

/-! ## The call data of `isValidSignature(bytes32,bytes)`, for any length -/

/-- The call data that `permit` sends to the owner for the digest `dg` and the signature `sig`
(any number of bytes): the selector `0x1626ba7e` of `isValidSignature(bytes32,bytes)`, the
digest, the offset 64 of the bytes, their length, the bytes, and zero bytes up to a multiple
of 32. -/
def erc1271Bytes (dg : U256) (sig : ByteArray) : ByteArray :=
  (wordBytes MAGIC_1271).extract 0 4 ++ (wordBytes dg ++ (wordBytes (64 : U256) ++
    (wordBytes (BitVec.ofNat 256 sig.size) ++
      (sig ++ ByteArray.mk (Array.replicate (ceilLen sig.size - sig.size) 0)))))

theorem size_zeros (n : Nat) : (ByteArray.mk (Array.replicate n (0 : UInt8))).size = n := by
  show (Array.replicate n (0 : UInt8)).size = n
  exact Array.size_replicate

theorem size_sel4 : ((wordBytes MAGIC_1271).extract 0 4).size = 4 := by
  rw [ByteArray.size_extract, size_wordBytes]
  rfl

/-- The size of the call data: 100 bytes and the length rounded up to 32. -/
theorem size_erc1271Bytes (dg : U256) (sig : ByteArray) :
    (erc1271Bytes dg sig).size = 100 + ceilLen sig.size := by
  unfold erc1271Bytes
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_append, ByteArray.size_append, size_sel4, size_wordBytes, size_wordBytes,
    size_wordBytes, size_zeros]
  unfold ceilLen
  omega

/-- The bytes of the call data, part by part. -/
theorem byteAt_erc1271Bytes (dg : U256) (sig : ByteArray) (j : Nat) :
    byteAt (erc1271Bytes dg sig) j =
      if j < 4 then byteAt (wordBytes MAGIC_1271) j
      else if j < 36 then byteAt (wordBytes dg) (j - 4)
      else if j < 68 then byteAt (wordBytes (64 : U256)) (j - 36)
      else if j < 100 then byteAt (wordBytes (BitVec.ofNat 256 sig.size)) (j - 68)
      else byteAt sig (j - 100) := by
  unfold erc1271Bytes
  rw [EthLib.Base.byteAt_append, size_sel4, EthLib.Base.byteAt_append, size_wordBytes,
    EthLib.Base.byteAt_append, size_wordBytes, EthLib.Base.byteAt_append, size_wordBytes,
    EthLib.Base.byteAt_append_zeros, EthLib.Base.byteAt_extract, size_wordBytes]
  by_cases h1 : j < 4
  · rw [if_pos h1, if_pos h1, if_pos (by omega), Nat.zero_add]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j < 36
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]
      by_cases h3 : j < 68
      · rw [if_pos (by omega), if_pos h3, show j - 4 - 32 = j - 36 from by omega]
      · rw [if_neg (by omega), if_neg h3]
        by_cases h4 : j < 100
        · rw [if_pos (by omega), if_pos h4, show j - 4 - 32 - 32 = j - 68 from by omega]
        · rw [if_neg (by omega), if_neg h4, show j - 4 - 32 - 32 - 32 = j - 100 from by omega]

/-! ## The memory at the EXTCODESIZE of the owner -/

/-- What the code from pc 3580 uses of the memory `M`, for a signature of `L` bytes that the
decoder copied from the call data `data` at `f`: `F` is the free memory pointer (2 modulo 32,
past the signature), the memory ends 30 bytes after it, the word at 96 is zero, the word at 128
is the length and the bytes of the signature are at 160. -/
structure EncMem (M data : ByteArray) (f F L c : Nat) : Prop where
  size : M.size = F + 30
  fp : mw M 64 = W F
  w96 : mw M 96 = (0 : U256)
  w128 : mw M 128 = W L
  sig : ∀ j, j < L → byteAt M (160 + j) = byteAt data (f + j)
  hF : F % 32 = 2
  hFc : c + 482 ≤ F
  hFb : F < 2 ^ 99

/-- The size of the memory after the first run of the copy routine. -/
abbrev encS2 (F L : Nat) : Nat := (F + 132 + L + 63) / 32 * 32

/-- The memory at the GAS before the STATICCALL to the owner (pc 3681): the segments `sbE1`,
`sbE2`, `sbE3` around the two runs of the copy routine. -/
def encMem (M : ByteArray) (F L c : Nat) (dg nonce deadline value spender owner sel : U256) :
    ByteArray :=
  sbE3_M (copyMem (F + 32) (F + c + 132) (c + 100)
    (sbE2_M (copyMem 160 (F + 132) L (sbE1_M M F L dg nonce deadline value spender owner sel))
      F L c (encS2 F L) dg nonce deadline value spender owner sel))
    F c (F + 2 * c + 286) dg nonce deadline value spender owner sel

/-- The memories of the encoder, one after the other, and what each holds. The last fact: the
`c + 100` bytes at `F + c + 132`, the input of the STATICCALL, are `erc1271Bytes` of the digest
and of the `L` bytes of the signature. -/
theorem enc_chain {M data : ByteArray} {f F L c : Nat} (hL : LenC L c)
    (em : EncMem M data f F L c) (dg nonce deadline value spender owner sel : U256) :
    ∃ M1 M2 M3 M4 M5 : ByteArray,
      sbE1_M M F L dg nonce deadline value spender owner sel = M1 ∧
      copyMem 160 (F + 132) L M1 = M2 ∧
      sbE2_M M2 F L c (encS2 F L) dg nonce deadline value spender owner sel = M3 ∧
      copyMem (F + 32) (F + c + 132) (c + 100) M3 = M4 ∧
      sbE3_M M4 F c (F + 2 * c + 286) dg nonce deadline value spender owner sel = M5 ∧
      encMem M F L c dg nonce deadline value spender owner sel = M5 ∧
      M1.size = F + 158 ∧
      M2.size = encS2 F L ∧ mw M2 64 = W F ∧ mw M2 96 = (0 : U256) ∧
      M3.size = encS2 F L ∧
      M4.size = F + 2 * c + 286 ∧ mw M4 64 = W (F + c + 132) ∧
      M5.size = F + 2 * c + 286 ∧ mw M5 64 = W (F + c + 132) ∧ mw M5 96 = (0 : U256) ∧
      memoryReadBytes M5 (F + c + 132) (c + 100) = erc1271Bytes dg (copied data f L) := by
  have hFm := em.hF
  have hFc := em.hFc
  have hFb9 := em.hFb
  have hFb : F < 2 ^ 100 := by omega
  have hS : encS2 F L = (F + 132 + L + 63) / 32 * 32 := rfl
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  have hMs := em.size
  -- the start of the call data
  obtain ⟨M1, e1⟩ : ∃ M1, sbE1_M M F L dg nonce deadline value spender owner sel = M1 := ⟨_, rfl⟩
  have k1 := sbE1_mem (rest := []) (dg := dg) (nonce := nonce) (deadline := deadline)
    (value := value) (spender := spender) (owner := owner) (sel := sel) hFm (by omega) hFb hLs
    hMs em.fp em.w128
  rw [e1] at k1
  obtain ⟨s1, a64, -, a36, a68, a100, fr1⟩ := k1
  have a96 : mw M1 96 = (0 : U256) :=
    (mw_congr (M := M) (by omega) (by omega)
      (fun j hj => fr1 (96 + j) (by omega) (by omega))).trans em.w96
  -- the copy of the signature
  obtain ⟨M2, e2⟩ : ∃ M2, copyMem 160 (F + 132) L M1 = M2 := ⟨_, rfl⟩
  have k2 := copyMem_spec (S := 160) (D := F + 132) (N := L) (M := M1) (by omega) (by omega)
    (by omega) (by omega)
  rw [e2, s1] at k2
  obtain ⟨s2, lo2, cp2, z2⟩ := k2
  have s2' : M2.size = encS2 F L := by
    rw [s2]
    exact Nat.max_eq_right (by omega)
  have b64 : mw M2 64 = W F :=
    (mw_congr (M := M1) (by omega) (by omega) (fun j hj => lo2 (64 + j) (by omega))).trans a64
  have b96 : mw M2 96 = (0 : U256) :=
    (mw_congr (M := M1) (by omega) (by omega) (fun j hj => lo2 (96 + j) (by omega))).trans a96
  -- the length, the free memory pointer and the selector
  obtain ⟨M3, e3⟩ :
      ∃ M3, sbE2_M M2 F L c (encS2 F L) dg nonce deadline value spender owner sel = M3 :=
    ⟨_, rfl⟩
  have k3 := sbE2_mem (rest := []) (dg := dg) (nonce := nonce) (deadline := deadline)
    (value := value) (spender := spender) (owner := owner) (sel := sel) (c := c)
    (s := encS2 F L) hFm (by omega) hFb hLs hLm hLle hLlt (by omega) (by omega) (by omega)
    s2' b64 b96
  rw [e3] at k3
  obtain ⟨s3, c96, -, c64, csel, fr3⟩ := k3
  obtain ⟨S2, s2s, hS2a⟩ : ∃ S2, M2.size = S2 ∧ F + 158 ≤ S2 := ⟨_, s2', by omega⟩
  have tws : (memoryWrite (memoryExtend (memoryWrite (memoryExtend M2 0) F
      (wordBytes (W (c + 100)))) 0) 64 (wordBytes (W (F + c + 132)))).size =
      S2 + 0 + 0 := size_rawW (size_rawW s2s (by omega)) (by omega)
  have tw : ∀ i, F + 32 ≤ i → byteAt (memoryWrite (memoryExtend (memoryWrite (memoryExtend M2 0)
      F (wordBytes (W (c + 100)))) 0) 64 (wordBytes (W (F + c + 132)))) i = byteAt M2 i :=
    fun i hi => by
      rw [byteAt_rawW_miss (size_rawW s2s (by omega)) (by omega) (.inr (by omega)),
        byteAt_rawW_miss s2s (by omega) (.inr hi)]
  have m3lo : ∀ j, j < 4 → byteAt M3 (F + 32 + j) = byteAt (wordBytes MAGIC_1271) j :=
    fun j hj => (mw_byte (by omega) csel (by omega)).trans (magicOr_lo _ hj)
  have m3hi : ∀ j, 4 ≤ j → j < c + 100 → byteAt M3 (F + 32 + j) = byteAt M2 (F + 32 + j) := by
    intro j h4 hj
    by_cases h32 : j < 32
    · rw [mw_byte (by omega) csel h32, magicOr_hi _ h4, byteAt_wordOf (by omega) h32]
      exact tw _ (by omega)
    · exact fr3 _ (by omega) (by omega)
  -- the copy of the call data
  obtain ⟨M4, e4⟩ : ∃ M4, copyMem (F + 32) (F + c + 132) (c + 100) M3 = M4 := ⟨_, rfl⟩
  have k4 := copyMem_spec (S := F + 32) (D := F + c + 132) (N := c + 100) (M := M3) (by omega)
    (by omega) (by omega) (by omega)
  rw [e4, s3] at k4
  obtain ⟨s4, lo4, cp4, -⟩ := k4
  have s4' : M4.size = F + 2 * c + 286 := by
    rw [s4, Nat.max_eq_right (by omega)]
    omega
  have d64 : mw M4 64 = W (F + c + 132) :=
    (mw_congr (M := M3) (by omega) (by omega) (fun j hj => lo4 (64 + j) (by omega))).trans c64
  have d96 : mw M4 96 = (0 : U256) :=
    (mw_congr (M := M3) (by omega) (by omega) (fun j hj => lo4 (96 + j) (by omega))).trans c96
  -- the arguments of the call
  obtain ⟨M5, e5⟩ :
      ∃ M5, sbE3_M M4 F c (F + 2 * c + 286) dg nonce deadline value spender owner sel = M5 :=
    ⟨_, rfl⟩
  have k5 := sbE3_mem (rest := []) (dg := dg) (nonce := nonce) (deadline := deadline)
    (value := value) (spender := spender) (owner := owner) (sel := sel) (c := c)
    (s := F + 2 * c + 286) hFm (by omega) hFb hLm (by omega) (by omega) (by omega) (by omega)
    s4' d64
  rw [e5] at k5
  obtain ⟨s5, f64, fr5⟩ := k5
  have f96 : mw M5 96 = (0 : U256) :=
    (mw_congr (M := M4) (by omega) (by omega)
      (fun j hj => fr5 (96 + j) (by omega) (by omega))).trans d96
  have hdata : memoryReadBytes M5 (F + c + 132) (c + 100) = erc1271Bytes dg (copied data f L) := by
    apply read_eq_of_bytes (by omega)
      (by rw [size_erc1271Bytes, size_copied_data]; unfold ceilLen; omega)
    intro j hj
    rw [fr5 _ (by omega) (by omega), cp4 j hj, byteAt_erc1271Bytes, size_copied_data]
    by_cases h4 : j < 4
    · rw [if_pos h4]
      exact m3lo j h4
    rw [if_neg h4, m3hi j (by omega) hj]
    by_cases h36 : j < 36
    · rw [if_pos h36, lo2 _ (by omega), show F + 32 + j = F + 36 + (j - 4) from by omega]
      exact mw_byte (by omega) a36 (by omega)
    rw [if_neg h36]
    by_cases h68 : j < 68
    · rw [if_pos h68, lo2 _ (by omega), show F + 32 + j = F + 68 + (j - 36) from by omega]
      exact mw_byte (by omega) a68 (by omega)
    rw [if_neg h68]
    by_cases h100 : j < 100
    · rw [if_pos h100, lo2 _ (by omega), show F + 32 + j = F + 100 + (j - 68) from by omega]
      exact mw_byte (by omega) a100 (by omega)
    rw [if_neg h100, show F + 32 + j = F + 132 + (j - 100) from by omega, byteAt_copied]
    by_cases hin : j - 100 < L
    · rw [if_pos hin, cp2 _ hin, fr1 _ (by omega) (by omega)]
      exact em.sig _ hin
    · rw [if_neg hin]
      exact z2 _ (by omega) (by omega)
  refine ⟨M1, M2, M3, M4, M5, e1, e2, e3, e4, e5, ?_, s1, s2', b64, b96, s3, s4', d64, s5, f64,
    f96, hdata⟩
  unfold encMem
  rw [e1, e2, e3, e4, e5]

/-! ## The encoder, with exact gas -/

/-- The gas of the code from pc 3586 to the GAS before the STATICCALL (pc 3681): 841 for the
opcodes outside the two loops, 67 for each word copied (the words of the signature, then those
and 4 more), and the growth of the memory from `F + 30` to `F + 2 * c + 286` bytes. -/
def encCost (F c : Nat) : Nat :=
  841 + 134 * (c / 32) + (memoryGasCost (F + 2 * c + 286) - memoryGasCost (F + 30))

/-- The code that builds the call data of `isValidSignature`, from pc 3586 to the GAS before the
STATICCALL to the owner (pc 3681), for a signature of any length. -/
theorem encoder (hfork : .berlin ≤ fork) {M data : ByteArray} {f F L c : Nat} (hL : LenC L c)
    (em : EncMem M data f F L c) {dg nonce deadline value spender owner sel : U256} {gas : Nat}
    {state : State.TransactionState} {substate : Substate} (hg : encCost F c ≤ gas) :
    Logic.HoareG fork
      (At CODE message 3586 [(0 : U256), (128 : U256), dg, owner, (2739 : U256), dg, nonce,
        (128 : U256), deadline, value, spender, owner, (558 : U256), sel] M gas state substate)
      (At CODE message 3681 [bitwiseAnd ADDR_MASK owner, W (F + c + 132), W (c + 100),
        W (F + c + 132), (0 : U256), W (F + 2 * c + 232), bitwiseAnd ADDR_MASK owner, (0 : U256),
        (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256), dg, nonce, (128 : U256),
        deadline, value, spender, owner, (558 : U256), sel]
        (encMem M F L c dg nonce deadline value spender owner sel) (gas - encCost F c) state
        substate) := by
  have hFm := em.hF
  have hFc := em.hFc
  have hFb9 := em.hFb
  have hFb : F < 2 ^ 100 := by omega
  have hS : encS2 F L = (F + 132 + L + 63) / 32 * 32 := rfl
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  obtain ⟨M1, M2, M3, M4, M5, e1, e2, e3, e4, e5, e6, s1, s2, b64, b96, s3, s4, d64, -, -, -,
    -⟩ := enc_chain hL em dg nonce deadline value spender owner sel
  have g1 := memoryGasCost_mono (show F + 30 ≤ F + 158 by omega)
  have g2 := memoryGasCost_mono (show F + 158 ≤ encS2 F L by omega)
  have g3 := memoryGasCost_mono (show encS2 F L ≤ F + 2 * c + 286 by omega)
  have c2 : copyGas 160 (F + 132) L M1 =
      47 + 67 * (c / 32) + (memoryGasCost (encS2 F L) - memoryGasCost (F + 158)) := by
    unfold copyGas
    rw [e2, s2, s1]
    omega
  have c4 : copyGas (F + 32) (F + c + 132) (c + 100) M3 =
      47 + 67 * (c / 32 + 4) + (memoryGasCost (F + 2 * c + 286) - memoryGasCost (encS2 F L)) := by
    unfold copyGas
    rw [e4, s4, s3]
    omega
  unfold encCost at hg ⊢
  rw [e6, ← e5]
  refine Logic.Triple.seq (sbE1 (rest := []) hfork hFm (by omega) hFb hLs em.size em.fp em.w128
    (by simp) (by omega)) ?_
  rw [e1]
  refine Logic.Triple.seq (copy_routine (S := 160) (D := F + 132) (N := L) (M := M1) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
    (by rw [c2]; omega)) ?_
  rw [e2, c2]
  refine Logic.Triple.seq (sbE2 (rest := []) (c := c) (s := encS2 F L) hfork hFm (by omega) hFb
    hLs hLm hLle hLlt (by omega) (by omega) (by omega) s2 b64 b96 (by simp) (by omega)) ?_
  rw [e3]
  refine Logic.Triple.seq (copy_routine (S := F + 32) (D := F + c + 132) (N := c + 100) (M := M3)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
    (by rw [c4]; omega)) ?_
  rw [e4, c4]
  refine Logic.Triple.seq (sbE3 (rest := []) (c := c) (s := F + 2 * c + 286) hfork hFm (by omega)
    hFb hLm (by omega) (by omega) (by omega) (by omega) s4 d64 (by simp) (by omega)) ?_
  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)

/-! ## From the EXTCODESIZE of the owner to the end -/

/-- The ERC-1271 path of `permit` for a signature `sig` of any length, from the state `st0`, the
substate `ss0` and the gas `g0` at the EXTCODESIZE of the owner, under the real runner with the
gas bound `bound`.

The state gives the code `c` of the owner and it is not empty. The gas paid the access of the
owner and `k` more (the opcodes up to the GAS before the call and the growth of the memory).
Then the code made the STATICCALL that `OwnerCall` describes: to the owner address, with the call
data `erc1271Bytes dg sig` (`isValidSignature(digest, signature)` for the digest `dg` and the
bytes `sig` as given), in the state at the EXTCODESIZE with the read of the owner recorded and
the owner accessed, with `g0 - (the access cost + k) - 2` gas left at the STATICCALL. The return
data `out` is the output of the run of that message, which ended with no error; its size as a
word is 32 and its first word is the magic value.

The call kept every account, every storage word and every transient storage word
(`SameOutside []`), the logs, the accounts to delete and the refund counter. Then the code ended
as `PermitWrites` says from the state `st` and the substate `ss` after the call and a gas `g` at
most the gas left at the STATICCALL (an inequality: the gas that the code of the owner used is
not known). -/
def PermitByContractAny (fork : Fork) (bound : Nat) (m : Message fork)
    (st0 : State.TransactionState) (ss0 : Substate) (g0 : Nat) (s : Evm fork Nat) (k : Nat)
    (dg : U256) (sig : ByteArray) (owner spender value : U256) : Prop :=
  ∃ (c out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
    st0.getCode (st0.getAccount (toAddressMasked (bitwiseAnd owner ADDR_MASK))).codeHash =
      .ok c ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    externalBaseCost fork
      (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉ ss0.accessedAddresses)) + k ≤ g0 ∧
    OwnerCall fork bound m
      (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK)))
      { ss0 with accessedAddresses :=
        ss0.accessedAddresses.insert (toAddressMasked (bitwiseAnd owner ADDR_MASK)) }
      (g0 - (externalBaseCost fork
        (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉ ss0.accessedAddresses)) + k) - 2)
      (bitwiseAnd owner ADDR_MASK) (erc1271Bytes dg sig) out ∧
    BitVec.ofNat 256 out.size = 32 ∧
    loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
    State.TransactionState.SameOutside []
      (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))) st ∧
    st.parent = (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))).parent ∧
    ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
    ss.refundCounter = ss0.refundCounter ∧
    g ≤ g0 - (externalBaseCost fork
      (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉ ss0.accessedAddresses)) + k) - 2 ∧
    PermitWrites fork m st ss g 2324 s owner spender value

/-- `PermitByContractAny` gives the statement without the call (`PermitKept`), which the
invariant and the readable forms use. -/
theorem PermitByContractAny.kept {bound : Nat} {st0 : State.TransactionState} {ss0 : Substate}
    {g0 k : Nat} {s : Evm fork Nat} {dg owner spender value : U256} {sig : ByteArray}
    (h : PermitByContractAny fork bound message st0 ss0 g0 s k dg sig owner spender value) :
    ∃ g1, PermitKept fork message st0 ss0 g1 s owner spender value := by
  obtain ⟨c, out, st, ss, g, h1, h2, -, -, h3, h4, h5, h6, h7, h8, h9, -, h11⟩ := h
  exact ⟨g + 23 + 1290, c, out, st, ss, g + 23, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    Nat.le_refl _, permitWrites_shift (c := 2324) (by omega) h11⟩

theorem sub3 (a b c d : Nat) : a - b - c - d = a - (b + (c + d)) := by omega

theorem end_gas {g w sg : Nat} (h7 : 316 ≤ g) (h8 : 2007 + w ≤ g - 316)
    (h9 : 1 ≤ g - 316 - (2007 + w)) (hs : sg = g - 316 - (2007 + w) - 1) :
    2324 + w ≤ g ∧ sg = g - (2324 + w) := by omega

/-- From the EXTCODESIZE of the owner (pc 3580) to the end, for a signature of any length `L`:
a run that ends with no error is as `PermitByContractAny` says. The gas between the access of
the owner and the GAS before the STATICCALL is `16 + encCost F c`. -/
theorem permit_contract_any (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {z s : Evm fork Nat}
    {dg owner nonce deadline value spender sel : U256} {M data : ByteArray} {f F L c : Nat}
    (hL : LenC L c) (em : EncMem M data f F L c)
    (hz : At CODE message 3580
      [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] M gas state
        substate z)
    (hend : EndsL (processRunner fork bound) z s) (hok : s.error = none) :
    PermitByContractAny fork bound message state substate gas s (16 + encCost F c) dg
      (copied data f L) owner spender value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hFm := em.hF
  have hFc := em.hFc
  have hFb9 := em.hFb
  have hFb : F < 2 ^ 100 := by omega
  have hS : encS2 F L = (F + 132 + L + 63) / 32 * 32 := rfl
  have hLs := hL.small
  have hLm := hL.mod
  have hLle := hL.le
  have hLlt := hL.lt
  obtain ⟨within, hrun⟩ := hend
  rcases extcodesize_outcome hberlin (by code_fact) (by code_fact) hz within hrun with
    herr | ⟨cd, z1, hcode, hg1, hz1, w1, hrun1⟩
  · exact absurd hok herr
  have hend1 : EndsL (processRunner fork bound) z1 s := ⟨w1, hrun1⟩
  have hcs : isZero (BitVec.ofNat 256 cd.size) = 0 := by
    apply Classical.byContradiction
    intro hcs
    obtain ⟨-, z2, hz2, hend2⟩ := ok_splitLE (B := 16) (c := 16) (Nat.le_refl _)
      (fun g hg => b3581_1 hcs (by simp) hg) hz1 hend1 hok
    exact tail_no_code hberlin (by simp) (RunsTo.of_at hz2 hend2) hok
  obtain ⟨hg2, z2, hz2, hend2⟩ := ok_splitLE (B := 16) (c := 16) (Nat.le_refl _)
    (fun g hg => b3581_0 hcs (by simp) hg) hz1 hend1 hok
  obtain ⟨hg3, z3, hz3, hend3⟩ := ok_splitLE (B := encCost F c) (c := encCost F c)
    (Nat.le_refl _) (fun g hg => encoder hberlin hL em hg) hz2 hend2 hok
  obtain ⟨M1, M2, M3, M4, M5, -, -, -, -, -, e6, -, -, -, -, -, -, -, n0, n64, n96, nd⟩ :=
    enc_chain hL em dg nonce deadline value spender owner sel
  rw [e6, sub3] at hz3
  rw [show bitwiseAnd ADDR_MASK owner = bitwiseAnd owner ADDR_MASK from BitVec.and_comm _ _]
    at hz3
  have hXn : (W (F + c + 132)).toNat = F + c + 132 := W_toNat (by omega)
  have hNn : (W (c + 100)).toNat = c + 100 := W_toNat (by omega)
  -- the call
  obtain ⟨w3, hrun3⟩ := hend3
  rcases gas_outcome (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz3 w3 hrun3 with
    herr | ⟨z4, hz4, w4, hrun4⟩
  · exact absurd hok herr
  rcases staticcall_sent hparis hglam (by code_fact) (by code_fact) hz4.toLogic w4 hrun4 with
    herr | ⟨flag, out, g5, st, ss, z5, hflag, hat, hle, hso, hpar, hlogs, ⟨w5, hrun5⟩, hdel,
      href, hsent⟩
  · exact absurd hok herr
  rw [staticcall_mem_same out (by rw [hXn, hNn, n0]; omega)] at hat
  have h := RunsTo.of_logic hat ⟨w5, hrun5⟩
  have hX32 : (add (W (F + c + 132)) (32 : U256)).toNat = (W (F + c + 132)).toNat + 32 := by
    rw [show add (W (F + c + 132)) (32 : U256) = W (F + c + 132 + 32) from W_add _ _,
      W_toNat (by omega), hXn]
  rcases permitBytes_after_call hberlin n0 (by omega) (by rw [hXn]; omega)
      (by rw [hXn]; omega) hX32 n64 hflag h hok with
    ⟨-, g, l, hB, hat0, e0⟩ | ⟨hN, M', g, l, hB, s0, s64, s96, sX, sX32, hat1, e1⟩
  · -- no return data
    exfalso
    rcases hflag with rfl | rfl
    · obtain ⟨-, z6, hz6, hend6⟩ := ok_splitLE (B := 44) (c := 44) (Nat.le_refl _)
        (fun G hG => sbN0 (rest := []) (s := F + 2 * c + 286) hberlin (by omega) n0 n96
          (by simp) hG) hat0 e0 hok
      exact permit_fail_tail hberlin (by simp) (RunsTo.of_at hz6 hend6) hok
    · obtain ⟨-, z6, hz6, hend6⟩ := ok_splitLE (B := 58) (c := 58) (Nat.le_refl _)
        (fun G hG => sbN1 (rest := []) (s := F + 2 * c + 286) hberlin (by omega) n0 n96
          (by simp) hG) hat0 e0 hok
      exact permit_fail_tail hberlin (by simp) (RunsTo.of_at hz6 hend6) hok
  · -- return data of 32 bytes
    rw [hXn] at sX sX32
    have f64 : mw M' 64 = W (F + c + 132 + 64) :=
      s64.trans (by
        rw [show bitwiseAnd (add (32 : U256) (63 : U256)) (bitwiseNot (31 : U256)) = W 64 from by
          decide, W_add])
    rcases hflag with rfl | rfl
    · exfalso
      obtain ⟨-, z6, hz6, hend6⟩ := ok_splitLE (B := 46) (c := 46) (Nat.le_refl _)
        (fun G hG => sbA0 (rest := []) (X := F + c + 132) (s := F + 2 * c + 286) hberlin
          (by omega) (by omega) (by omega) (by omega) s0 f64 sX sX32 (by simp) hG) hat1 e1 hok
      exact permit_fail_tail hberlin (by simp) (RunsTo.of_at hz6 hend6) hok
    by_cases hm : equal (loadWord (memoryReadBytes out 0 32) 0 32)
        (bitwiseAnd (loadWord (memoryReadBytes out 0 32) 0 32)
          (115792089210356248756420345214020892766250353992003419616917011526809519390720 : U256))
        = 0
    · exfalso
      obtain ⟨-, z6, hz6, hend6⟩ := ok_splitLE (B := 229) (c := 229) (Nat.le_refl _)
        (fun G hG => sbA1m (rest := []) (X := F + c + 132) (s := F + 2 * c + 286) hberlin
          (by omega) (by omega) (by omega) (by omega) s0 f64 sX sX32 hm (by simp) hG) hat1 e1 hok
      exact tail_mask hberlin (by simp) (RunsTo.of_at hz6 hend6) hok
    by_cases he : equal (bitwiseAnd
        (115792089210356248756420345214020892766250353992003419616917011526809519390720 : U256)
        (loadWord (memoryReadBytes out 0 32) 0 32))
        (10019309979067222254582373821846632475949454479833780424560900009889672200192 : U256) = 0
    · exfalso
      obtain ⟨-, z6, hz6, hend6⟩ := ok_splitLE (B := 316) (c := 316) (Nat.le_refl _)
        (fun G hG => sbA1e (rest := []) (X := F + c + 132) (s := F + 2 * c + 286) hberlin
          (by omega) (by omega) (by omega) (by omega) s0 f64 sX sX32 hm he (by simp) hG) hat1 e1
        hok
      exact tail_magic hberlin (by simp) (RunsTo.of_at hz6 hend6) hok
    obtain ⟨hg7, z7, hz7, hend7⟩ := ok_splitLE (B := 316) (c := 316) (Nat.le_refl _)
      (fun G hG => sbA1 (rest := []) (X := F + c + 132) (s := F + 2 * c + 286) hberlin
        (by omega) (by omega) (by omega) (by omega) s0 f64 sX sX32 hm he (by simp) hG) hat1 e1 hok
    obtain ⟨t0, t64, -, -, -⟩ := sbA1_mem (rest := []) (dg := dg) (nonce := nonce)
      (deadline := deadline) (value := value) (spender := spender) (owner := owner) (sel := sel)
      (X := F + c + 132) (s := F + 2 * c + 286) (by omega) (by omega) (by omega) (by omega) s0
      f64 sX sX32
    by_cases hgood : ¬(message.isStatic = false ∧ hasAccount st message.currentTarget)
    · exact (no_ok_stuckLE (B := 187) (fun G hG => sbW_2 (rest := []) (X := F + c + 132)
        (s := F + 2 * c + 286) hberlin (by omega) (by omega) (by omega) (by omega) t0 t64
        (Gas.bad_of_not hgood) (by simp) hG) hz7 hend7 hok).elim
    obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood
    obtain ⟨hg8, z8, hz8, hend8⟩ := ok_splitLE
      (B := (2007 + Gas.writeCost fork
        (originalAt st message.currentTarget (permitAllowKey owner spender))
        (storageAt st message.currentTarget (permitAllowKey owner spender)) value
        (coldIn ss message.currentTarget (permitAllowKey owner spender))) + 2301)
      (Nat.le_add_right _ _)
      (fun G hG => sbW (rest := []) (X := F + c + 132) (s := F + 2 * c + 286) hberlin (by omega)
        (by omega) (by omega) (by omega) hstatic hacc t0 t64 (by simp) (Nat.lt_of_succ_le hG))
      hz7 hend7 hok
    obtain ⟨hg9, -, ho, hgas, hst, hss⟩ := ok_exactLE (B := 1) (cost := 1)
      (fun G hG => b558_0 hG) hz8 hend8 hok
    obtain ⟨hw1, hw2⟩ := end_gas hg7 hg8 hg9 hgas
    have e1' := word_eq_of_equal hm
    have e2' := word_eq_of_equal he
    obtain ⟨cc, route, caller, msg, child, hcc, hroute, hsend, hran, hcerr, hcout⟩ :=
      hsent (by decide)
    exact ⟨cd, out, st, ss, g, hcode, isZero_eq_zero_iff.mp hcs, by omega,
      ownerCall_of_sends (i := W (F + c + 132)) (isz := W (c + 100))
        (by rw [hXn, hNn, n0]; omega) (by rw [hXn, hNn]; exact nd) hcc hroute hsend hran hcerr
        hcout, hN,
      e1'.trans ((BitVec.and_comm _ _).trans e2'), hso, hpar, hlogs, hdel, href, by omega,
      hstatic, hacc, hw1, ho, hw2, hst, hss⟩

end SkyVerify

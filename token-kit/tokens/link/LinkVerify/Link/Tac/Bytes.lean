import LinkVerify.Link.Tac.Main

/-!
# transferAndCall: the head of the data of the second log and of the call data

The two byte strings are ranges of the memory from the free memory pointer `tacF message`
(`tacLog2Data`, `tacCallData` in Defs.lean). Here, the words of their heads:

- `tac_log2_words`: the size of the data of the second log, and its first three words: the
  amount, the offset 64 of the bytes, and the length of the bytes.
- `tac_call_words`: the size of the call data and the four words after the selector: the
  caller, the amount, the offset 96 of the bytes, and the length of the bytes.
- `tac_call_selector`, `sel_bytes`: the first four bytes of the call data are a4 c0 ed 36, the
  selector of `onTokenTransfer(address,uint256,bytes)`.
- `tac_log2_head`, `tac_call_head`: the same facts, as words of the two byte strings.

What is not proven here: the bytes after the head (the bytes of the data, in whole words). They
are exact by definition only: the memory terms `tacLogMem` and `tacMem`.
-/

set_option autoImplicit false
set_option linter.deprecated false
set_option maxRecDepth 8192

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit
open LinkVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

/-- The copy loop of the second log leaves the bytes below its first word. -/
theorem cp1_frame {mem : ByteArray} {F W S a j : Nat} (hFm : F % 32 = 0) (hSm : S % 32 = 0)
    (hsz : mem.size = S) (hSa : F + 96 ≤ S) (h : a + j ≤ F + 96) :
    memoryReadBytes (cp1Mem mem F W S) a j = memoryReadBytes mem a j :=
  (lp1_mem hFm hSm (W / 32) 0 mem (by rw [hsz]; omega)).2 a j (by omega)

/-- The copy loop of the call data leaves the bytes below its first word. -/
theorem cp2_frame {mem : ByteArray} {F W S a j : Nat} (hFm : F % 32 = 0) (hSm : S % 32 = 0)
    (hsz : mem.size = S) (hSa : F + 160 ≤ S) (h : a + j ≤ F + 132) :
    memoryReadBytes (cp2Mem mem F W S) a j = memoryReadBytes mem a j :=
  (lp2_mem hFm hSm (W / 32) 0 mem (by rw [hsz]; omega)).2 a j (by omega)

/-- The cut of the last word of the second log leaves the bytes below the data. -/
theorem lg2_frame {L : U256} {mem : ByteArray} {F N W a j : Nat} (hW : W = (N + 31) / 32 * 32)
    (hsz : mem.size = F + W + 96) (h : a + j ≤ F + 96) :
    memoryReadBytes (lg2Mem L mem F N W) a j = memoryReadBytes mem a j := by
  unfold lg2Mem
  split
  · rfl
  · unfold lg2mMem
    exact read_wr_ne hsz (Nat.le_refl _) (by omega) (by omega) (.inl (by omega))

/-- The cut of the last word of the call data leaves the bytes below the data. -/
theorem fb2_frame {L : U256} {mem : ByteArray} {F N W a j : Nat} (hW : W = (N + 31) / 32 * 32)
    (hsz : mem.size = F + W + 160) (h : a + j ≤ F + 132) :
    memoryReadBytes (fb2Mem L mem F N W) a j = memoryReadBytes mem a j := by
  unfold fb2Mem
  split
  · rfl
  · unfold fb2mMem
    exact read_wr_ne hsz (Nat.le_refl _) (by omega) (by omega) (.inl (by omega))

/-- The offset of the bytes in the call data, as the code computes it, is 96. -/
theorem off96 (x : U256) :
    sub (add (32 : U256) (add (32 : U256) (add (32 : U256) x))) x = (96 : U256) := by
  unfold add sub
  bv_omega

/-- The data of the second log: its size and its first three words. -/
theorem tac_log2_words (hN : tacN message < 2 ^ 64) :
    (tacLog2Data message).size = tacW message + 96 ∧
    loadWord (memoryReadBytes (tacLogMem message) (tacF message) 32) 0 32 = tacValue message ∧
    loadWord (memoryReadBytes (tacLogMem message) (tacF message + 32) 32) 0 32 = (64 : U256) ∧
    loadWord (memoryReadBytes (tacLogMem message) (tacF message + 64) 32) 0 32 =
      tacLen message := by
  have hL : (tacLen message).toNat = tacN message := rfl
  have hF : (tacFpw (tacLen message)).toNat = tacF message := tacFpw_toNat rfl hN
  have hFe : tacF message = tacW message + 128 := rfl
  have hW : tacW message = (tacN message + 31) / 32 * 32 := rfl
  have hFm : tacF message % 32 = 0 := by omega
  have hFb : tacF message < 2 ^ 128 := by omega
  have hF0 : 128 ≤ tacF message := by omega
  have hNF : tacW message + 128 ≤ tacF message := by omega
  obtain ⟨hsz1, h64_1, h96_1⟩ := dec_mem (message := message) hL hF hFe hW hN
  obtain ⟨hsz3, h64_3, h96_3, -, -⟩ := xf1_mem (message := message) hF hFm hFb hF0 hsz1 h64_1 h96_1
  obtain ⟨hsz4, h64_4, h96_4, -, -⟩ :=
    xf2_mem (message := message) (to := tacTo message) hF hFm hFb hF0 hsz3 h64_3 h96_3
  obtain ⟨hsz5, h64_5, h96_5, -, -, -⟩ :=
    xf3_mem (to := tacTo message) (value := tacValue message) hF hFm hFb hF0 hsz4 h64_4 h96_4
  obtain ⟨hsz6, h64_6, h96_6, hv, ho, hl⟩ :=
    lg1_mem (value := tacValue message) hF hFm hFb hF0 hL hW hNF hsz5 h64_5 h96_5
  obtain ⟨hsz7, h64_7, h96_7⟩ := cp1_mem (S := tacF message + 96) hF0 hFm hW hsz6 (by omega)
    (by omega) (by omega) h64_6 h96_6
  obtain ⟨hsz8, -, -⟩ := lg2_mem hF hFm hFb hF0 hL hW hNF hsz7 h64_7 h96_7
  refine ⟨size_memoryReadBytes (by rw [show (tacLogMem message).size = _ from hsz8]; omega),
    ?_, ?_, ?_⟩
  · show loadWord (memoryReadBytes (lg2Mem _ (cp1Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [lg2_frame hW hsz7 (by omega), cp1_frame hFm (by omega) hsz6 (by omega) (by omega)]
    exact hv
  · show loadWord (memoryReadBytes (lg2Mem _ (cp1Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [lg2_frame hW hsz7 (by omega), cp1_frame hFm (by omega) hsz6 (by omega) (by omega)]
    exact ho
  · show loadWord (memoryReadBytes (lg2Mem _ (cp1Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [lg2_frame hW hsz7 (by omega), cp1_frame hFm (by omega) hsz6 (by omega) (by omega)]
    exact hl

/-- The call data: its size and the four words after the selector: the caller (cut to 160
bits), the amount, the offset 96 of the bytes and the length of the bytes. -/
theorem tac_call_words (hN : tacN message < 2 ^ 64) :
    (tacCallData message).size = tacW message + 132 ∧
    loadWord (memoryReadBytes (tacMem message) (tacF message + 4) 32) 0 32 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          message.caller.toU256) ∧
    loadWord (memoryReadBytes (tacMem message) (tacF message + 36) 32) 0 32 = tacValue message ∧
    loadWord (memoryReadBytes (tacMem message) (tacF message + 68) 32) 0 32 = (96 : U256) ∧
    loadWord (memoryReadBytes (tacMem message) (tacF message + 100) 32) 0 32 =
      tacLen message := by
  have hL : (tacLen message).toNat = tacN message := rfl
  have hF : (tacFpw (tacLen message)).toNat = tacF message := tacFpw_toNat rfl hN
  have hFe : tacF message = tacW message + 128 := rfl
  have hW : tacW message = (tacN message + 31) / 32 * 32 := rfl
  have hFm : tacF message % 32 = 0 := by omega
  have hFb : tacF message < 2 ^ 128 := by omega
  have hF0 : 128 ≤ tacF message := by omega
  have hNF : tacW message + 128 ≤ tacF message := by omega
  obtain ⟨hsz1, h64_1, h96_1⟩ := dec_mem (message := message) hL hF hFe hW hN
  obtain ⟨hsz3, h64_3, h96_3, -, -⟩ := xf1_mem (message := message) hF hFm hFb hF0 hsz1 h64_1 h96_1
  obtain ⟨hsz4, h64_4, h96_4, -, -⟩ :=
    xf2_mem (message := message) (to := tacTo message) hF hFm hFb hF0 hsz3 h64_3 h96_3
  obtain ⟨hsz5, h64_5, h96_5, -, -, -⟩ :=
    xf3_mem (to := tacTo message) (value := tacValue message) hF hFm hFb hF0 hsz4 h64_4 h96_4
  obtain ⟨hsz6, h64_6, h96_6, -, -, -⟩ :=
    lg1_mem (value := tacValue message) hF hFm hFb hF0 hL hW hNF hsz5 h64_5 h96_5
  obtain ⟨hsz7, h64_7, h96_7⟩ := cp1_mem (S := tacF message + 96) hF0 hFm hW hsz6 (by omega)
    (by omega) (by omega) h64_6 h96_6
  obtain ⟨hsz8, h64_8, h96_8⟩ := lg2_mem hF hFm hFb hF0 hL hW hNF hsz7 h64_7 h96_7
  obtain ⟨hsz10, h64_10, h96_10, hfrom, hval, hoff, hlen⟩ :=
    fb1_mem (message := message) (value := tacValue message)
      (S1 := max (tacF message + tacW message + 96) (tacF message + 128))
      (S2 := max (max (tacF message + tacW message + 96) (tacF message + 128))
        (tacF message + 160)) hF hFm hFb hF0 hL hW hNF hsz8 h64_8 h96_8 rfl rfl
  obtain ⟨hsz11, h64_11, h96_11⟩ := cp2_mem
    (S := max (max (tacF message + tacW message + 96) (tacF message + 128))
      (tacF message + 160)) hF0 hFm hW hsz10 (by omega) (by omega) (by omega) h64_10 h96_10
  obtain ⟨hsz12, -, -⟩ := lg2_mem hF hFm hFb hF0 hL hW hNF hsz7 h64_7 h96_7
  obtain ⟨hsz13, -, -⟩ := tac_call_mem hN
  refine ⟨size_memoryReadBytes (by rw [show (tacMem message).size = _ from hsz13]; omega),
    ?_, ?_, ?_, ?_⟩
  · show loadWord (memoryReadBytes (fb2Mem _ (cp2Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [fb2_frame hW hsz11 (by omega), cp2_frame hFm (by omega) hsz10 (by omega) (by omega)]
    exact hfrom
  · show loadWord (memoryReadBytes (fb2Mem _ (cp2Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [fb2_frame hW hsz11 (by omega), cp2_frame hFm (by omega) hsz10 (by omega) (by omega)]
    exact hval
  · show loadWord (memoryReadBytes (fb2Mem _ (cp2Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [fb2_frame hW hsz11 (by omega), cp2_frame hFm (by omega) hsz10 (by omega) (by omega)]
    exact hoff.trans (off96 _)
  · show loadWord (memoryReadBytes (fb2Mem _ (cp2Mem _ _ _ _) _ _ _) _ 32) 0 32 = _
    rw [fb2_frame hW hsz11 (by omega), cp2_frame hFm (by omega) hsz10 (by omega) (by omega)]
    exact hlen

/-! ## The selector, and the words as words of the two byte strings -/

/-- The first `k` bytes at `o` after a write of a word at `o`: the first `k` bytes of the word. -/
theorem read_wr_head {m : ByteArray} {sz sz' o k : Nat} {v : U256} (hs : m.size = sz)
    (hle : sz ≤ sz') (hfit : o + 32 ≤ sz') (hk0 : 0 < k) (hk : k ≤ 32) :
    memoryReadBytes (memoryWrite (memoryExtend m (sz' - sz)) o (wordBytes v)) o k =
      (wordBytes v).extract 0 k := by
  have hw : (wordBytes v).size = 32 := size_wordBytes v
  have h := memoryReadBytes_memoryWrite (memory := memoryExtend m (sz' - sz))
    (value := wordBytes v) (start := o) (by rw [size_memoryExtend, hs, hw]; omega)
  rw [hw] at h
  conv => rhs; rw [← h]
  unfold memoryReadBytes
  rw [if_neg (by omega), if_neg (by decide), ByteArray.extract_extract]
  congr 1 <;> omega

/-- A range of a range of the memory is a range of the memory. -/
theorem read_read {m : ByteArray} {a n k j : Nat} (hj : 0 < j) (h : k + j ≤ n) :
    memoryReadBytes (memoryReadBytes m a n) k j = memoryReadBytes m (a + k) j := by
  unfold memoryReadBytes
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), ByteArray.extract_extract]
  congr 1
  omega

/-- The word of the selector of `onTokenTransfer(address,uint256,bytes)`: 0xa4c0ed36, then 28
zero bytes. -/
def SELW : U256 := (74520178973814446874257326340491505677632248123858308376541350643553525563392 : U256)

/-- The first four bytes of the head of the call data: the selector word the code writes. -/
theorem fb1_sel {value L fpw : U256} {mem : ByteArray} {F W S1 S2 : Nat}
    (hsz : mem.size = F + W + 96) (hS1 : S1 = max (F + W + 96) (F + 128))
    (hS2 : S2 = max S1 (F + 160)) :
    memoryReadBytes (fb1Mem message value L fpw mem F W S1 S2) F 4 =
      (wordBytes SELW).extract 0 4 := by
  unfold fb1Mem SELW
  have s1 := size_wr (v := (74520178973814446874257326340491505677632248123858308376541350643553525563392 : U256)) (o := F) hsz (Nat.le_refl _) (by omega)
  have s2 := size_wr (v := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256))
    (o := F + 4) s1 (Nat.le_refl _) (by omega)
  have s3 := size_wr (v := value) (o := F + 36) s2 (Nat.le_refl _) (by omega)
  have s4 := size_wr (v := sub (add (32 : U256) (add (32 : U256) (add (32 : U256)
    (add (4 : U256) fpw)))) (add (4 : U256) fpw)) (o := F + 68) (sz' := S1) s3 (by omega)
    (by omega)
  rw [read_wr_ne s4 (by omega) (by omega) (by omega) (.inl (by omega)),
    read_wr_ne s3 (by omega) (by omega) (by omega) (.inl (by omega)),
    read_wr_ne s2 (Nat.le_refl _) (by omega) (by omega) (.inl (by omega)),
    read_wr_ne s1 (Nat.le_refl _) (by omega) (by omega) (.inl (by omega))]
  exact read_wr_head hsz (Nat.le_refl _) (by omega) (by omega) (by omega)

/-- The first four bytes of the call data: those of the selector word. -/
theorem tac_call_selector (hN : tacN message < 2 ^ 64) :
    memoryReadBytes (tacCallData message) 0 4 = (wordBytes SELW).extract 0 4 := by
  have hL : (tacLen message).toNat = tacN message := rfl
  have hF : (tacFpw (tacLen message)).toNat = tacF message := tacFpw_toNat rfl hN
  have hFe : tacF message = tacW message + 128 := rfl
  have hW : tacW message = (tacN message + 31) / 32 * 32 := rfl
  have hFm : tacF message % 32 = 0 := by omega
  have hFb : tacF message < 2 ^ 128 := by omega
  have hF0 : 128 ≤ tacF message := by omega
  have hNF : tacW message + 128 ≤ tacF message := by omega
  obtain ⟨hsz1, h64_1, h96_1⟩ := dec_mem (message := message) hL hF hFe hW hN
  obtain ⟨hsz3, h64_3, h96_3, -, -⟩ := xf1_mem (message := message) hF hFm hFb hF0 hsz1 h64_1 h96_1
  obtain ⟨hsz4, h64_4, h96_4, -, -⟩ :=
    xf2_mem (message := message) (to := tacTo message) hF hFm hFb hF0 hsz3 h64_3 h96_3
  obtain ⟨hsz5, h64_5, h96_5, -, -, -⟩ :=
    xf3_mem (to := tacTo message) (value := tacValue message) hF hFm hFb hF0 hsz4 h64_4 h96_4
  obtain ⟨hsz6, h64_6, h96_6, -, -, -⟩ :=
    lg1_mem (value := tacValue message) hF hFm hFb hF0 hL hW hNF hsz5 h64_5 h96_5
  obtain ⟨hsz7, h64_7, h96_7⟩ := cp1_mem (S := tacF message + 96) hF0 hFm hW hsz6 (by omega)
    (by omega) (by omega) h64_6 h96_6
  obtain ⟨hsz8, h64_8, h96_8⟩ := lg2_mem hF hFm hFb hF0 hL hW hNF hsz7 h64_7 h96_7
  obtain ⟨hsz10, h64_10, h96_10, -, -, -, -⟩ :=
    fb1_mem (message := message) (value := tacValue message)
      (S1 := max (tacF message + tacW message + 96) (tacF message + 128))
      (S2 := max (max (tacF message + tacW message + 96) (tacF message + 128))
        (tacF message + 160)) hF hFm hFb hF0 hL hW hNF hsz8 h64_8 h96_8 rfl rfl
  obtain ⟨hsz11, -, -⟩ := cp2_mem
    (S := max (max (tacF message + tacW message + 96) (tacF message + 128))
      (tacF message + 160)) hF0 hFm hW hsz10 (by omega) (by omega) (by omega) h64_10 h96_10
  unfold tacCallData
  rw [read_read (by decide) (by omega), Nat.add_zero]
  show memoryReadBytes (fb2Mem _ (cp2Mem _ _ _ _) _ _ _) _ 4 = _
  rw [fb2_frame hW hsz11 (by omega), cp2_frame hFm (by omega) hsz10 (by omega) (by omega)]
  exact fb1_sel hsz8 rfl rfl

/-- The four bytes of the selector: a4 c0 ed 36. -/
theorem sel_bytes : (wordBytes SELW).extract 0 4 = ⟨#[0xa4, 0xc0, 0xed, 0x36]⟩ := by
  decide +kernel

/-- The head of the data of the second log, as words of the byte string itself: the amount, the
offset 64 of the bytes and the length of the bytes. -/
theorem tac_log2_head (hN : tacN message < 2 ^ 64) :
    loadWord (memoryReadBytes (tacLog2Data message) 0 32) 0 32 = tacValue message ∧
    loadWord (memoryReadBytes (tacLog2Data message) 32 32) 0 32 = (64 : U256) ∧
    loadWord (memoryReadBytes (tacLog2Data message) 64 32) 0 32 = tacLen message := by
  obtain ⟨-, h0, h1, h2⟩ := tac_log2_words hN
  unfold tacLog2Data
  rw [read_read (by decide) (by omega), read_read (by decide) (by omega),
    read_read (by decide) (by omega), Nat.add_zero]
  exact ⟨h0, h1, h2⟩

/-- The head of the call data, as bytes and words of the byte string itself: the selector, the
caller (cut to 160 bits), the amount, the offset 96 of the bytes and the length of the bytes. -/
theorem tac_call_head (hN : tacN message < 2 ^ 64) :
    memoryReadBytes (tacCallData message) 0 4 = ⟨#[0xa4, 0xc0, 0xed, 0x36]⟩ ∧
    loadWord (memoryReadBytes (tacCallData message) 4 32) 0 32 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) ∧
    loadWord (memoryReadBytes (tacCallData message) 36 32) 0 32 = tacValue message ∧
    loadWord (memoryReadBytes (tacCallData message) 68 32) 0 32 = (96 : U256) ∧
    loadWord (memoryReadBytes (tacCallData message) 100 32) 0 32 = tacLen message := by
  obtain ⟨-, h0, h1, h2, h3⟩ := tac_call_words hN
  refine ⟨(tac_call_selector hN).trans sel_bytes, ?_⟩
  unfold tacCallData
  rw [read_read (by decide) (by omega), read_read (by decide) (by omega),
    read_read (by decide) (by omega), read_read (by decide) (by omega)]
  exact ⟨h0, h1, h2, h3⟩

end LinkVerify.Tac

import SkyVerify.Sky.BytesWord

/-!
# The copy routine of the code (pc 3812), for any number of bytes

Hand-written. The code at pc 3812 copies `N` bytes of the memory from `S` to `D`, one word at a
time, and then writes a zero word at `D + N`. The number of turns of its loop is the number of
words of `N`, so the generators of the kit (fixed shapes) cannot cut it; this file proves it by
induction, with exact gas:

- `wr`: the memory after the write of a word at any offset (the growth is computed from the
  size), with the rule `mstoreW`;
- `loopMem`: the memory after `r` turns of the loop, and `loopMem_spec`, what it holds;
- `copy_loop`: the loop from pc 3815 to its exit at pc 3839;
- `copy_routine`: the routine from pc 3812 to the JUMP at pc 3847, to the memory `copyMem`;
- `copyMem_spec`: the size and the bytes of `copyMem`.
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

/-! ## A write of a word at any offset -/

/-- The memory after MSTORE of `v` at `o`: the memory grows to the end of the word rounded up to
32 when the word ends past it. -/
def wr (M : ByteArray) (o : Nat) (v : U256) : ByteArray :=
  memoryWrite (memoryExtend M (max M.size ((o + 63) / 32 * 32) - M.size)) o (wordBytes v)

theorem size_wr (M : ByteArray) (o : Nat) (v : U256) :
    (wr M o v).size = max M.size ((o + 63) / 32 * 32) := by
  unfold wr
  rw [size_rawW rfl (by omega)]
  omega

theorem byteAt_wr_miss {M : ByteArray} {o i : Nat} {v : U256} (h : i < o ∨ o + 32 ≤ i) :
    byteAt (wr M o v) i = byteAt M i :=
  byteAt_rawW_miss rfl (by omega) h

theorem byteAt_wr_hit {M : ByteArray} {o i : Nat} {v : U256} (h1 : o ≤ i) (h2 : i < o + 32) :
    byteAt (wr M o v) i = byteAt (wordBytes v) (i - o) :=
  byteAt_rawW_hit rfl (by omega) h1 h2

/-- The growth of the memory for a word at any offset. -/
theorem extW {sz o : Nat} {start : U256} (ho : start.toNat = o) (hmod : sz % 32 = 0) :
    extendMemory sz [(start, (32 : U256))] =
      ⟨memoryGasCost (max sz ((o + 63) / 32 * 32)) - memoryGasCost sz,
        max sz ((o + 63) / 32 * 32) - sz⟩ := by
  by_cases h : o + 32 ≤ sz
  · have e : max sz ((o + 63) / 32 * 32) = sz := by omega
    rw [ext0 ho h, e, Nat.sub_self, Nat.sub_self]
  · have e : max sz ((o + 63) / 32 * 32) = (o + 63) / 32 * 32 := by omega
    rw [e]
    exact extN (s' := (o + 63) / 32 * 32) ho hmod (by omega) (by omega) (by omega) (by omega)
      (by omega)

/-- MSTORE at any offset, to the memory `wr`. -/
theorem mstoreW {pc : Nat} {start value : U256} {rest : List U256} {M M' : ByteArray} {o : Nat}
    {gas : Nat} {state : State.TransactionState} {substate : Substate}
    (hlt : pc < CODE.size) (hbyte : CODE[pc] = 0x52) (ho : start.toNat = o)
    (hmod : M.size % 32 = 0) (hm : wr M o value = M')
    (hgas : 3 + (memoryGasCost M'.size - memoryGasCost M.size) ≤ gas) :
    Gas.HoareG fork (At CODE message pc (start :: value :: rest) M gas state substate)
      (At CODE message (pc + 1) rest M'
        (gas - (3 + (memoryGasCost M'.size - memoryGasCost M.size))) state substate) := by
  subst hm
  rw [size_wr] at hgas ⊢
  exact mstoreK hlt hbyte rfl (extW ho hmod) ho rfl hgas

/-! ## The loop -/

/-- The memory after `r` turns of the loop, from the turn `k`: each turn writes at `D + 32 k`
the word read at `S + 32 k`. -/
def loopMem (S D : Nat) : Nat → Nat → ByteArray → ByteArray
  | _, 0, M => M
  | k, r + 1, M =>
    loopMem S D (k + 1) r (wr M (D + 32 * k) (loadWord (memoryReadBytes M (S + 32 * k) 32) 0 32))

/-- What `loopMem` holds, for a source that ends before the target (`S + N ≤ D`): its size, the
bytes below the first word written, and the bytes copied. -/
theorem loopMem_spec {S D N : Nat} (h1 : S + 32 ≤ D) (h2 : S + N ≤ D) :
    ∀ (r k : Nat) (M : ByteArray), M.size % 32 = 0 → S + 32 * k + 32 ≤ M.size →
      (loopMem S D k r M).size % 32 = 0 ∧ M.size ≤ (loopMem S D k r M).size ∧
      (loopMem S D k r M).size ≤ max M.size ((D + 32 * (k + r) + 31) / 32 * 32) ∧
      (0 < r → D + 32 * (k + r) ≤ (loopMem S D k r M).size) ∧
      (∀ j, j < D + 32 * k → byteAt (loopMem S D k r M) j = byteAt M j) ∧
      (∀ j, 32 * k ≤ j → j < 32 * (k + r) → j < N →
        byteAt (loopMem S D k r M) (D + j) = byteAt M (S + j)) := by
  intro r
  induction r with
  | zero =>
    intro k M hmod hfit
    exact ⟨hmod, Nat.le_refl _, Nat.le_max_left _ _, fun h => absurd h (Nat.lt_irrefl 0),
      fun _ _ => rfl, fun j a b _ => by omega⟩
  | succ r ih =>
    intro k M hmod hfit
    obtain ⟨M1, hM1⟩ : ∃ M1, M1 = wr M (D + 32 * k)
      (loadWord (memoryReadBytes M (S + 32 * k) 32) 0 32) := ⟨_, rfl⟩
    have eL : loopMem S D k (r + 1) M = loopMem S D (k + 1) r M1 := by rw [hM1]; rfl
    have s1 : M1.size = max M.size ((D + 32 * k + 63) / 32 * 32) := by rw [hM1, size_wr]
    obtain ⟨a, b, c, d, e, f⟩ := ih (k + 1) M1 (by omega) (by omega)
    rw [eL]
    refine ⟨a, by omega, by omega, fun _ => ?_, fun j hj => ?_, fun j j1 j2 j3 => ?_⟩
    · rcases Nat.eq_zero_or_pos r with h | h
      · omega
      · have := d h
        omega
    · rw [e j (by omega), hM1, byteAt_wr_miss (.inl (by omega))]
    · by_cases hj : j < 32 * (k + 1)
      · rw [e (D + j) (by omega), hM1, byteAt_wr_hit (by omega) (by omega),
          show D + j - (D + 32 * k) = j - 32 * k by omega, byteAt_wordOf hfit (by omega)]
        congr 1
        omega
      · rw [f j (by omega) (by omega) j3, hM1, byteAt_wr_miss (.inl (by omega))]

/-- The loop of the copy routine, from its head (pc 3815) at the turn `k` to its exit (pc 3839),
`r` turns later. Each turn costs 67 gas and the growth of the memory; the last test costs 26. -/
theorem copy_loop {S D N K : Nat} (hS : S < 2 ^ 100) (hD : D < 2 ^ 100) (hN : N < 2 ^ 100)
    (hK1 : N ≤ 32 * K) (hK2 : 32 * K < N + 32) (h1 : S + 32 ≤ D) (h2 : S + N ≤ D) :
    ∀ (r k : Nat) (M : ByteArray) (gas : Nat) {rest : List U256}
      {state : State.TransactionState} {substate : Substate},
      k + r = K → M.size % 32 = 0 → S + 32 * k + 32 ≤ M.size → rest.length ≤ 900 →
      26 + 67 * r + (memoryGasCost (loopMem S D k r M).size - memoryGasCost M.size) ≤ gas →
      Logic.HoareG fork
        (At CODE message 3815 (W (32 * k) :: W S :: W D :: W N :: rest) M gas state substate)
        (At CODE message 3839 (W (32 * K) :: W S :: W D :: W N :: rest) (loopMem S D k r M)
          (gas - (26 + 67 * r + (memoryGasCost (loopMem S D k r M).size - memoryGasCost M.size)))
          state substate) := by
  intro r
  induction r with
  | zero =>
    intro k M gas rest state substate hk hmod hfit hrest hg
    have ek : k = K := by omega
    subst ek
    have e0 : loopMem S D k 0 M = M := rfl
    rw [e0] at hg ⊢
    have hlt : lessThan (W (32 * k)) (W N) = 0 := by
      unfold lessThan
      rw [W_toNat (by omega), W_toNat (by omega)]
      exact if_neg (by omega)
    have hc : isZero (lessThan (W (32 * k)) (W N)) ≠ 0 := by rw [hlt]; decide
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 (instruction_of_stackOnlyStep rfl)
    step unR 0x15 instruction_iszero
    step pushR 2 (3839 : U256)
    at_pc 3823
    step jumpiR hc
    at_pc 3839
    exact hoareL (restate rfl rfl rfl (by gas_ok) rfl rfl)
  | succ r ih =>
    intro k M gas rest state substate hk hmod hfit hrest hg
    obtain ⟨v, hv⟩ : ∃ v, loadWord (memoryReadBytes M (S + 32 * k) 32) 0 32 = v := ⟨_, rfl⟩
    obtain ⟨M1, hM1⟩ : ∃ M1, wr M (D + 32 * k) v = M1 := ⟨_, rfl⟩
    have eL : loopMem S D k (r + 1) M = loopMem S D (k + 1) r M1 := by rw [← hM1, ← hv]; rfl
    have s1 : M1.size = max M.size ((D + 32 * k + 63) / 32 * 32) := by rw [← hM1, size_wr]
    obtain ⟨-, sb, -, -, -, -⟩ := loopMem_spec h1 h2 r (k + 1) M1 (by omega) (by omega)
    have m1 := memoryGasCost_mono (show M.size ≤ M1.size by omega)
    have m2 := memoryGasCost_mono sb
    rw [eL] at hg ⊢
    have hlt : lessThan (W (32 * k)) (W N) = 1 := by
      unfold lessThan
      rw [W_toNat (by omega), W_toNat (by omega)]
      exact if_pos (by omega)
    have hc : isZero (lessThan (W (32 * k)) (W N)) = 0 := by rw [hlt]; decide
    step jumpdestR
    step dupR 3
    step dupR 1
    step binR 0x10 (instruction_of_stackOnlyStep rfl)
    step unR 0x15 instruction_iszero
    step pushR 2 (3839 : U256)
    at_pc 3823
    step jumpi0R hc
    at_pc 3824
    step dupR 1
    step dupR 1
    step binR 0x01 instruction_add
    step foldK (y := W (S + 32 * k))
      ((W_add (32 * k) S).trans (congrArg W (show 32 * k + S = S + 32 * k by omega)))
    step mloadK (by code_fact) (by code_fact) rfl (o := S + 32 * k) (W_toNat (by omega)) hfit hv
      (by gas_ok)
    step dupR 3
    step dupR 2
    step binR 0x01 instruction_add
    step foldK (y := W (D + 32 * k))
      ((W_add (32 * k) D).trans (congrArg W (show 32 * k + D = D + 32 * k by omega)))
    step mstoreW (by code_fact) (by code_fact) (o := D + 32 * k) (W_toNat (by omega)) hmod hM1
      (by gas_ok)
    step pushR 1 (32 : U256)
    at_pc 3834
    step binR 0x01 instruction_add
    step foldK (y := W (32 * (k + 1)))
      ((W_add 32 (32 * k)).trans (congrArg W (show 32 + 32 * k = 32 * (k + 1) by omega)))
    step pushR 2 (3815 : U256)
    at_pc 3838
    step jumpR
    at_pc 3815
    exact Logic.Triple.seq (ih (k + 1) M1 _ (by omega) (by omega) (by omega) hrest (by gas_ok))
      (hoareL (restate rfl rfl rfl (by gas_ok) rfl rfl))

/-! ## The routine -/

/-- The memory after the copy routine: the loop over the words of `N`, then a zero word at
`D + N`. -/
def copyMem (S D N : Nat) (M : ByteArray) : ByteArray :=
  wr (loopMem S D 0 ((N + 31) / 32) M) (D + N) (0 : U256)

/-- The memory after the copy routine: its size, the bytes below `D`, the `N` bytes copied, and
the 32 zero bytes after them. -/
theorem copyMem_spec {S D N : Nat} {M : ByteArray} (h1 : S + 32 ≤ D) (h2 : S + N ≤ D)
    (hmod : M.size % 32 = 0) (hfit : S + 32 ≤ M.size) :
    (copyMem S D N M).size = max M.size ((D + N + 63) / 32 * 32) ∧
    (∀ j, j < D → byteAt (copyMem S D N M) j = byteAt M j) ∧
    (∀ j, j < N → byteAt (copyMem S D N M) (D + j) = byteAt M (S + j)) ∧
    (∀ j, N ≤ j → j < N + 32 → byteAt (copyMem S D N M) (D + j) = 0) := by
  obtain ⟨a, b, c, d, e, f⟩ := loopMem_spec h1 h2 ((N + 31) / 32) 0 M hmod (by omega)
  unfold copyMem
  refine ⟨?_, fun j hj => ?_, fun j hj => ?_, fun j j1 j2 => ?_⟩
  · rw [size_wr]
    omega
  · rw [byteAt_wr_miss (.inl (by omega)), e j (by omega)]
  · rw [byteAt_wr_miss (.inl (by omega)), f j (by omega) (by omega) hj]
  · rw [byteAt_wr_hit (by omega) (by omega), byteAt_wordBytes_zero]

/-- The gas of the copy routine from pc 3812 to the JUMP at pc 3847: 47 for the opcodes outside
the loop, 67 for each word, and the growth of the memory. -/
def copyGas (S D N : Nat) (M : ByteArray) : Nat :=
  47 + 67 * ((N + 31) / 32) + (memoryGasCost (copyMem S D N M).size - memoryGasCost M.size)

/-- The copy routine, from its entry (pc 3812) to its JUMP back (pc 3847): `N` bytes from `S` to
`D`, for any `N`, with exact gas. The source ends before the target. -/
theorem copy_routine {S D N : Nat} {M : ByteArray} {gas : Nat} {rest : List U256}
    {state : State.TransactionState} {substate : Substate}
    (hS : S < 2 ^ 100) (hD : D < 2 ^ 100) (hN : N < 2 ^ 100) (h1 : S + 32 ≤ D) (h2 : S + N ≤ D)
    (hmod : M.size % 32 = 0) (hfit : S + 32 ≤ M.size) (hrest : rest.length ≤ 900)
    (hg : copyGas S D N M ≤ gas) :
    Logic.HoareG fork
      (At CODE message 3812 (W S :: W D :: W N :: rest) M gas state substate)
      (At CODE message 3847 rest (copyMem S D N M) (gas - copyGas S D N M) state substate) := by
  obtain ⟨a, b, c, d, e, f⟩ := loopMem_spec h1 h2 ((N + 31) / 32) 0 M hmod (by omega)
  obtain ⟨L, hL⟩ : ∃ L, loopMem S D 0 ((N + 31) / 32) M = L := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, wr L (D + N) (0 : U256) = C := ⟨_, rfl⟩
  have eC : copyMem S D N M = C := by unfold copyMem; rw [hL, hC]
  have sC : C.size = max L.size ((D + N + 63) / 32 * 32) := by rw [← hC, size_wr]
  unfold copyGas at hg ⊢
  rw [eC] at hg ⊢
  rw [hL] at a b
  have m1 := memoryGasCost_mono b
  have m2 := memoryGasCost_mono (show L.size ≤ C.size by omega)
  step jumpdestR
  step pushR 1 (0 : U256)
  at_pc 3815
  step foldK (y := W (32 * 0)) rfl
  refine Logic.Triple.seq (copy_loop hS hD hN (K := (N + 31) / 32) (by omega) (by omega) h1 h2
    ((N + 31) / 32) 0 M _ (by omega) hmod (by omega) (by omega) (by rw [hL]; omega)) ?_
  rw [hL]
  step jumpdestR
  step popR
  step popR
  at_pc 3842
  step pushR 1 (0 : U256)
  at_pc 3844
  step swap2K (by code_fact) (by code_fact) (by gas_ok)
  step binR 0x01 instruction_add
  step foldK (y := W (D + N)) ((W_add N D).trans (congrArg W (show N + D = D + N by omega)))
  step mstoreW (by code_fact) (by code_fact) (o := D + N) (W_toNat (by omega)) a hC (by gas_ok)
  exact hoareL (restate rfl rfl rfl (by gas_ok) rfl rfl)

end SkyVerify

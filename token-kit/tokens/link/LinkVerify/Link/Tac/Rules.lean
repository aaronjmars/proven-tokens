import TokenKit.Evm.RawMem
import TokenKit.Evm.Note
import TokenKit.Evm.SafeL
import TokenKit.Evm.Call
import TokenKit.Evm.Stack
import UsdtVerify.Evm.Call
import LinkVerify.Link.Steps

/-!
# Rules for a memory of unknown size

transferAndCall copies call data of any length to memory, so the size of the memory and the
offsets of its writes are terms, not numerals. The rules here state the growth of memory by
plain inequalities that `omega` closes.

- `ceil32_eq`: the rounding to a multiple of 32, as a division.
- `mstoreS`: MSTORE from a memory of size `sz` to a memory of size `sz'`.
- `size_wr`, `load_wr_self`, `load_wr_ne`, `read_wr_ne`: the size, the word written, and what
  a write leaves.
- `toNat_add'`, `toNat_sub'`: the value of a sum and of a difference with no wrap.
- `exponentBytes_one`: an exponent from 1 to 255 has one byte.
- `extcodesizeL`: EXTCODESIZE over the steps that are monotone in gas.

Nothing here is about one function.
-/

set_option autoImplicit false

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- The least multiple of 32 that is at least `x`, as a division. -/
theorem ceil32_eq (x : Nat) : ceil32 x = (x + 31) / 32 * 32 := by
  show (if x % 32 = 0 then x else x + 32 - x % 32) = (x + 31) / 32 * 32
  by_cases h : x % 32 = 0
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The value of a sum that does not wrap. -/
theorem toNat_add' {a b : U256} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y)
    (h : x + y < 2 ^ 256) : (add a b).toNat = x + y := by
  unfold add
  rw [BitVec.toNat_add, ha, hb]
  exact Nat.mod_eq_of_lt h

/-- The value of a difference that does not wrap. -/
theorem toNat_sub' {a b : U256} {x y : Nat} (ha : a.toNat = x) (hb : b.toNat = y)
    (h : y ≤ x) : (sub a b).toNat = x - y := by
  have hx : x < 2 ^ 256 := ha ▸ a.isLt
  unfold sub
  rw [BitVec.toNat_sub, ha, hb, show 2 ^ 256 - y + x = (x - y) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- An exponent from 1 to 255 has one byte. -/
theorem exponentBytes_one {e : U256} {x : Nat} (he : e.toNat = x) (h1 : 0 < x) (h2 : x < 256) :
    exponentBytes e = 1 := by
  unfold exponentBytes bitLength
  rw [he, if_neg (by omega)]
  have : x.log2 < 8 := (Nat.log2_lt (by omega)).mpr (by omega)
  omega

/-- MSTORE from a memory of size `sz`, a multiple of 32, to a memory of size `sz'`: the greater
of `sz` and the rounded end of the word. -/
theorem mstoreS {start value : U256} {rest : List U256} {sz sz' o : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) (hsz : memory.size = sz)
    (hmod : sz % 32 = 0) (ho : start.toNat = o)
    (hsz' : max sz ((o + 63) / 32 * 32) = sz')
    (hgas : 3 + (memoryGasCost sz' - memoryGasCost sz) ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (sz' - sz)) o (wordBytes value))
        (gas - (3 + (memoryGasCost sz' - memoryGasCost sz))) state substate) := by
  have h32 : (32 : U256).toNat = 32 := by decide
  have hext : extendMemory sz [(start, 32)] =
      ⟨memoryGasCost sz' - memoryGasCost sz, sz' - sz⟩ := by
    by_cases h : o + 32 ≤ sz
    · have e : sz' = sz := by omega
      rw [extendMemory_of_le (by rw [ho, h32]; exact h), e]
      simp
    · have e : sz' = (o + 32 + 31) / 32 * 32 := by omega
      rw [extendMemory_of_lt hmod (by decide) (by rw [ho, h32]; omega), ho, h32, ceil32_eq, e]
  exact mstoreK hlt hbyte hsz hext ho rfl hgas

/-- The size of a memory after a write of a word. -/
theorem size_wr {m : ByteArray} {sz sz' o : Nat} {v : U256} (hs : m.size = sz)
    (hle : sz ≤ sz') (hfit : o + 32 ≤ sz') :
    (memoryWrite (memoryExtend m (sz' - sz)) o (wordBytes v)).size = sz' := by
  rw [size_rawW hs (by omega)]
  omega

/-- The word at `o` after a write of a word at `o`. -/
theorem load_wr_self {m : ByteArray} {sz sz' o : Nat} {v : U256} (hs : m.size = sz)
    (hle : sz ≤ sz') (hfit : o + 32 ≤ sz') :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m (sz' - sz)) o (wordBytes v)) o 32)
      0 32 = v :=
  load_rawW_self hs (by omega)

/-- A write of a word at `o` leaves the known word at `a`, when the two do not overlap. -/
theorem load_wr_ne {m : ByteArray} {sz sz' o a : Nat} {v w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz)
    (hle : sz ≤ sz') (hfit : o + 32 ≤ sz') (ha : a + 32 ≤ sz) (hd : a + 32 ≤ o ∨ o + 32 ≤ a) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m (sz' - sz)) o (wordBytes v)) a 32)
      0 32 = w :=
  load_rawW h hs (by omega) ha hd

/-- A write of a word at `o` leaves the bytes that it does not touch. -/
theorem read_wr_ne {m : ByteArray} {sz sz' o a k : Nat} {v : U256} (hs : m.size = sz)
    (hle : sz ≤ sz') (hfit : o + 32 ≤ sz') (ha : a + k ≤ sz) (hd : a + k ≤ o ∨ o + 32 ≤ a) :
    memoryReadBytes (memoryWrite (memoryExtend m (sz' - sz)) o (wordBytes v)) a k =
      memoryReadBytes m a k :=
  read_rawW hs (by omega) ha hd

/-- The price of a LOG3 of `k` bytes. -/
theorem logCost3 {size : U256} {k : Nat} (h : size.toNat = k) :
    logCost 3 size = 1500 + 8 * k := by
  unfold logCost
  rw [h]
  show 375 + 8 * k + 375 * 3 = 1500 + 8 * k
  omega

/-- The number of words that cover `k` bytes. -/
theorem wordCount_eq (k : Nat) : wordCount k = (k + 31) / 32 := by
  show ceil32 k / 32 = (k + 31) / 32
  rw [ceil32_eq]
  omega

/-- CALLDATACOPY of `k` bytes to the end of a memory of size `sz`, a multiple of 32: the memory
grows by `k` rounded up to 32. -/
theorem calldatacopyS {start offset size : U256} {rest : List U256} {sz k : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37) (hsz : memory.size = sz)
    (hmod : sz % 32 = 0) (ho : start.toNat = sz) (hk : size.toNat = k)
    (hgas : 3 + 3 * ((k + 31) / 32) +
      (memoryGasCost (sz + (k + 31) / 32 * 32) - memoryGasCost sz) ≤ gas) :
    Logic.HoareG fork
      (At code message pc (start :: offset :: size :: rest) memory gas state substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory ((k + 31) / 32 * 32)) sz
          (copied message.data offset.toNat k))
        (gas - (3 + 3 * ((k + 31) / 32) +
          (memoryGasCost (sz + (k + 31) / 32 * 32) - memoryGasCost sz))) state substate) := by
  have hext : extendMemory sz [(start, size)] =
      ⟨memoryGasCost (sz + (k + 31) / 32 * 32) - memoryGasCost sz, (k + 31) / 32 * 32⟩ := by
    by_cases h : k = 0
    · have hz : size = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [hk, h]
        rfl
      rw [hz, extendMemory_of_length_eq_zero, h]
      simp
    · have hz : size ≠ 0 := by
        intro e
        rw [e] at hk
        exact h hk.symm
      rw [extendMemory_of_lt hmod hz (by rw [ho, hk]; omega), ho, hk, ceil32_eq]
      have e : (sz + k + 31) / 32 * 32 = sz + (k + 31) / 32 * 32 := by omega
      rw [e]
      congr 1
      omega
  exact calldatacopyK hlt hbyte hsz hext ho rfl hk (wordCount_eq k) rfl hgas

/-- The size of a memory after a copy to its end. -/
theorem size_cp {m data : ByteArray} {sz f k : Nat} (hs : m.size = sz) :
    (memoryWrite (memoryExtend m ((k + 31) / 32 * 32)) sz (copied data f k)).size =
      sz + (k + 31) / 32 * 32 :=
  size_rawC hs (by omega)

/-- A copy to the end of a memory leaves the bytes of the memory. -/
theorem read_cp {m data : ByteArray} {sz f k a j : Nat} (hs : m.size = sz) (ha : a + j ≤ sz) :
    memoryReadBytes (memoryWrite (memoryExtend m ((k + 31) / 32 * 32)) sz (copied data f k)) a j =
      memoryReadBytes m a j := by
  have hc : (copied data f k).size = k := by simp [ByteArray.size, bufferRead_length]
  by_cases hk : k = 0
  · have e : memoryWrite (memoryExtend m ((k + 31) / 32 * 32)) sz (copied data f k) =
        memoryExtend m ((k + 31) / 32 * 32) := by
      unfold memoryWrite
      rw [if_pos (by rw [hc, hk])]
    rw [e, memoryReadBytes_memoryExtend (by omega)]
  · rw [memoryReadBytes_memoryWrite_of_disjoint (by rw [size_memoryExtend, hc, hs]; omega)
        (by rw [hc]; omega),
      memoryReadBytes_memoryExtend (by omega)]

/-- A copy to the end of a memory leaves the known word at `a`. -/
theorem load_cp {m data : ByteArray} {sz f k a : Nat} {w : U256}
    (h : loadWord (memoryReadBytes m a 32) 0 32 = w) (hs : m.size = sz) (ha : a + 32 ≤ sz) :
    loadWord (memoryReadBytes (memoryWrite (memoryExtend m ((k + 31) / 32 * 32)) sz
      (copied data f k)) a 32) 0 32 = w := by
  rw [read_cp hs ha]
  exact h

/-- EXTCODESIZE from Berlin, over the steps that are monotone in gas: the word on top of the
stack, read as an address, is replaced by the size of the code `c` of that account; the account
is recorded as read and accessed; the price is the one of a cold or a warm access. The state
must give the code of the account. -/
theorem extcodesizeL (hfork : .berlin ≤ fork) {word : U256} {rest : List U256} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (toAddressMasked word)).codeHash = .ok c)
    (hgas : externalBaseCost fork (coldAccount substate (toAddressMasked word)) ≤ gas) :
    Logic.HoareG fork (At code message pc (word :: rest) memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory
        (gas - externalBaseCost fork (coldAccount substate (toAddressMasked word)))
        (state.recordAccountRead (toAddressMasked word))
        (accessAccount substate (toAddressMasked word))) :=
  liftAt fun rd => by
    refine Logic.At.ruleG_of_follows hlt hbyte
      (ofByte_of_decode (op := .extcodesize) rfl (Fork.frontier_le _))
      UsdtVerify.Complete.instruction_extcodesize' ?_ ?_
    · rintro evm ⟨-, -, -, -, hst, -, -, -, -, -, hs, -, -⟩ k low rfl
      have hst' : low.stack.val = word :: rest := hst
      have hs' : low.state = state := hs
      have found : accountCode low (toAddressMasked word) = .ok c := by
        simp [accountCode, hs', hcode, Except.mapError]
      have found' : accountCode (addGas k low) (toAddressMasked word) = .ok c := found
      rw [extcodesizeStep_of_accountCode hst' found,
        extcodesizeStep_of_accountCode (evm := addGas k low) hst' found']
      simp only [accessAddress]
      split <;> exact follows_map_charge fun _ => rfl
    · rintro evm ⟨hc, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
      have found : accountCode evm (toAddressMasked word) = .ok c := by
        simp [accountCode, hs, hcode, Except.mapError]
      rw [extcodesizeStep_of_accountCode hst found]
      simp only [accessAddress, hfork, ↓reduceIte, hss, hg, charge_nat hgas]
      exact ⟨_, rfl, hc, hj, hm, by simp [hpc], rfl, hmem, rfl, hrun, herr, hout, by simp [hs],
        by simp, hrd⟩

end LinkVerify.Tac

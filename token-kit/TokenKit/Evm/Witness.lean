import UsdtVerify.Evm.Sample
import TokenKit.Evm.Rules

/-!
# Tools for a concrete witness of a success path

A path theorem has many hypotheses. A witness is one concrete call on one concrete state where
all of them hold, so the theorem is not empty. The lemmas here discharge the usual conditions for
a call whose amount word is 0 and read the argument words of call data built with upstream's
`data1`, `data2`, `data3` (UsdtVerify/Evm/Sample.lean).

Nothing here is about one token.
-/

namespace TokenKit.Witness

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm

/-- The check of SafeMath `add` passes when the added word is 0. -/
theorem nolt (x : U256) : isZero (isZero (isZero (lessThan (add x 0) x))) ≠ 0 := by
  have h : add x 0 = x := by simp [add]
  rw [h]
  have h2 : lessThan x x = 0 := by simp [lessThan]
  rw [h2]
  decide

/-- The check of SafeMath `sub` passes when the subtracted word is 0. -/
theorem nogt (x : U256) : isZero (isZero (isZero (greaterThan 0 x))) ≠ 0 := by
  have h2 : greaterThan 0 x = 0 := by simp [greaterThan]
  rw [h2]
  decide

/-- `if (v > a)` as compiled is not taken when `v` is 0. -/
theorem nogt1 (x : U256) : isZero (greaterThan 0 x) ≠ 0 := by
  have h2 : greaterThan 0 x = 0 := by simp [greaterThan]
  rw [h2]
  decide

/-- The check of SafeMath `add` passes when the sum is below `2^256`. -/
theorem noov (x v : U256) (h : x.toNat + v.toNat < 2 ^ 256) :
    isZero (isZero (isZero (lessThan (add x v) x))) ≠ 0 := by
  have e : lessThan (add x v) x = 0 := by
    refine if_neg ?_
    simp only [add, BitVec.toNat_add]
    omega
  rw [e]
  decide

/-- `require(a == b)` as compiled passes for equal words. -/
theorem eq2 (x : U256) : isZero (isZero (equal x x)) ≠ 0 := by
  have e : equal x x = 1 := by unfold equal; exact if_pos rfl
  rw [e]
  decide

/-- `require(x >= 0)` as solc 0.4 compiles it (three ISZERO over LT) passes. -/
theorem nolt0 (x : U256) : isZero (isZero (isZero (lessThan x 0))) ≠ 0 := by
  have h2 : lessThan x 0 = 0 := by simp [lessThan]
  rw [h2]
  decide

/-- `a == b` as a jump condition is 0 for two different words. -/
theorem eq2_ne {a b : U256} (h : a ≠ b) : isZero (isZero (equal a b)) = 0 := by
  have e : equal a b = 0 := by unfold equal; exact if_neg h
  rw [e]
  decide

/-- `a == b` as a jump condition is not 0 for the same word. -/
theorem eq2_eq {a b : U256} (h : a = b) : isZero (isZero (equal a b)) ≠ 0 := by
  have e : equal a b = 1 := by unfold equal; exact if_pos h
  rw [e]
  decide

/-- The address word of the concrete caller `CALLER1` below. -/
abbrev CALLER1W : U256 := 0x0101010101010101010101010101010101010101

/-- `require(w != 0)` as compiled passes for a word that is not 0. -/
theorem ne3 (w : U256) (hw : w ≠ 0) : isZero (isZero (isZero (equal w 0))) ≠ 0 := by
  have e : equal w 0 = 0 := by unfold equal; exact if_neg hw
  rw [e]
  decide

variable {sel : ByteArray}

theorem arg1_data1 (hs : sel.size = 4) (a : U256) : loadWord (data1 sel a) 4 32 = a :=
  wordArg_data1 hs a

theorem arg1_data2 (hs : sel.size = 4) (a b : U256) : loadWord (data2 sel a b) 4 32 = a := by
  have := loadWord_append_wordBytes_append sel (wordBytes b) a
  rw [hs] at this
  exact this

theorem arg2_data2 (hs : sel.size = 4) (a b : U256) : loadWord (data2 sel a b) 36 32 = b :=
  wordArg_data2_1 hs a b

theorem arg1_data3 (hs : sel.size = 4) (a b c : U256) : loadWord (data3 sel a b c) 4 32 = a := by
  have := loadWord_append_wordBytes_append sel (wordBytes b ++ wordBytes c) a
  rw [hs, ← ByteArray.append_assoc] at this
  exact this

theorem arg2_data3 (hs : sel.size = 4) (a b c : U256) : loadWord (data3 sel a b c) 36 32 = b := by
  have := loadWord_append_wordBytes_append (sel ++ wordBytes a) (wordBytes c) b
  rw [ByteArray.size_append, hs, size_wordBytes] at this
  exact this

theorem arg3_data3 (hs : sel.size = 4) (a b c : U256) : loadWord (data3 sel a b c) 68 32 = c :=
  wordArg_data3_2 hs a b c

/-- A concrete caller: the address whose 20 bytes are 1. -/
def CALLER1 : Address := Vector.replicate 20 1

/-- The address word of `CALLER1` is not 0. -/
theorem caller1_ne : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    CALLER1.toU256 ≠ 0 := by decide

/-- The address word of `CALLER1`. -/
theorem caller1_word : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    CALLER1.toU256 = CALLER1W := by decide

end TokenKit.Witness

import TokenKit.Evm.Witness
import TokenKit.Evm.Readable
import TokenKit.Evm.SafeL

/-!
# Tools for a concrete witness of a path of optimized code

- `data4 sel a b c d`: call data with a 4-byte selector and four argument words, with its size,
  its selector and its four argument words (`data1`, `data2`, `data3` are upstream's).
- `Witness.endsL_of_reaches`: a frame that reaches a stopped frame by steps of `Logic.StepG` is
  run to it by the loop of the interpreter, for every message runner and every bound that holds
  its gas (EthLib's `runFrame_of_reaches`). So a witness of a token in the logic mode is a run
  of the real loop.
- `Witness.caller1_toU256`: the word of the concrete caller `CALLER1`.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- A 4-byte selector and four argument words. -/
def data4 (sel : ByteArray) (a b c d : U256) : ByteArray :=
  sel ++ wordBytes a ++ wordBytes b ++ wordBytes c ++ wordBytes d

variable {sel : ByteArray}

theorem size_data4 (hs : sel.size = 4) (a b c d : U256) : (data4 sel a b c d).size = 132 := by
  simp [data4, ByteArray.size_append, size_wordBytes, hs]

theorem selector_data4 (hs : sel.size = 4) (a b c d : U256) :
    selector (data4 sel a b c d) = selector sel := by
  rw [data4, selector_append _ (by simp only [ByteArray.size_append, hs]; omega),
    selector_append _ (by simp only [ByteArray.size_append, hs]; omega),
    selector_append _ (by rw [ByteArray.size_append, hs]; omega),
    selector_append _ (by simp [hs])]

namespace Witness

theorem arg1_data4 (hs : sel.size = 4) (a b c d : U256) :
    loadWord (data4 sel a b c d) 4 32 = a := by
  have := loadWord_append_wordBytes_append sel (wordBytes b ++ wordBytes c ++ wordBytes d) a
  rw [hs, ← ByteArray.append_assoc, ← ByteArray.append_assoc] at this
  exact this

theorem arg2_data4 (hs : sel.size = 4) (a b c d : U256) :
    loadWord (data4 sel a b c d) 36 32 = b := by
  have := loadWord_append_wordBytes_append (sel ++ wordBytes a) (wordBytes c ++ wordBytes d) b
  rw [ByteArray.size_append, hs, size_wordBytes, ← ByteArray.append_assoc] at this
  exact this

theorem arg3_data4 (hs : sel.size = 4) (a b c d : U256) :
    loadWord (data4 sel a b c d) 68 32 = c := by
  have := loadWord_append_wordBytes_append (sel ++ wordBytes a ++ wordBytes b) (wordBytes d) c
  rw [ByteArray.size_append, ByteArray.size_append, hs, size_wordBytes] at this
  exact this

theorem arg4_data4 (hs : sel.size = 4) (a b c d : U256) :
    loadWord (data4 sel a b c d) 100 32 = d := by
  have := loadWord_append_wordBytes (sel ++ wordBytes a ++ wordBytes b ++ wordBytes c) d
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_append, hs,
    size_wordBytes] at this
  exact this

/-- The word of the concrete caller `CALLER1`. -/
theorem caller1_toU256 : CALLER1.toU256 = CALLER1W := by decide

variable {fork : Fork}

/-- A frame that reaches a stopped frame by steps of `Logic.StepG` is run to it by the loop of
the interpreter, for every message runner and every bound that holds its gas. -/
theorem endsL_of_reaches {evm s : Evm fork Nat} (hr : Reaches (Logic.StepG fork) evm s)
    (hrun : s.running = false) {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (within : GasMeter.gasHeld evm.gas ≤ bound) : EndsL runChild evm s :=
  ⟨within, runFrame_of_reaches (hr.mono And.left) hrun within⟩

end Witness

end TokenKit

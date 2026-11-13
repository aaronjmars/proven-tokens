import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Opt
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# Rules that LINK needs and the shared library does not have yet

Nothing here is about LINK alone: every lemma is a candidate for the kit (see `status.json`,
`to_merge_into_kit`). They live here because the shared library is owned by another line of
work while this token is built.

Solidity 0.4 with the optimizer (the dispatcher of LINK):

- `and_div_selector`, `div_and_selector`: the selector word, `(calldata[0] / 2^224) & 0xffffffff`
  in either order of AND, is the number `selector`.
- `size_isZero_zero`, `size_isZero_ne`: the test `CALLDATASIZE == 0`.
- `equal_key_zero_r`: EQ of a word that is no key with a key, the word first.
-/

namespace TokenKit

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

/-- The selector word of Solidity 0.4: the mask on the left. -/
theorem and_div_selector (data : ByteArray) :
    bitwiseAnd (4294967295 : U256) (div (loadWord data 0 32)
      (26959946667150639794667015087019630673637144422540572481103610249216 : U256)) =
      BitVec.ofNat 256 (selector data) :=
  selector_word data

/-- The selector word of Solidity 0.4: the mask on the right. -/
theorem div_and_selector (data : ByteArray) :
    bitwiseAnd (div (loadWord data 0 32)
      (26959946667150639794667015087019630673637144422540572481103610249216 : U256))
      (4294967295 : U256) = BitVec.ofNat 256 (selector data) := by
  rw [← and_div_selector]
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

/-- With call data that is not empty, the test `CALLDATASIZE == 0` is 0. -/
theorem size_isZero_zero {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 256) :
    isZero (BitVec.ofNat 256 n) = 0 := by
  apply isZero_eq_zero_iff.mpr
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  simp at this
  omega

/-- With no call data, the test `CALLDATASIZE == 0` is not 0. -/
theorem size_isZero_ne {n : Nat} (h : n < 1) : isZero (BitVec.ofNat 256 n) ≠ 0 := by
  have h0 : n = 0 := by omega
  subst h0
  decide

/-- EQ of a word that is not in a list with a key of the list is 0, the word first. -/
theorem equal_key_zero_r {x k : U256} {l : List U256} (h : x ∉ l) (hk : k ∈ l) : equal x k = 0 :=
  if_neg (fun (e : x = k) => h (e ▸ hk))

end TokenKit

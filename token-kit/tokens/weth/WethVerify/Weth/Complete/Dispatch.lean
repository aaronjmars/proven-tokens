import UsdtVerify.Evm.GasRules
import WethVerify.Weth.Enter

/-!
# The three cases of the dispatcher

Every call data falls in one of three cases (`selector_cases`): fewer than 4 bytes; 4 bytes or
more whose selector is no key of the table; or 4 bytes or more whose selector is the key of entry
`i` of the table, for some `i : Fin 11`. The first two run the fallback (`enterShort`,
`enterOther` of Weth/Enter.lean), the third the function of the entry (`enter`).

Unlike a token with no fallback, a successful run of WETH9 says nothing of the call data: the
fallback is payable and takes any call data.
-/

namespace WethVerify.Complete

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG SpecG.not_ok StepG
open UsdtVerify.Gas
open GasCosts

/-- Every call data has fewer than 4 bytes, or a selector that is no key of the table, or the
selector of entry `i` of the table. -/
theorem selector_cases (data : ByteArray) :
    data.size < 4 ∨
      (4 ≤ data.size ∧ BitVec.ofNat 256 (selector data) ∉ ENTRIES.map Prod.fst) ∨
      (4 ≤ data.size ∧ ∃ i : Fin 11, selector data = ENTRIES[i].1.toNat) := by
  by_cases hs : data.size < 4
  · exact .inl hs
  by_cases hm : BitVec.ofNat 256 (selector data) ∈ ENTRIES.map Prod.fst
  · refine .inr (.inr ⟨by omega, ?_⟩)
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hlen : ENTRIES.length = 11 := rfl
    refine ⟨⟨i, hlen ▸ hi⟩, ?_⟩
    have hlt : selector data < 2 ^ 256 :=
      Nat.lt_of_lt_of_le (selector_lt data) (by decide)
    show selector data = (ENTRIES[i]).1.toNat
    rw [hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · exact .inr (.inl ⟨by omega, hm⟩)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

theorem halted_true_error {out : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} (e : Evm fork Nat) (h : Halted true out g st ss e) : e.error ≠ none := by
  rw [h.2.1]; simp

end WethVerify.Complete

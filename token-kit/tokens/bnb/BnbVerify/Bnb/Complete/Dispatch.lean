import UsdtVerify.Evm.GasRules
import UsdtVerify.Evm.Exact
import BnbVerify.Bnb.Spec.Dispatch

/-!
# Completeness of the dispatcher

Every call data falls in one of three cases (`selector_cases`): empty; not empty with a selector
that is no key of the table; or the selector is the key of entry `i` of the table, for some
`i : Fin 15`. The selector of a call data of 1 to 3 bytes is read with zeros after its end, as
the bytecode reads it.

The fallback and the nonpayable revert of `Bnb/Spec/Dispatch.lean` are stated over `StepG`; with
`ok_exactE` and `SpecG.not_okE` they cover every gas, out of gas included.

- `Stopped c gas state substate s`: the frame `s` is the end of a run that stopped with no
  output, the state and the substate it started with, and `c` gas spent.
- `ends_ok_dispatch`: from Berlin, a run from pc 0 that ends with no error is one of: the
  fallback on an empty call data (51 gas), the fallback on an unknown selector (404 gas), or a
  call of entry `i` of the table with no value.
- `ends_ok_fallback`: a run that ends with no error on a call data that is empty or names no
  function stopped in the fallback: nothing written, nothing logged, for any call value.
-/

namespace BnbVerify.Complete

open UsdtVerify

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic hiding SpecG SpecG.not_ok StepG
open UsdtVerify.Gas
open UsdtVerify.Complete
open GasCosts

/-- Every call data is empty, or has a selector that is no key of the table, or has the selector
of entry `i` of the table. -/
theorem selector_cases (data : ByteArray) :
    data.size = 0 ∨
      (1 ≤ data.size ∧ BitVec.ofNat 256 (selector data) ∉ ENTRIES.map Prod.fst) ∨
      (1 ≤ data.size ∧ ∃ i : Fin 15, selector data = ENTRIES[i].1.toNat) := by
  by_cases hs : data.size = 0
  · exact .inl hs
  by_cases hm : BitVec.ofNat 256 (selector data) ∈ ENTRIES.map Prod.fst
  · refine .inr (.inr ⟨by omega, ?_⟩)
    obtain ⟨e, he, hk⟩ := List.mem_map.mp hm
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hlen : ENTRIES.length = 15 := rfl
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

/-- The end of a run that stopped with no output, nothing written, nothing logged, and `c` gas
spent. -/
def Stopped (c gas : Nat) (state : State.TransactionState) (substate : Substate)
    (s : Evm fork Nat) : Prop :=
  c ≤ gas ∧ s.output = ByteArray.empty ∧ s.gas = gas - c ∧ s.state = state ∧
    s.substate = substate

/-- From Berlin, a fresh frame of `CODE` at pc 0, with any gas and any call value, and call data
of size below `2^256`: if a loop of steps from it ends with no error (`Ends`), then either the
call data is empty and the run stopped in the fallback for 51 gas, or the selector is no key of
the table and the run stopped in the fallback for 404 gas, or the selector is the key of some
entry `i` of the table and the call value is 0. -/
theorem ends_ok_dispatch (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm) {s : Evm fork Nat}
    (hrun : Ends fork evm s) (hok : s.error = none) :
    (message.data.size = 0 ∧ Stopped 51 gas state substate s) ∨
      (1 ≤ message.data.size ∧
        BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst ∧
        Stopped 404 gas state substate s) ∨
      (1 ≤ message.data.size ∧ message.value = 0 ∧
        ∃ i : Fin 15, selector message.data = ENTRIES[i].1.toNat) := by
  rcases selector_cases message.data with hs | ⟨hs, hunk⟩ | ⟨hs, i, hi⟩
  · obtain ⟨hcg, -, ho, hgas, hst, hss⟩ := ok_exactE (B := 51) (cost := 51) (by omega)
      (fun g hg => Fallback.spec_empty hs hg) start hrun hok
    exact .inl ⟨hs, hcg, ho, hgas, hst, hss⟩
  · obtain ⟨hcg, -, ho, hgas, hst, hss⟩ := ok_exactE (B := 404) (cost := 404) (by omega)
      (fun g hg => Fallback.spec_unknown hs hsize' hunk hg) start hrun hok
    exact .inr (.inl ⟨hs, hunk, hcg, ho, hgas, hst, hss⟩)
  · refine .inr (.inr ⟨hs, ?_, i, hi⟩)
    by_cases hv : message.value = 0
    · exact hv
    exact absurd hok (SpecG.not_okE (Nonpayable.spec hfork hs hsize' i hi hv
      (gas := gas + (84 + 22 * (i.val + 1))) (by omega)) halted_true_error
      (at_addGas start _) hrun)

/-- A run that ends with no error on a call data that is empty, or whose selector is no key of
the table, stopped in the fallback: no output, nothing written, nothing logged. The call value is
free: the contract accepts ETH on these calls. -/
theorem ends_ok_fallback (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hno : message.data.size = 0 ∨
      BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)
    {gas : Nat} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm) {s : Evm fork Nat}
    (hrun : Ends fork evm s) (hok : s.error = none) :
    s.output = ByteArray.empty ∧ s.state = state ∧ s.substate = substate ∧
      (s.gas = gas - 51 ∨ s.gas = gas - 404) := by
  rcases ends_ok_dispatch hfork hsize' start hrun hok with
    ⟨-, -, ho, hg, hst, hss⟩ | ⟨-, -, -, ho, hg, hst, hss⟩ | ⟨hs, -, i, hi⟩
  · exact ⟨ho, hst, hss, .inl hg⟩
  · exact ⟨ho, hst, hss, .inr hg⟩
  · exfalso
    rcases hno with h0 | hunk
    · omega
    · apply hunk
      have hlt : selector message.data < 2 ^ 256 :=
        Nat.lt_of_lt_of_le (selector_lt message.data) (by decide)
      refine List.mem_map.mpr ⟨ENTRIES[i], List.getElem_mem _, ?_⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      exact hi.symm

/-- The same as `ends_ok_dispatch` for the loop of the interpreter, with any gas bound and any
message runner. -/
theorem runFrame_ok_dispatch (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    {gas : Nat} {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) {s : Evm fork Nat}
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    (message.data.size = 0 ∧ Stopped 51 gas state substate s) ∨
      (1 ≤ message.data.size ∧
        BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst ∧
        Stopped 404 gas state substate s) ∨
      (1 ≤ message.data.size ∧ message.value = 0 ∧
        ∃ i : Fin 15, selector message.data = ENTRIES[i].1.toNat) :=
  ends_ok_dispatch hfork hsize' start (Ends.run hrun) hok

end BnbVerify.Complete

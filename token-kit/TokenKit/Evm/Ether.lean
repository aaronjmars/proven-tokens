import TokenKit.Evm.Solvent
import EthLib.Execution.Proofs.State.Frame
import EthLib.Execution.Proofs.Evm.Logic.Callee
import EthLib.Execution.Proofs.Evm.Call.Parent

/-!
# Ether that the message layer moves into and out of a contract with code

From Paris, a change of an account deletes it when it is left empty (no nonce, no balance, no
code), and with it its storage. An account with code is never empty, so a move of ether into or
out of it keeps its storage.

- `moveEther_into`: a move of `v` wei from another account into `C`, which has code: every
  storage word of `C` is kept and its ether grows by `v` (no wrap).
- `moveEther_outOf`: a move of `v` wei out of `C`, which has code, to another account: every
  storage word of `C` is kept and its ether falls by `v` (which it had).
- `solvent_moveEther_outOf`: so `Backed b v C` before gives `Solvent b C` after.
- `backed_moveEther_into`: and `Solvent b C` before a move in gives `Backed b v C` after.
- `noCode_message`: from Paris, a message to an address with no code and no precompile, that the
  runner of the interpreter ends with no error, ends in the state of its caller (no value moved)
  or in that state after the move of its value.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH EMPTY_ACCOUNT Account)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {tx tx' : State.TransactionState} {C other : Address} {v : U256}

/-- An account with code is recorded in the state. -/
theorem getAccountOptional_ne_none_of_code
    (h : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH) : tx.getAccountOptional C ≠ none := by
  intro hn
  apply h
  unfold getAccount
  rw [hn]
  rfl

/-- A move of ether into an account with code keeps its storage and adds to its ether. -/
theorem moveEther_into (hne : other ≠ C) (hcode : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork other C v = .ok tx') :
    (∀ n, storageAt tx' C n = storageAt tx C n) ∧
      (etherOf tx' C).toNat = (etherOf tx C).toNat + v.toNat := by
  obtain ⟨-, hfit, -, hrec, -⟩ := moveEther_eq_ok hne h
  have hc' : (tx'.getAccount C).codeHash ≠ EMPTY_CODE_HASH := by
    rw [hrec]
    exact hcode
  refine ⟨fun n => ?_, ?_⟩
  · unfold moveEther at h
    cases hm : tx.modifyState fork other (Account.debit other v) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok mid =>
      simp only [hm, bind, Except.bind] at h
      unfold storageAt
      rw [getStorage_modifyState h C _,
        if_neg (fun k => getAccountOptional_ne_none_of_code hc' k.2),
        getStorage_modifyState hm C _, if_neg (fun k => hne k.1.symm)]
  · unfold etherOf
    rw [hrec]
    show ((tx.getAccount C).balance + v).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hfit]

/-- A move of ether out of an account with code keeps its storage and takes from its ether. -/
theorem moveEther_outOf (hne : C ≠ other) (hcode : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork C other v = .ok tx') :
    (∀ n, storageAt tx' C n = storageAt tx C n) ∧ v.toNat ≤ (etherOf tx C).toNat ∧
      (etherOf tx' C).toNat = (etherOf tx C).toNat - v.toNat := by
  obtain ⟨hfunds, -, hsend, -, -⟩ := moveEther_eq_ok hne h
  have hle : v.toNat ≤ (tx.getAccount C).balance.toNat := by
    simpa [BitVec.lt_def] using hfunds
  have hc' : (tx'.getAccount C).codeHash ≠ EMPTY_CODE_HASH := by
    rw [hsend]
    exact hcode
  refine ⟨fun n => ?_, hle, ?_⟩
  · unfold moveEther at h
    cases hm : tx.modifyState fork C (Account.debit C v) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok mid =>
      simp only [hm, bind, Except.bind] at h
      obtain ⟨-, -, -, hrest⟩ := modifyState_eq_ok h
      have hmid : (mid.getAccount C).codeHash ≠ EMPTY_CODE_HASH := by
        rw [← hrest C hne]
        exact hc'
      unfold storageAt
      rw [getStorage_modifyState h C _, if_neg (fun k => hne k.1),
        getStorage_modifyState hm C _,
        if_neg (fun k => getAccountOptional_ne_none_of_code hmid k.2)]
  · unfold etherOf
    rw [hsend]
    show ((tx.getAccount C).balance - v).toNat = _
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]

namespace Supply

variable {b : U256}

/-- A move of `v` wei out of a contract with code: backed by `v` to spare before, solvent after. -/
theorem solvent_moveEther_outOf (hne : C ≠ other)
    (hcode : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork C other v = .ok tx') (hb : Backed b v C tx) : Solvent b C tx' := by
  obtain ⟨hs, hle, he⟩ := moveEther_outOf hne hcode h
  unfold Backed at hb
  unfold Solvent
  rw [sumBal_congr hs, he]
  omega

/-- A move of `v` wei into a contract with code: solvent before, backed with `v` to spare after. -/
theorem backed_moveEther_into (hne : other ≠ C)
    (hcode : (tx.getAccount C).codeHash ≠ EMPTY_CODE_HASH)
    (h : tx.moveEther fork other C v = .ok tx') (hb : Solvent b C tx) : Backed b v C tx' := by
  obtain ⟨hs, he⟩ := moveEther_into hne hcode h
  unfold Solvent at hb
  unfold Backed
  rw [sumBal_congr hs, he]
  omega

end Supply

/-- From Paris, a message to an address with no code and no precompile that the runner of the
interpreter ends with no error: when it moves a value, the move succeeds and the end state is
the state after the move; when it moves none, the end state is the state of the caller. -/
theorem noCode_message (hparis : .paris ≤ fork) {bound : Nat} {caller child : Evm fork Nat}
    {msg : Message fork} {to : Address} (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = .empty) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) :
    (msg.shouldTransferValue = true ∧ msg.value ≠ 0 →
        caller.state.moveEther fork msg.caller msg.currentTarget msg.value = .ok child.state) ∧
      (¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) → child.error = none →
        child.state = caller.state) := by
  obtain ⟨lt, child', hrun, rfl⟩ := hran
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  refine ⟨fun ht => ?_, fun ht herr => ?_⟩
  · obtain ⟨moved, hm, -, hs⟩ :=
      (meets_paidNoCode (fork := fork) bound).ok caller msg lt child' hrun hcode
        (by rw [htarget]; rfl) noPre ht
    rw [hst] at hm
    rw [hs]
    exact hm
  · simp only [processRunner, htarget] at hrun
    obtain ⟨stopped, ran, hse, hss⟩ := runFrame_startFrame_empty (fork := fork)
      (state := startState fork msg caller.state) (substate := caller.substate.child)
      (runChild := processRunner fork msg.gas) (within := Nat.le_refl _) hcode
    have hmap := processMessage_map_val ht noPre ran
    rw [hrun] at hmap
    have he : child'.val = rollbackOnError caller.state stopped := Except.ok.inj hmap
    rw [he, rollbackOnError_of_error_eq_none hse, hss, hst]

end TokenKit

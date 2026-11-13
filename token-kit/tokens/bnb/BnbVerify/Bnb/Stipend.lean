import BnbVerify.Bnb.Seq
import TokenKit.Evm.Move
import TokenKit.Evm.Stipend

/-!
# withdrawEther with no assumption on the runner: the owner is ANY code

`Withdraw.supply_withdrawEther` and the sequence theorems of Bnb/Seq.lean take the local
assumption `Withdraw.KeepsInv runChild message S` on the runner: the one message that the CALL of
`withdrawEther` sends, when it ends with no error, keeps `Inv`. Bnb/Sanity/Withdraw.lean proves it
for EthLib's real runner only for an owner with no code or the code STOP.

This file proves it for EthLib's real runner (`processRunner`, EthLib's `processMessage`) and
EVERY code of the owner, the way WETH does for its `withdraw` (Weth/Reenter.lean). Written by
hand (not generated).

Why it holds. The CALL of `withdrawEther` (pc 3010) asks for the gas `2300 * (amount == 0)`
(`Withdraw.askedWord`, read from the bytes by the generated path `withdrawEther_p2`): 0 when the
amount is not 0 (the message then gets the stipend of 2300) and 2300 when the amount is 0 (no
stipend). So the message gets at most 2300 gas in both cases; this is the last field of
`Withdraw.Payout` (`msg.gas ≤ 2300`, proved in `withdrawEther_run` from `callGas_subCall_le` and
`Withdraw.askedWord_le`). `TokenKit.Stipend.processMessage_quiet` proves, by induction over
EthLib's interpreter, that from Istanbul a message with at most 2300 gas that ends with no error
changes no account and no storage word apart from the move of its own value (SSTORE fails at
2300 gas or less, a CALL with value costs 9000, CREATE 32000, SELFDESTRUCT 5000). The owner may
call back into BNB (a warm CALL costs 100): that inner run is one of the messages of the
induction, with less than 2300 gas, so it cannot write a storage word either. The move of the
value keeps the storage of a contract that holds code (TokenKit's `moveEther_keeps_storage`).
`Inv` reads the storage of the contract only.

- `processRunner_keepsInv_any`: from Istanbul, for every bound, every message and every state
  where the account of the contract holds code, `KeepsInv (processRunner fork bound) message S`.
  The two hypotheses, and why each one is needed:
  - `hist` (`.istanbul ≤ fork`): the hypothesis of `processMessage_quiet`. EthLib's SSTORE fails
    with 2300 gas or less from Istanbul (EIP-2200); before, SSTORE could run inside the stipend.
    There is no upper bound on the fork for this theorem.
  - `hC` (the code hash of the account of the contract is not the hash of no code): the message
    moves its value from the contract to the owner, and EthLib's `moveEther` may delete an
    account that is left empty; an account that holds code is never empty, so its storage stays.
    It is the account whose code runs, so on a chain it holds. `process_step` has the same
    hypothesis (`hcode`).
  NOT needed here: no hypothesis on the code of the owner, none on an EIP-7702 delegation, none
  that the owner is no precompile (`processMessage_quiet` covers a precompile target and every
  delegation that the callee meets).
- `supply_withdrawEther_process`: `Withdraw.supply_withdrawEther` for `processRunner` with no
  assumption on the runner.
- `process_step_withdraw_process`, `process_step_all_process`, `process_step_inv_all_process`:
  `process_step_withdraw`, `process_step_all` and `process_step_inv_all` of Bnb/Seq.lean with no
  `KeepsInv` hypothesis. The older theorems are kept as they were.

What is still asked for a call of `withdrawEther`, and why:

- `fork < .glamsterdam`: EthLib's rules for the CALL step of the contract itself
  (`TokenKit.call_outcome`, used by `Withdraw.withdrawEther_run`) are proved for the one-counter
  gas rules before Glamsterdam.
- `hdel`: from Prague (`.pectra ≤ fork`), the code of the owner is no EIP-7702 delegation.
  It is still needed, and only for the CALL step of the contract: `call_outcome` does not cover
  a CALL whose target is a delegated account (the step then loads the code of the delegate and
  prices its access). It is not a limit on what the callee does. Before Prague it asks nothing.
- `hcode`: the account of the contract holds code (as above).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace BnbVerify.Withdraw

open UsdtVerify
open TokenKit TokenKit.Complete
open BnbVerify BnbVerify.Paths BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-- From Istanbul, for EthLib's real runner and EVERY code of the owner: the one message that the
CALL of `withdrawEther` sends (`Payout message S`, at most 2300 gas), when it ends with no error,
leaves every storage word of the contract as it was. The owner may call the contract again.
`hC`: the account of the contract holds code. -/
theorem payout_keeps_storage (hist : .istanbul ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState}
    (hC : (S.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {caller : Evm fork Nat} {msg : Message fork} (lt : msg.gas < bound)
    {child : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hch : processRunner (Meter := Nat) fork bound caller msg lt = .ok child)
    (hpay : Payout message S caller msg) (herr : child.val.error = none) (n : U256) :
    storageAt child.val.state message.currentTarget n =
      storageAt caller.state message.currentTarget n := by
  obtain ⟨c, hc, hreads, mcaller, mtarget, mt, mca, mcode, mdata, mval, mdep, mstat, mgas⟩ := hpay
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, mt]
  rw [hp] at hch
  obtain ⟨h1, h2⟩ := Stipend.processMessage_quiet (Meter := Nat) hist msg.gas msg caller.state
    caller.substate.child _ _ rfl mgas (by rw [mt]; rfl) child hch herr
  have hq0 := Stipend.quiet_startState msg caller.state
  by_cases ht : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · obtain ⟨moved, hm, hq⟩ := h1 ht
    have hcodeS : ((startState fork msg caller.state).getAccount message.currentTarget).codeHash ≠
        EMPTY_CODE_HASH := by
      rw [hq0.1, readsAs_getAccount hreads]
      exact hC
    exact ((hq.2 _ _).trans (moveEther_keeps_storage hcodeS hm n)).trans (hq0.2 _ _)
  · exact (h2 ht).2 _ _

/-- From Istanbul, the local assumption of `withdrawEther` is TRUE for EthLib's real runner, for
every bound and EVERY code of the owner, when the account of the contract holds code. No
hypothesis on the owner: any code, a precompile, an EIP-7702 delegation. -/
theorem processRunner_keepsInv_any (hist : .istanbul ≤ fork) {bound : Nat}
    {message : Message fork} {S : State.TransactionState}
    (hC : (S.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    KeepsInv (processRunner (Meter := Nat) fork bound) message S := by
  refine fun caller msg lt child hch hpay herr hinv => ?_
  exact (Supply.inv2_congr (fun n => payout_keeps_storage hist hC lt hch hpay herr n)).mpr hinv

/-- The supply invariant through `withdrawEther` under EthLib's real runner, from Berlin and
before Glamsterdam, with NO assumption on the runner and none on the code that the owner runs.
`hdel`: the code of the owner is no EIP-7702 delegation from Prague (needed by the CALL step of
the contract, `withdrawEther_run`). `hC`: the account of the contract holds code. -/
theorem supply_withdrawEther_process (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hdel : ∀ c, state.getCode (state.getAccount (ownerOf message state)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (hinv : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound
      (processRunner (Meter := Nat) fork bound) evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_withdrawEther hfork hglam hsize' hsel hdel
    (processRunner_keepsInv_any (Nat.le_trans (by decide) hfork) hC) hinv start within hrun hok

end BnbVerify.Withdraw

namespace BnbVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- `process_step_withdraw` with no assumption on the runner. From Paris and before Glamsterdam,
a top-level message to `C` whose code is `CODE` (no precompile, call data below 2^256 bytes) with
the selector of `withdrawEther`, run by EthLib's `processMessage` to the end, is a sequence of
steps of `Calls C`, whatever the code of the owner. `hdel`: the code of the owner is no EIP-7702
delegation from Prague. `hcode`: the account of the contract holds code. -/
theorem process_step_withdraw_process {fork : Fork} (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hdel : ∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
      .ok c → .pectra ≤ fork → delegatedAddress c = none)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    Calls message.currentTarget state ended.val.state :=
  process_step_withdraw hparis hglam hmc noPrecompile hsize hsel hdel
    (Withdraw.processRunner_keepsInv_any (Nat.le_trans (by decide) hparis) hcode) hproc

/-- `process_step_all` with no assumption on the runner. From Paris, EVERY top-level message to
`C` whose code is `CODE` (no precompile, call data below 2^256 bytes, any selector), run by
EthLib's `processMessage` to the end, is a sequence of steps of `Calls C`. `K` (keccak) is asked
only for a selector other than `withdrawEther`; `hw` (before Glamsterdam, and the code of the
owner is no EIP-7702 delegation from Prague) only for the selector of `withdrawEther`. -/
theorem process_step_all_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (K : selector message.data ≠ 0x3bed33ce → Sep (callKeys message))
    (hw : selector message.data = 0x3bed33ce → fork < .glamsterdam ∧
      (∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
        .ok c → .pectra ≤ fork → delegatedAddress c = none))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended) :
    Calls message.currentTarget state ended.val.state :=
  process_step_all hparis hmc noPrecompile hsize hcode K
    (fun hsel => ⟨(hw hsel).1, (hw hsel).2,
      Withdraw.processRunner_keepsInv_any (Nat.le_trans (by decide) hparis) hcode⟩) hproc

/-- `process_step_inv_all` with no assumption on the runner. From Paris, every top-level message
of `CODE` to `C` (any selector, `withdrawEther` to any owner too) that `processMessage` ends keeps
the invariant: `Inv` at its start gives `Inv` at its end (hypotheses of
`process_step_all_process`). -/
theorem process_step_inv_all_process {fork : Fork} (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (K : selector message.data ≠ 0x3bed33ce → Sep (callKeys message))
    (hw : selector message.data = 0x3bed33ce → fork < .glamsterdam ∧
      (∀ c, state.getCode (state.getAccount (Withdraw.ownerOf message state)).codeHash =
        .ok c → .pectra ≤ fork → delegatedAddress c = none))
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state :=
  inv_calls (process_step_all_process hparis hmc noPrecompile hsize hcode K hw hproc) hI

end BnbVerify

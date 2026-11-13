import TokenKit.Evm.Logic
import WethVerify.Weth.Gen

/-!
# totalSupply() of WETH9: the ether balance of the contract

WETH9 keeps no total supply in storage: `totalSupply()` returns `this.balance`. Its code runs
ADDRESS and BALANCE (pc 1648 to 1671), two opcodes outside the simulated set of usdt-verify, so
the generator stops at 1648 (`totalSupply_p1`) and starts again at 1672 (`totalSupplyTail_p0`).
This file proves the four instructions between and joins the three parts.

- `etherOf S a`: the ether balance of the account `a` in the state `S`, as a word.
- `totalSupply_island`: ADDRESS, PUSH20 mask, AND, BALANCE.
- `totalSupply_path`: from pc 0, with the selector of `totalSupply()` and no value: the run
  returns the 32-byte word `etherOf state message.currentTarget`; the state is the start state
  with the account of the contract recorded as read; the substate is the start substate with the
  contract in the accessed addresses; no storage write, no log. The gas is 243 plus the price of
  the account access.
- `ok_totalSupply_exact`: every run of the interpreter loop from pc 0 with that selector that
  ends with no error is that path (so its value is 0), for any gas, any gas bound and any message
  runner.

The revert path (a call with value) is `totalSupply_p0` of the generated file.
-/

set_option autoImplicit false

namespace WethVerify.Paths

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify WethVerify.Blocks WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The four instructions of `this.balance`: ADDRESS, PUSH20 mask, AND, BALANCE. -/
theorem totalSupply_island (hfork : .berlin ≤ fork) {x : U256} {gas : Nat}
    (hg : 8 + accountAccessCost fork (coldAccount substate message.currentTarget) ≤ gas) :
    Logic.HoareG fork
      (At CODE message 1648 [(0 : U256), (436 : U256), x] (memW [(0 : U256), (0 : U256), (96 : U256)])
        gas state substate)
      (At CODE message 1672 [etherOf state message.currentTarget, (0 : U256), (436 : U256), x]
        (memW [(0 : U256), (0 : U256), (96 : U256)])
        (gas - (8 + accountAccessCost fork (coldAccount substate message.currentTarget)))
        (state.recordAccountRead message.currentTarget)
        (accessAccount substate message.currentTarget)) := by
  have hm := toAddressMasked_mask_toU256 message.currentTarget
  step addressL (by code_fact) (by code_fact) (by omega) (by stk_ok)
  step pushR 20 (1461501637330902918203684832716283019655932542975 : U256)
  at_pc 1670
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step balanceL hfork (by code_fact) (by code_fact) (by rw [hm]; gas_ok)
  rw [hm]
  exact Gas.Triple.lift (restate (by decide) rfl rfl (by gas_ok) rfl rfl)

/-- The success path of `totalSupply()`: it returns the ether balance of the contract. -/
theorem totalSupply_path (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hc1 : isZero message.value ≠ 0) {gas : Nat}
    (hg : 243 + accountAccessCost fork (coldAccount substate message.currentTarget) ≤ gas) :
    Logic.SpecG fork (At CODE message 0 [] .empty gas state substate)
      (Halted false (wordBytes (etherOf state message.currentTarget))
        (gas - (243 + accountAccessCost fork (coldAccount substate message.currentTarget)))
        (state.recordAccountRead message.currentTarget)
        (accessAccount substate message.currentTarget)) := by
  step totalSupply_p1 hfork hsize hsize' hsel hc1 (by omega)
  step totalSupply_island hfork (by omega)
  exact Gas.Triple.lift (haltGas (totalSupplyTail_p0 hfork (by omega)) (by omega))

/-- Every successful run of `totalSupply()`: no value, and the output, gas, state and substate
of `totalSupply_path`. -/
theorem ok_totalSupply_exact (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
      243 + accountAccessCost fork (coldAccount substate message.currentTarget) ≤ gas ∧
      s.output = wordBytes (etherOf state message.currentTarget) ∧
      s.gas = gas - (243 + accountAccessCost fork (coldAccount substate message.currentTarget)) ∧
      s.state = state.recordAccountRead message.currentTarget ∧
      s.substate = accessAccount substate message.currentTarget := by
  by_cases hc1 : isZero message.value = 0
  · exact (no_okE (B := 153) (fun g hg => totalSupply_p0 hfork hsize hsize' hsel hc1 (by omega))
      (fun _ e h => halted_true_error e h) start (Ends.run hrun) hok).elim
  · obtain ⟨hcg, -, ho, hgas, hst, hss⟩ := ok_exactL
      (B := 243 + accountAccessCost fork (coldAccount substate message.currentTarget))
      (fun g hg => totalSupply_path hfork hsize hsize' hsel hc1 hg) start within hrun hok
    exact ⟨hc1, hcg, ho, hgas, hst, hss⟩

end WethVerify.Paths

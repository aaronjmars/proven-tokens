import WbtcVerify.Wbtc.SeqLocal
import WbtcVerify.Wbtc.Gen.PTotalSupply

/-!
# The run-local conditions hold on real runs (they are not empty)

Written by hand (not generated). `AnyLocal.lean` and `SeqLocal.lean` ask the condition `CleanW`
of a run of EthLib's interpreter. Here it is machine-checked on real runs of the code of WBTC:
every call `totalSupply()` with no value and enough gas, to any account `C` that runs the code,
from any state and any caller.

- `not_sent_totalSupply`: the frame of such a call sends no message (it runs to its end under
  every runner, by the path theorem `totalSupply_p1`).
- `cleanW_totalSupply`: for WBTC at the target of the call, the run is clean as soon as
  `Sep (callKeys message)` holds for that ONE message: the run-local condition is then exactly
  upstream's local hypothesis, nothing more.
- `cleanW_totalSupply_other`: for WBTC at any OTHER address `L`, the run is clean with no
  hypothesis at all (nothing enters `L`, nothing is deposited): `CleanW` is satisfiable outright.
- `process_good_totalSupply`: so `process_good_local` applies to these runs.

Not covered: a machine-checked instance of `CleanW` for a run of `reclaimToken` against a
concrete token. It needs the list of the messages that the frame of `reclaimToken` sends
(`Trace.Sent`), which the stream "reclaim" states as two `Ran` facts (existence), not as "these
two and no other"; see work/findings/reenter.json.
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit
open WbtcVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {meter : Nat}

/-- The frame of a call `totalSupply()` with no value and enough gas sends no message, under any
runner. -/
theorem not_sent_totalSupply (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0)
    (hg : (272 + (slotCost (coldIn substate message.currentTarget (1 : U256)))) ≤ meter)
    {evm0 : Evm fork Nat} (fo : Trace.FrameOf message state substate meter evm0)
    {bound : Nat} (r : MessageRunner fork Nat bound) (c : Evm fork Nat) (m : Message fork) :
    ¬ Trace.Sent r evm0 c m := by
  obtain ⟨-, state1, hst, rfl⟩ := fo
  have ht : ¬(message.shouldTransferValue = true ∧ message.value ≠ 0) := fun h => h.2 hval
  have hsub : Trace.startSub message substate = substate := by
    unfold Trace.startSub
    rw [ite_eq_right_of_eq_false _ _ (eq_false ht)]
  rw [hsub]
  have hc1 : (isZero message.value) ≠ 0 := by rw [hval]; decide
  refine Trace.not_sent_of_specG
    (totalSupply_p1 (fork := fork) (message := message) (state := state1) (substate := substate)
      hfork hsize hsize' hsel hc1 hg) ?_ r c m
  exact ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- For WBTC at the target of a call `totalSupply()`: the run is clean as soon as the local
hypothesis `Sep (callKeys message)` of that one message holds. -/
theorem cleanW_totalSupply (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0)
    (hg : (272 + (slotCost (coldIn substate message.currentTarget (1 : U256)))) ≤ meter)
    (hsep : Sep (callKeys message)) :
    CleanW message.currentTarget message state substate meter :=
  Trace.clean_of_no_sent
    (fun _ fo c m => not_sent_totalSupply hfork hcode hsize hsize' hsel hval hg fo _ c m)
    (fun _ => hsep)

/-- For WBTC at another address `L` than the target of a call `totalSupply()`: the run is clean,
with no hypothesis on keccak at all. -/
theorem cleanW_totalSupply_other (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0)
    (hg : (272 + (slotCost (coldIn substate message.currentTarget (1 : U256)))) ≤ meter)
    {L : Address} (hne : message.currentTarget ≠ L) :
    CleanW L message state substate meter :=
  Trace.clean_of_no_sent
    (fun _ fo c m => not_sent_totalSupply hfork hcode hsize hsize' hsel hval hg fo _ c m)
    (fun h => absurd h hne)

/-- `process_good_local` on a real run: a call `totalSupply()` that `processMessage` ends leaves
a good state good, under the local hypothesis of that one message only. -/
theorem process_good_totalSupply (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hcode : message.code = CODE) (htarget : message.target.isSome = true)
    (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0)
    (hg : (272 + (slotCost (coldIn substate message.currentTarget (1 : U256)))) ≤ meter)
    (hsep : Sep (callKeys message))
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (g : GoodWbtc message.currentTarget state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodWbtc message.currentTarget ended.val.state :=
  process_good_local hfork hglam (fun _ => ⟨hcode, htarget, hsize'⟩) g
    (cleanW_totalSupply hfork hcode hsize hsize' hsel hval hg hsep) h

end WbtcVerify

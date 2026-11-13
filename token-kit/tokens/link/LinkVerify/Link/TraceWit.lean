import LinkVerify.Link.SeqLocal
import LinkVerify.Link.Gen.PTotalSupply

/-!
# The run-local conditions on real runs

Written by hand (not generated). `AnyLocal.lean` and `SeqLocal.lean` ask the condition `CleanL`
of a run of EthLib's interpreter. Here it is machine-checked on real runs of the code of LINK:
every call `totalSupply()` with no value and enough gas, to any account `C` that runs the code,
from any state and any caller.

- `not_sent_totalSupply`: the frame of such a call sends no message (it runs to its end under
  every runner, by the path theorem `totalSupply_p1`).
- `cleanL_totalSupply`: for LINK at the target of the call, the run is clean as soon as
  `Sep (callKeys message)` holds for that ONE message: the run-local condition is then exactly
  upstream's local hypothesis, nothing more. This is an implication: `Sep` itself is a fact about
  keccak that is never proved here.
- `cleanL_totalSupply_other`: for LINK at any OTHER address `L`, the run is clean with no
  hypothesis at all (nothing enters `L`, nothing is deposited): `CleanL` holds outright there.
- `process_good_totalSupply`: so `process_good_local` applies to these runs.

A run of `transferAndCall` to a receiver that calls back into the token is in `ReWit/`
(`ReWit/Closed.lean`: `supply_tac_re_frame`, `process_tac_re`, `reenter_closed`): there
`CleanFrameL` and `CleanL` are shown for one concrete run from `Sep` of the four words of that
run, and the reentrancy theorems are applied to it.

Not covered: `CleanL` for a run of `transferAndCall` to any other receiver with code (only the
one receiver `RE` of `ReWit/Re.lean`, amount 1, empty data); `Sep` is not proved for any list.
-/

set_option autoImplicit false

namespace LinkVerify

open UsdtVerify
open TokenKit
open LinkVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {meter : Nat}

/-- The frame of a call `totalSupply()` with no value and enough gas sends no message, under any
runner. -/
theorem not_sent_totalSupply (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0) (hg : 214 ≤ meter)
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

/-- For LINK at the target of a call `totalSupply()`: the run is clean as soon as the local
hypothesis `Sep (callKeys message)` of that one message holds. -/
theorem cleanL_totalSupply (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0) (hg : 214 ≤ meter)
    (hsep : Sep (callKeys message)) :
    CleanL message.currentTarget message state substate meter :=
  Trace.clean_of_no_sent
    (fun _ fo c m => not_sent_totalSupply hfork hcode hsize hsize' hsel hval hg fo _ c m)
    (fun _ => hsep)

/-- For LINK at another address `L` than the target of a call `totalSupply()`: the run is clean,
with no hypothesis on keccak at all. -/
theorem cleanL_totalSupply_other (hfork : .berlin ≤ fork)
    (hcode : message.code = CODE) (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0) (hg : 214 ≤ meter)
    {L : Address} (hne : message.currentTarget ≠ L) :
    CleanL L message state substate meter :=
  Trace.clean_of_no_sent
    (fun _ fo c m => not_sent_totalSupply hfork hcode hsize hsize' hsel hval hg fo _ c m)
    (fun h => absurd h hne)

/-- `process_good_local` on a real run: a call `totalSupply()` that `processMessage` ends leaves
a good state good, under the local hypothesis of that one message only. -/
theorem process_good_totalSupply (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hcode : message.code = CODE) (htarget : message.target.isSome = true)
    (hsize : 1 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hval : message.value = 0) (hg : 214 ≤ meter) (hG : message.gas ≤ GAS_CAP)
    (hsep : Sep (callKeys message))
    {held : GasMeter.gasHeld meter ≤ message.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (g : GoodLink message.currentTarget state)
    (h : processMessage fork message state substate meter held = .ok ended) :
    GoodLink message.currentTarget ended.val.state :=
  process_good_local hfork hglam hG (fun _ => ⟨hcode, htarget, hsize'⟩) g
    (cleanL_totalSupply hfork hcode hsize hsize' hsel hval hg hsep) h

end LinkVerify

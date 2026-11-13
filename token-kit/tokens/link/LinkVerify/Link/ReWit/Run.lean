import LinkVerify.Link.ReWit.Re
import LinkVerify.Link.Sanity.Tac
import LinkVerify.Link.Sanity.Base
import LinkVerify.Link.Gen.PTransfer

/-!
# A real run of transferAndCall with a receiver that calls back into LINK

Written by hand (not generated). Fix of audit 4, LINK-4: a witness run where the receiver of
`transferAndCall` really re-enters the token.

The run. The caller `Witness.CALLER1` calls `transferAndCall(0x1000, 1, "")` on the token at `C`.
The account of the address word 0x1000 holds the code `RE` (`ReWit/Re.lean`). LINK moves 1 token
to 0x1000 and CALLs `onTokenTransfer` there. The code `RE` CALLs back its caller, the token, with
`transfer(0x2000, 1)`. This inner call runs the code of LINK again, inside the outer call: it
moves the token on from 0x1000 to 0x2000. `RE` returns, the outer call returns `true`.

- `re_inner_spec`, `re_inner_runs`: the inner call `transfer(0x2000, 1)` from 0x1000, by the path
  theorem `transfer_p5`, and under `processRunner`.
- `tacCallGas_le`: the gas of `transferAndCall` to the CALL is at most 100000 (empty `bytes`
  argument, before Glamsterdam).
- `tac_call_run_re`: the frame of `transferAndCall` with `tacCallGas + 300000` gas, for every
  runner: the message of its CALL has at least 210000 gas, and the list of the messages that the
  frame sends (`Trace.Sent`): that one, then those of the frame after the CALL.
- `tac_re_core`: THE RUN, three frames deep, on EthLib's real runner `processRunner`, in every
  state `S` where `C` holds the code of LINK, 0x1000 holds `RE`, the caller has `10^27` tokens
  and 0x1000 and 0x2000 have none. The loop of the interpreter ends with no error and the output
  `true`. The end balances show that the inner call happened: the caller has `10^27 - 1`, the
  receiver 0x1000 has 0 (it got 1 and sent it on), and 0x2000 has 1. And the only message that
  enters `C` in the runs that the frame starts is the inner call, whose mapping keys are the
  words 0x1000, 0x2000 and 1 (`Trace.CleanFrame` for every condition `Q` that holds for these
  keys).

Assumed: Paris ≤ fork < Glamsterdam. No hypothesis on keccak is used in this file: the facts on
the slots of the three balances are computed in the kernel (`decide +kernel`).
Not covered: other amounts, other receivers, a receiver that calls back more than once.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace LinkVerify.Sanity

open UsdtVerify
open TokenKit
open LinkVerify LinkVerify.Tac LinkVerify.Paths UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## Words and addresses -/

theorem q1 : bitwiseAnd (0x2000 : U256)
    (1461501637330902918203684832716283019655932542975 : U256) = 0x2000 := by decide

theorem q2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (0x2000 : U256) = 0x2000 := by decide

theorem q3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (1 : U256) = 1 := by decide

/-- The word of the address of the word 0x1000. -/
theorem rcpt_toU256 : (toAddressMasked (0x1000 : U256)).toU256 = 0x1000 := by
  apply BitVec.eq_of_toNat_eq
  rw [EthLib.Base.toNat_toU256_toAddressMasked]
  decide

/-- An address with the word of LINK is no precompile, at any fork. -/
theorem notPrecompile_link {C : Address}
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256)) :
    Precompiles.isPrecompile fork C.toU256.toNat = false := by
  have h : (0x514910771af9ca656af840dff83e8264ecf986ca : U256).toNat =
      0x514910771af9ca656af840dff83e8264ecf986ca := by decide
  rw [hC, h]
  rfl

/-- An address with the word of LINK is not the address of the word 0x1000. -/
theorem rcpt_ne_link {C : Address}
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256)) :
    toAddressMasked (0x1000 : U256) ≠ C := by
  intro h
  have h2 : (toAddressMasked (0x1000 : U256)).toU256 = C.toU256 := congrArg _ h
  rw [rcpt_toU256, hC] at h2
  exact absurd h2 (by decide)

/-- Before Glamsterdam an SSTORE costs at most 22100. -/
theorem writeMax_le (hglam : fork < .glamsterdam) : Gas.writeMax fork ≤ 22100 := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  simp [Gas.writeMax, hng]

/-! ## The inner call: transfer(0x2000, 1) from 0x1000 -/

set_option maxHeartbeats 1000000 in
/-- The inner call, by the path theorem `transfer_p5`. A message with the code of LINK at `C`,
the call data `reData` (`transfer(0x2000, 1)`), no value, from the address word 0x1000, in a
state where the caller `CALLER1` has `10^27 - 1` tokens, 0x1000 has 1 and 0x2000 has 0: from
60000 gas the frame halts normally with the output `true`, in a state where `CALLER1` still has
`10^27 - 1`, 0x1000 has 0 and 0x2000 has 1. -/
theorem re_inner_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {im : Message fork} {St : State.TransactionState} {ss : Substate} {C : Address}
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hct : im.currentTarget = C) (hdata : im.data = reData) (hv : im.value = 0)
    (hstatic : im.isStatic = false) (hcw : im.caller.toU256 = (0x1000 : U256))
    (hacc : hasAccount St C)
    (hb0 : storageAt St C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999)
    (hb1 : storageAt St C (mapSlot (0x1000 : U256) 1) = 1)
    (hb2 : storageAt St C (mapSlot (0x2000 : U256) 1) = 0) {gas : Nat} (hg : 60000 ≤ gas) :
    ∃ (cost : Nat) (st' : State.TransactionState) (ss' : Substate),
      Logic.SpecG fork (At CODE im 0 [] .empty gas St ss)
        (Halted false (wordBytes (1 : U256)) (gas - cost) st' ss') ∧
      storageAt st' C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt st' C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt st' C (mapSlot (0x2000 : U256) 1) = 1 := by
  have hsz : im.data.size = 68 := by rw [hdata]; exact reData_size
  have hsl : selector im.data = 0xa9059cbb := by rw [hdata]; exact reData_sel
  have hA1 : loadWord im.data 4 32 = (0x2000 : U256) := by rw [hdata]; exact reData_arg1
  have hA2 : loadWord im.data 36 32 = (1 : U256) := by rw [hdata]; exact reData_arg2
  have hacc' : hasAccount St im.currentTarget := by rw [hct]; exact hacc
  have hW := writeMax_le hglam
  refine ⟨_, _, _, transfer_p5 (fork := fork) (message := im) (state := St) (substate := ss)
    hfork (by rw [hsz]; decide) (by rw [hsz]; decide) hsl hstatic hacc'
    (by
      simp (disch := supply_side) only
        [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
          Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
          Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
          Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
          Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel)
    (by
      simp (disch := supply_side) only
        [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
          Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add (Nat.le_refl 3345) (_root_.UsdtVerify.slotCost_le _))
              (Nat.le_trans (Gas.writeCost_le hfork _ _ _ _) hW))
            (_root_.UsdtVerify.slotCost_le _))
          (Nat.le_trans (Gas.writeCost_le hfork _ _ _ _) hW)) 2300)
      (by omega)), ?_, ?_, ?_⟩
  · simp (disch := supply_side) only
      [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel
  · simp (disch := supply_side) only
      [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel
  · simp (disch := supply_side) only
      [hv, hsz, hA1, hA2, hcw, hct, hC, g1, g4, q1, q2, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, hb0, hb1, hb2]
      <;> decide +kernel

/-- The inner call under the real runner: `processRunner` does run it, with no error, to a state
with the three balances of `re_inner_spec`. -/
theorem re_inner_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {caller : Evm fork Nat} {im : Message fork} (lt : im.gas < bound) {C : Address}
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hcode : im.code = CODE) (htarget : im.target = some C) (hca : im.codeAddress = some C)
    (hct : im.currentTarget = C) (hdata : im.data = reData) (hv : im.value = 0)
    (hstatic : im.isStatic = false) (hcw : im.caller.toU256 = (0x1000 : U256))
    (hgas : im.gas = 200000) (hacc : hasAccount caller.state C)
    (hb0 : storageAt caller.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999)
    (hb1 : storageAt caller.state C (mapSlot (0x1000 : U256) 1) = 1)
    (hb2 : storageAt caller.state C (mapSlot (0x2000 : U256) 1) = 0) :
    ∃ ch, processRunner (Meter := Nat) fork bound caller im lt = .ok ch ∧ ch.1.error = none ∧
      storageAt ch.1.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt ch.1.state C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt ch.1.state C (mapSlot (0x2000 : U256) 1) = 1 := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨cost, st', ss', spec, s0, s1, s2⟩ :=
    re_inner_spec hfork hglam (ss := caller.substate.child) hC hct hdata hv hstatic hcw hacc
      hb0 hb1 hb2 (gas := im.gas) (by omega)
  obtain ⟨ch, hch, hce, hcs, -⟩ :=
    spec_message_runs hparis lt hcode htarget (noPre_of hca (notPrecompile_link hC)) hv spec
  exact ⟨ch, hch, hce, by rw [hcs]; exact s0, by rw [hcs]; exact s1, by rw [hcs]; exact s2⟩

/-! ## The gas of transferAndCall to the CALL -/

theorem xf1Cost_le (message : Message fork) (ss : Substate) :
    xf1Cost message ss ≤ 233 + 2100 := by
  unfold xf1Cost
  exact Nat.add_le_add (Nat.le_refl 233) (_root_.UsdtVerify.slotCost_le _)

theorem xf2Cost_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (message : Message fork) (x0 to : U256) (S : State.TransactionState) (ss : Substate) :
    xf2Cost fork message x0 to S ss ≤ 313 + 22100 + 2100 := by
  unfold xf2Cost
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.le_refl 313)
      (Nat.le_trans (Gas.writeCost_le hfork _ _ _ _) (writeMax_le hglam)))
    (_root_.UsdtVerify.slotCost_le _)

theorem xf3Cost_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (message : Message fork) (x0 to : U256) (S : State.TransactionState) (ss : Substate)
    (F : Nat) :
    xf3Cost fork message x0 to S ss F ≤
      255 + 22100 + (memoryGasCost (F + 32) - memoryGasCost F) + (1500 + 8 * 32) := by
  unfold xf3Cost
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add (Nat.le_refl 255)
        (Nat.le_trans (Gas.writeCost_le hfork _ _ _ _) (writeMax_le hglam)))
      (Nat.le_refl _))
    (Nat.le_refl _)

theorem externalBaseCost_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (cold : Bool) : externalBaseCost fork cold ≤ 2600 := by
  rw [externalBaseCost_of_berlin hfork hglam]
  split <;> omega

theorem ic_someCost_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (to : U256)
    (ss : Substate) : ic_someCost fork to ss ≤ 95 + 2600 := by
  unfold ic_someCost
  exact Nat.add_le_add (Nat.le_refl 95) (externalBaseCost_le hfork hglam _)

theorem fb2Cost_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) (to : U256)
    (ss : Substate) (N : Nat) : fb2Cost fork to ss N ≤ 227 + 2600 := by
  unfold fb2Cost fb2nCost fb2mCost
  split
  · exact Nat.add_le_add (by decide) (externalBaseCost_le hfork hglam _)
  · exact Nat.add_le_add (Nat.le_refl 227) (externalBaseCost_le hfork hglam _)

/-- From Berlin and before Glamsterdam, for an empty `bytes` argument: the gas of
`transferAndCall` from pc 0 to the CALL is at most 100000, in every state and substate. -/
theorem tacCallGas_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} (hN : tacN message = 0) (S : State.TransactionState)
    (ss : Substate) : tacCallGas fork message S ss ≤ 100000 := by
  have hW : tacW message = 0 := by
    show (tacN message + 31) / 32 * 32 = 0
    rw [hN]
  have hF : tacF message = 128 := by
    show tacW message + 128 = 128
    rw [hW]
  unfold tacCallGas tac_callCost
  rw [hF, hN, hW]
  refine Nat.le_trans
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.le_refl _) (Nat.le_refl _))
        (xf1Cost_le _ _)) (xf2Cost_le hfork hglam _ _ _ _ _))
        (xf3Cost_le hfork hglam _ _ _ _ _ _)) (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _))
        (ic_someCost_le hfork hglam _ _)) (Nat.le_refl _)) (Nat.le_refl _))
        (fb2Cost_le hfork hglam _ _ _)) ?_
  decide +kernel

/-! ## The frame of transferAndCall, with gas for a callee that works -/

/-- `tac_call_run` with `tacCallGas + 300000` gas, and with the list of the messages that the
frame sends. From pc 0 of `transferAndCall`, for a recipient with code `c` (no EIP-7702
delegation) and below the depth limit: the loop of the interpreter goes to the CALL and sends one
message `msg` from a frame `caller`. The message has at least 210000 gas, goes to the recipient
from the token with the code `c` and no value. For every frame `child` that the runner gives for
it, the loop goes on from pc 3089. Each message that the frame sends (`Trace.Sent`) is `msg`, or
is sent by the frame at pc 3089 after the runner ended `msg`. For every runner and every bound
from the gas of the frame. -/
theorem tac_call_run_re (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize : 1 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x4000aea0) (hval : message.value = 0)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hN : tacN message < 2 ^ 64) {c : ByteArray} (hcode : TacCode message state c)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (h4 : TacFits message state) (h5 : TacHasCode c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {bound : Nat} (runChild : MessageRunner fork Nat bound)
    (hb : tacCallGas fork message state substate + 300000 ≤ bound)
    {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty (tacCallGas fork message state substate + 300000) state
      substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧ 210000 ≤ msg.gas ∧
      caller.state = ((tacCallSt message state).recordAccountRead
        (toAddressMasked (tacToW message))).recordAccountRead message.currentTarget ∧
      msg.target = some (toAddressMasked (tacToW message)) ∧
      msg.codeAddress = some (toAddressMasked (tacToW message)) ∧
      msg.code = c ∧ msg.value = 0 ∧ msg.caller = message.currentTarget ∧
      msg.currentTarget = toAddressMasked (tacToW message) ∧
      msg.depth = message.depth + 1 ∧ msg.isStatic = false ∧
      (∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ (after : Evm fork Nat) (w : GasMeter.gasHeld after.gas ≤ bound),
          At CODE message 3089
            ((if child.1.error.isNone then 1 else 0) ::
              tacRest message (BitVec.ofNat 256 (selector message.data)))
            (tacMem message) after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate after ∧
          147 ≤ after.gas ∧
          Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within =
            Evm.runFrame (step fork) (step_decreases fork) bound runChild after w) ∧
      ∀ (c' : Evm fork Nat) (m : Message fork), Trace.Sent runChild evm c' m →
        (c' = caller ∧ m = msg) ∨
        ∃ (lt : msg.gas < bound)
          (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas })
          (after : Evm fork Nat),
          runChild caller msg lt = .ok child ∧
          At CODE message 3089
            ((if child.1.error.isNone then 1 else 0) ::
              tacRest message (BitVec.ofNat 256 (selector message.data)))
            (tacMem message) after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate after ∧
          147 ≤ after.gas ∧ Trace.Sent runChild after c' m := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hp1 := (transferAndCall_p1 (fork := fork) (message := message) (state := state)
    (substate := substate) hfork hsize hsize' hsel (by rw [hval]; decide)
    (gas := tacCallGas fork message state substate + 300000) (by omega)).toHoare
  have hcall := tac_at_call (fork := fork) (message := message)
    (sel := BitVec.ofNat 256 (selector message.data)) (state := state) (substate := substate)
    hfork hstatic hacc hN hcode h1 h2 h3 h4 h5
    (gas := tacCallGas fork message state substate + 300000 - 207) (by omega)
  obtain ⟨z, hr, hz⟩ := Triple.seq hp1 hcall evm start
  have hz' : At CODE message 3088
      (tacAsked fork message state substate
          (tacCallGas fork message state substate + 300000 - 207) :: tacToW message :: 0 ::
        tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132) ::
        tacFpw (tacLen message) :: 0 ::
        tacRest message (BitVec.ofNat 256 (selector message.data)))
      (tacMem message)
      (tacCallGas fork message state substate + 300000 - 207 -
        (tacCallGas fork message state substate + 5))
      (tacCallSt message state) (tacCallSs fork message state substate) z := hz
  obtain ⟨zc, zj, zm, zp, zst, zmem, zg, zrun, zerr, zout, zs, zss⟩ := id hz'
  obtain ⟨hin, -, -⟩ := tac_call_range (message := message) hN
  have hrun1 := runFrame_eq_of_reaches (bound := bound) (runChild := runChild)
    Step.gasHeld_le Step.runFrame_eq hr within
  have hstep : step fork z = callStep .call z := step_at_call hz' (by code_fact) (by code_fact)
  have hext : extendMemory z.memory.size
      [(tacFpw (tacLen message), BitVec.ofNat 256 (tacW message + 132)),
        (tacFpw (tacLen message), (0 : U256))] = ⟨0, 0⟩ := by
    rw [zmem]
    exact extendMemory_in hin
  have h0 : (extendMemory z.memory.size
      [(tacFpw (tacLen message), BitVec.ofNat 256 (tacW message + 132)),
        (tacFpw (tacLen message), (0 : U256))]).cost = 0 := by
    rw [hext]
  have hEle : callBaseCost fork
        (decide (toAddressMasked (tacToW message) ∉ z.substate.accessedAddresses)) +
      routeCost fork (z.substate.accessedAddresses.insert (toAddressMasked (tacToW message)))
        none ≤ 2600 := by
    have hr0 : routeCost fork
        (z.substate.accessedAddresses.insert (toAddressMasked (tacToW message))) none = 0 := rfl
    rw [callBaseCost_of_berlin hfork hglam, hr0]
    split <;> omega
  generalize hEdef : callBaseCost fork
        (decide (toAddressMasked (tacToW message) ∉ z.substate.accessedAddresses)) +
      routeCost fork (z.substate.accessedAddresses.insert (toAddressMasked (tacToW message)))
        none = E at hEle
  have hst0 : z.stack.val = tacAsked fork message state substate
        (tacCallGas fork message state substate + 300000 - 207) :: tacToW message ::
      ((if CallKind.call.sendsValue then [0] else []) ++
        tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132) ::
        tacFpw (tacLen message) :: 0 ::
        tacRest message (BitVec.ofNat 256 (selector message.data))) := zst
  obtain ⟨cl, msg, hsent, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10,
      s1, s2, m1, mr, m2, m3, mt, mca, mc, mdp, md, m5, mst, m6, m7, mb, mtx⟩ :=
    callStep_child_of_routes (kind := .call) (route := none) hfork hst0
      (by rw [zs]; exact tac_code_at_call hcode h5)
      (show Routes fork z.state c none from fun hp => hdel hp)
      (by rw [zm]; exact hdepth)
      (by rw [h0, hEdef, zg]; omega)
  rw [h0, hEdef] at m1 c7
  have hask : (tacAsked fork message state substate
      (tacCallGas fork message state substate + 300000 - 207)).toNat = 299081 := by
    unfold tacAsked
    have e : tacCallGas fork message state substate + 300000 - 207 -
        tacCallGas fork message state substate - 2 = 299791 := by omega
    rw [e]
    decide
  have hEg : E ≤ z.gas := by rw [zg]; omega
  have hk := mcg_keep (fork := fork) htw
    (asked := (tacAsked fork message state substate
      (tacCallGas fork message state substate + 300000 - 207)).toNat)
    (gas := z.gas) (E := E) hEg
  have hmg : msg.gas = min 299081 (z.gas - E - (z.gas - E) / 64) := by
    rw [m1, mcg_sub htw hEg, hask]
  rw [zg] at hmg hk c7
  have hlt : msg.gas < bound := by omega
  have hbig : 210000 ≤ msg.gas := by omega
  have hclg : 147 ≤ cl.gas := by
    rw [c7]
    omega
  have hme : memoryExtend (tacMem message) (ExtendMemory.expandBy ⟨0, 0⟩) = tacMem message :=
    memoryExtend_zero _
  -- the frame after the CALL, for every frame of the callee
  have key : ∀ (child after : Evm fork Nat),
      resumeCall fork cl 0 (tacFpw (tacLen message)) 0 child = .ok after →
      At CODE message 3089
        ((if child.error.isNone then 1 else 0) ::
          tacRest message (BitVec.ofNat 256 (selector message.data)))
        (tacMem message) after.gas (incorporateChild fork cl child).state
        (incorporateChild fork cl child).substate after ∧
      147 ≤ after.gas := by
    intro child after hres
    obtain ⟨after', hres', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
      resumeCall_eq (fork := fork) (caller := cl) (child := child)
        (o := tacFpw (tacLen message)) (osz := 0)
        (by rw [c5]; simp [tacRest, STACK_LIMIT])
    have e : after' = after := Except.ok.inj (hres'.symm.trans hres)
    subst e
    have hw : memoryWrite (tacMem message) (tacFpw (tacLen message)).toNat
        (child.output.extract 0 (min (0 : U256).toNat child.output.size)) =
        tacMem message := by
      simp [memoryWrite]
    have hmem : after'.memory = tacMem message := by
      rw [a6, c6, hext, zmem, hme]
      exact hw
    refine ⟨⟨a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
      by rw [a4, c4, zp], by rw [a5, c5], hmem, rfl, a8.trans (c8.trans zrun),
      a9.trans (c9.trans zerr), a10.trans (c10.trans zout), a11, a12⟩, ?_⟩
    rw [a7]
    omega
  refine ⟨cl, msg, hlt, hbig, by rw [s1, zs, zm] <;> rfl, mt.trans (by simp), mca, mc,
    m5.trans (by simp), m2.trans (by simp [zm]), m3, by rw [m6, zm],
    m7.trans (by simp [zm, hstatic]), ?_, ?_⟩
  · intro lt child hch
    obtain ⟨after, hres, -⟩ :=
      resumeCall_eq (fork := fork) (caller := cl) (child := child.1)
        (o := tacFpw (tacLen message)) (osz := 0)
        (by rw [c5]; simp [tacRest, STACK_LIMIT])
    obtain ⟨hat, hga⟩ := key child.1 after hres
    obtain ⟨w, hrun2⟩ : ∃ w : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild z
          (Nat.le_trans (hr.gasHeld_le Step.gasHeld_le) within) =
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after w :=
      ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) lt hch hres⟩
    exact ⟨after, w, hat, hga, hrun1.trans hrun2⟩
  · intro c' m hs
    have hs1 := Trace.Sent.of_reaches hr hs
    rcases Trace.Sent.of_step_child (by rw [hstep]; exact hsent) hs1 with
      h | ⟨lt, child, after, hch, hres, hs2⟩
    · exact .inl h
    · obtain ⟨hat, hga⟩ := key child.1 after hres
      exact .inr ⟨lt, child, after, hch, hat, hga, hs2⟩

/-! ## The call -/

/-- The gas limit of the top-level message. -/
def RE_GAS : Nat := 1000000

/-- The call `transferAndCall(0x1000, 1, "")` from `Witness.CALLER1` to `C`, with the gas limit
`RE_GAS`. -/
abbrev m_re (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address) :
    Message fork :=
  { m_tac b t C 1 with gas := RE_GAS }

section Facts

variable (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)

theorem re_m_size : (m_re b t C).data.size = 132 := tac_size b t C 1

theorem re_m_sel : selector (m_re b t C).data = 0x4000aea0 := tac_sel b t C 1

theorem re_m_to : tacTo (m_re b t C) = 0x1000 := tac_to b t C 1

theorem re_m_value : tacValue (m_re b t C) = 1 := tac_value b t C 1

theorem re_m_n : tacN (m_re b t C) = 0 := tac_n b t C 1

theorem re_m_nlt : tacN (m_re b t C) < 2 ^ 64 := tac_nlt b t C 1

theorem re_m_caller : (m_re b t C).caller.toU256 = Witness.CALLER1W := Witness.caller1_toU256

theorem re_m_target : (m_re b t C).currentTarget = C := rfl

theorem re_m_rcpt :
    toAddressMasked (tacToW (m_re b t C)) = toAddressMasked (0x1000 : U256) :=
  tac_rcpt b t C 1

theorem re_m_set : TacToSet (m_re b t C) := tac_set b t C 1

theorem re_m_other (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256)) :
    TacToOther (m_re b t C) := tac_other b t C 1 hC

/-- The caller has `10^27` tokens: the amount 1 is covered. -/
theorem re_m_funded {S : State.TransactionState}
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW) :
    TacFunded (m_re b t C) S := by
  simp only [TacFunded, re_m_value, re_m_caller, re_m_target, tac_caller, tac_target, g2, hbal] <;> decide +kernel

/-- The recipient has 0 tokens: its new balance does not wrap. -/
theorem re_m_fits {S : State.TransactionState} (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0) :
    TacFits (m_re b t C) S := by
  simp (disch := supply_side) only [TacFits, re_m_value, re_m_to, re_m_caller, re_m_target, tac_caller, tac_target,
    g1, g2, g3, g4, storageAt_readSlot, Readable.storageAt_writeSlot_ite, hbal, hto]
    <;> decide +kernel

/-- The three balances after the token move, in the state at the CALL. -/
theorem re_m_call_balances {S : State.TransactionState} (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hto2 : storageAt S C (mapSlot (0x2000 : U256) 1) = 0) :
    storageAt (tacCallSt (m_re b t C) S) C (mapSlot Witness.CALLER1W 1) =
        999999999999999999999999999 ∧
      storageAt (tacCallSt (m_re b t C) S) C (mapSlot (0x1000 : U256) 1) = 1 ∧
      storageAt (tacCallSt (m_re b t C) S) C (mapSlot (0x2000 : U256) 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := supply_side) only [tacCallSt, tac_callSt, storageAt_rar, re_m_value, re_m_to,
      re_m_caller, re_m_target, tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto, hto2]
      <;> decide +kernel
  · simp (disch := supply_side) only [tacCallSt, tac_callSt, storageAt_rar, re_m_value, re_m_to,
      re_m_caller, re_m_target, tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto, hto2]
      <;> decide +kernel
  · simp (disch := supply_side) only [tacCallSt, tac_callSt, storageAt_rar, re_m_value, re_m_to,
      re_m_caller, re_m_target, tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto, hto2]
      <;> decide +kernel

end Facts

/-- The gas of the frame of the run: the gas to the CALL and 300000 more. -/
def reMeter (fork : Fork) (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) (S : State.TransactionState) (ss : Substate) : Nat :=
  tacCallGas fork (m_re b t C) S ss + 300000

/-- The gas of the frame is within the gas limit of the message. -/
theorem reMeter_le (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate) :
    reMeter fork b t C S ss ≤ (m_re b t C).gas := by
  have h := tacCallGas_le hfork hglam (re_m_n b t C) S ss
  show tacCallGas fork (m_re b t C) S ss + 300000 ≤ 1000000
  omega

/-! ## The run -/

/-- THE RUN WITH A RECEIVER THAT CALLS BACK, on EthLib's real runner, from Paris and before
Glamsterdam. In any state `S` where `C` (an address with the word of LINK) holds the code of
LINK, the address of the word 0x1000 holds the code `RE`, the caller has `10^27` tokens and
0x1000 and 0x2000 have none: the frame of `transferAndCall(0x1000, 1, "")`, run by the loop of
the interpreter with `processRunner` (any bound from the gas of the frame), ends with no error
and the output `true`. At the end the caller has `10^27 - 1` tokens, 0x1000 has 0 and 0x2000 has
1: the receiver did call `transfer(0x2000, 1)` on the token while the token was calling it.

The last part lists what enters `C` in the runs that the frame starts: for every condition `Q`
on messages that holds for the mapping keys [0x1000, 0x2000, 1] (the keys of the inner call),
the frame is clean (`Trace.CleanFrame`). -/
theorem tac_re_core (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (S : State.TransactionState) (ss : Substate)
    (hold : Reenter.HoldsCode C CODE S)
    (hre : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash = .ok RE)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = TOTALW)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hto2 : storageAt S C (mapSlot (0x2000 : U256) 1) = 0)
    {B : Nat} (hB : reMeter fork b t C S ss ≤ B) {evm : Evm fork Nat}
    (start : At CODE (m_re b t C) 0 [] .empty (reMeter fork b t C S ss) S ss evm)
    (within : GasMeter.gasHeld evm.gas ≤ B) :
    ∃ s, Evm.runFrame (step fork) (step_decreases fork) B (processRunner fork B) evm within =
        .ok s ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt s.state C (mapSlot (0x1000 : U256) 1) = 0 ∧
      storageAt s.state C (mapSlot (0x2000 : U256) 1) = 1 ∧
      ∀ (Q : Message fork → Prop),
        (∀ m : Message fork, callKeys m = [(0x1000 : U256), (0x2000 : U256), (1 : U256)] → Q m) →
        Trace.CleanFrame C CODE Q B evm := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hacc : hasAccount S C := hold.hasAccount
  have hcodeT : TacCode (m_re b t C) S RE := by
    unfold TacCode
    rw [re_m_to]
    exact hre
  obtain ⟨cl, msg, hlt, hmg, hcls, mt, mca, mc, mv, mcal, mct, mdp, mst, hafter, honly⟩ :=
    tac_call_run_re hfork hglam (message := m_re b t C) (state := S) (substate := ss)
      (by rw [re_m_size]; decide) (by rw [re_m_size]; decide) (re_m_sel b t C) rfl rfl hacc
      (re_m_nlt b t C) hcodeT (re_m_set b t C) (re_m_other b t C hC) (re_m_funded b t C hbal)
      (re_m_fits b t C hacc hbal hto) (by unfold TacHasCode; decide +kernel)
      (fun _ => re_not_delegated) (show 0 + 1 ≤ STACK_DEPTH_LIMIT by decide)
      (processRunner fork B) hB start within
  rw [re_m_rcpt] at hcls mt mca mct
  have mcal' : msg.caller = C := mcal
  have mdp' : msg.depth = 1 := mdp
  have hclHold : Reenter.HoldsCode C CODE cl.state := by
    rw [hcls]
    exact Reenter.holdsCode_recordAccountRead _
      (Reenter.holdsCode_recordAccountRead _ (holdsCode_tacCallSt hold))
  obtain ⟨hb0, hb1, hb2⟩ := re_m_call_balances b t C hacc hbal hto hto2
  have hclc : cl.state.getCode (cl.state.getAccount msg.caller).codeHash = .ok CODE := by
    rw [mcal']
    exact hclHold.1
  have hmdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT := by
    rw [mdp']
    decide
  -- the message that the CALL of `RE` sends: the inner call
  have facts : ∀ (cl1 : Evm fork Nat) (im : Message fork),
      ReSends msg cl.state cl.substate.child CODE cl1 im →
      im.code = CODE ∧ im.target = some C ∧ im.codeAddress = some C ∧ im.currentTarget = C ∧
      im.data = reData ∧ im.value = 0 ∧ im.isStatic = false ∧
      im.caller.toU256 = (0x1000 : U256) ∧ hasAccount cl1.state C ∧
      storageAt cl1.state C (mapSlot Witness.CALLER1W 1) = 999999999999999999999999999 ∧
      storageAt cl1.state C (mapSlot (0x1000 : U256) 1) = 1 ∧
      storageAt cl1.state C (mapSlot (0x2000 : U256) 1) = 0 := by
    intro cl1 im hs
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hs
    refine ⟨r8, by rw [r6, mcal'], by rw [r7, mcal'], r5.trans mcal', r9, r10, r12.trans mst,
      by rw [r4, mct]; exact rcpt_toU256, ?_, ?_, ?_, ?_⟩
    · rw [r1]
      exact (Reenter.holdsCode_recordAccountRead _
        (Reenter.holdsCode_recordAccountRead _ hclHold)).hasAccount
    · rw [r1, storageAt_rar, storageAt_rar, hcls, storageAt_rar, storageAt_rar]
      exact hb0
    · rw [r1, storageAt_rar, storageAt_rar, hcls, storageAt_rar, storageAt_rar]
      exact hb1
    · rw [r1, storageAt_rar, storageAt_rar, hcls, storageAt_rar, storageAt_rar]
      exact hb2
  -- the run of the message to `RE`
  obtain ⟨child, cl1, im, lt', ch, hchild, hchildE, hchildO, hs, himg, hch, hchE, hst⟩ :=
    re_message_runs hparis hglam hlt mc mt (noPre_of mca notPrecompile_rcpt) mv hclc
      (fun _ => code_not_delegated) hmdepth hmg
      (fun cl1 im lt' hs hg => by
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := facts cl1 im hs
        obtain ⟨ch, hch, hce, -⟩ :=
          re_inner_runs hparis hglam lt' hC f1 f2 f3 f4 f5 f6 f7 f8 hg f9 f10 f11 f12
        exact ⟨ch, hch, hce⟩)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := facts cl1 im hs
  obtain ⟨ch', hch', -, e0, e1, e2⟩ :=
    re_inner_runs hparis hglam lt' hC f1 f2 f3 f4 f5 f6 f7 f8 himg f9 f10 f11 f12
  have hchEq : ch' = ch := Except.ok.inj (hch'.symm.trans hch)
  rw [hchEq] at e0 e1 e2
  -- the frame of transferAndCall after the CALL
  obtain ⟨after, w, hat, hga, hrun12⟩ := hafter hlt child hchild
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [hchildE] <;> rfl
  have hat1 := hat
  rw [hflag] at hat1
  have spec := tac_after_ok (fork := fork) (message := m_re b t C)
    (sel := BitVec.ofNat 256 (selector (m_re b t C).data)) (flag := 1)
    (st := (incorporateChild fork cl child.1).state)
    (ss := (incorporateChild fork cl child.1).substate)
    (re_m_nlt b t C) (by decide) hga
  obtain ⟨s, hrf, hH⟩ := spec.runFrame (runChild := processRunner fork B) hat1 w
  obtain ⟨-, he, ho, -, hss, -⟩ := hH
  have hsst : s.state = ch.1.state := by
    rw [hss, state_incorporate_ok hchildE, hst]
  refine ⟨s, hrun12.trans hrf, by simpa using he, ho, by rw [hsst]; exact e0,
    by rw [hsst]; exact e1, by rw [hsst]; exact e2, ?_⟩
  intro Q hQ c m hsent
  rcases honly c m hsent with ⟨hc0, hm0⟩ | ⟨lt2, child2, after2, hch2, hat2, hga2, hs2⟩
  · rw [hc0, hm0]
    refine cleanRun_call (by rw [mt]; rfl)
      (re_clean hparis hglam mc mv hclc (fun _ => code_not_delegated) hmdepth
        (show 5000 ≤ msg.gas by omega) (Nat.le_refl _)
        (fun h => absurd (mct.symm.trans h) (rcpt_ne_link hC)) ?_)
    intro cl2 im2 hs2 hg2
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ := facts cl2 im2 hs2
    have hg3 : im2.gas = 200000 := hg2 hmg
    obtain ⟨cost, st', ss', spec2, -⟩ :=
      re_inner_spec hfork hglam (ss := cl2.substate.child) hC k4 k5 k6 k7 k8 k9 k10 k11 k12
        (gas := im2.gas) (by omega)
    refine cleanRun_call (by rw [k2]; rfl)
      (clean_of_spec hparis k6 k1 spec2 (fun _ => hQ im2 ?_))
    have hA1 : loadWord im2.data 4 32 = (0x2000 : U256) := by rw [k5]; exact reData_arg1
    have hA2 : loadWord im2.data 36 32 = (1 : U256) := by rw [k5]; exact reData_arg2
    simp only [callKeys, k8, hA1, hA2, g4, q2, q3]
  · have hc2 : child2 = child := Except.ok.inj (hch2.symm.trans hchild)
    rw [hc2, hflag] at hat2
    have spec3 := tac_after_ok (fork := fork) (message := m_re b t C)
      (sel := BitVec.ofNat 256 (selector (m_re b t C).data)) (flag := 1)
      (st := (incorporateChild fork cl child.1).state)
      (ss := (incorporateChild fork cl child.1).substate)
      (re_m_nlt b t C) (by decide) hga2
    exact absurd hs2 (Trace.not_sent_of_specG spec3 hat2 _ c m)

end LinkVerify.Sanity

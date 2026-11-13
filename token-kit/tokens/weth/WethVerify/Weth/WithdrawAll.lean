import TokenKit.Evm.CallOutcome
import TokenKit.Evm.Solvent
import WethVerify.Weth.Withdraw

/-!
# withdraw(uint256) of WETH9: every run, with the failing cases

`ok_withdraw_exact` (Weth/Withdraw.lean) describes a run of `withdraw` that ends with no error,
under three side conditions: the state gives the code of the sender, the call depth has room,
and the gas reaches the CALL and pays its price. This file removes the three: it proves that a
run that ends with no error MEETS them, so every other run ends with an error.

- `callStep_value_deep_mem`: the step of a CALL with value at the depth limit pushes 0 and keeps
  the memory. (`callStep_value_deep` of Evm/CallOutcome.lean, with the memory.)
- `call_bad`: a run of the loop from a frame at a CALL, when the state does not give the code of
  the callee, or the gas is below the price, or the depth is at the limit, or the value is above
  the balance: the run ends with an error, or goes on from the next opcode with 0 pushed.
- `ok_withdraw_all`: every run of `withdraw` from pc 0 that returns a frame with no error. Its
  only hypotheses on the fork and the sender are `hglam` and `hdel`. It gives: the state gave the
  code of the sender, the depth had room, the gas paid for the CALL, no value came with the
  call, `wad` is at most the token balance of the sender and at most the ether of the contract,
  the runner ended the one message of the CALL with no error, and the end state is its state.
- The failing cases, each for every runner and every bound, each says that the frame that the
  loop returns has an error (the message then rolls its writes back):
  `withdraw_fails_value` (the call carries value), `withdraw_fails_balance` (the token balance
  of the sender is below `wad`), `withdraw_fails_ether` (the ether of the contract is below
  `wad`), `withdraw_fails_depth` (call depth at the limit of 1024), `withdraw_fails_gas` (the
  gas does not reach the CALL or does not pay its price: out of gas at the CALL),
  `withdraw_fails_noCode` (the state does not give the code of the sender),
  `withdraw_fails_callee` (the message of the CALL ends with an error: the CALL fails).

## Forks

`withdraw_fails_value` and `withdraw_fails_balance` hold from Berlin on every fork: they are
before the CALL. Every other theorem here needs `hglam : fork < .glamsterdam`: EthLib's rules of
the CALL step are proved for the one-counter gas rules, which Glamsterdam replaces (EIP-8037
splits the gas in two counters). So the covered forks are Berlin, London, Paris, Shanghai,
Cancun, Prague and Osaka. Glamsterdam is not covered.

`hdel`: from Prague, the code of the sender is no EIP-7702 delegation. EthLib's rule of the CALL
step does not cover a delegated target. Before Prague `hdel` holds for every sender.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace WethVerify.Paths

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify WethVerify.Blocks WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

section Steps

variable {fork : Fork} {evm : Evm fork Nat} {g a v i isz o osz : U256} {rest : List U256}

/-- Before Glamsterdam, a CALL with value at the depth limit, from a frame that is not static
and holds the value and the gas of the price: no message is sent, the frame pushes 0, and its
memory only grows for the two ranges. -/
theorem callStep_value_deep_mem (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {calleeCode : ByteArray}
    (hst : evm.stack.val = g :: a :: v :: i :: isz :: o :: osz :: rest) (hv : v ≠ 0)
    (hstatic : evm.message.isStatic = false)
    (hbal : v ≤ (evm.state.getAccount evm.message.currentTarget).balance)
    (hcode : evm.state.getCode (evm.state.getAccount (toAddressMasked a)).codeHash =
      .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdeep : STACK_DEPTH_LIMIT < evm.message.depth + 1)
    (hgas : (callBaseCost fork (decide (toAddressMasked a ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked a) v + callValueCost fork v) +
      (extendMemory evm.memory.size [(i, isz), (o, osz)]).cost ≤ evm.gas) :
    ∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.memory = memoryExtend evm.memory
        (extendMemory evm.memory.size [(i, isz), (o, osz)]).expandBy := by
  have hng : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt hglam
  rcases evm with ⟨pc, ⟨l, hl⟩, memory, code, valid, gas, running, message, output, returnData,
    state, substate, error⟩
  simp only at hst
  subst hst
  have hgc : ∀ (tx : State.TransactionState) (x : Address) h,
      (tx.recordAccountRead x).getCode h = tx.getCode h := fun _ _ _ => rfl
  have hga : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).getAccount y = tx.getAccount y := fun _ _ _ => rfl
  have hal : ∀ (tx : State.TransactionState) (x y : Address),
      (tx.recordAccountRead x).isAccountAlive y = tx.isAccountAlive y := fun _ _ _ => rfl
  simp only at hcode hgas hdeep hstatic hbal ⊢
  have hdel' : (if Fork.pectra ≤ fork then delegatedAddress calleeCode else none) = none := by
    split
    · exact hdel ‹_›
    · rfl
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hsd : Fork.spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hv' : ¬v = 0#256 := hv
  generalize hE : callBaseCost fork (!decide (toAddressMasked a ∈ substate.accessedAddresses)) +
    (if state.isAccountAlive (toAddressMasked a) = true then 0 else NEW_ACCOUNT) + CALL_VALUE = E
  have hgas' : E + (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    rw [← hE]; simpa [callNewAccountCost, callValueCost, hv', hng, hsd] using hgas
  have hmin : min g.toNat (maxMessageCallGas
      (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E)) + E +
      (extendMemory memory.size [(i, isz), (o, osz)]).cost ≤ gas := by
    have : maxMessageCallGas (gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E) ≤
        gas - (extendMemory memory.size [(i, isz), (o, osz)]).cost - E := Nat.sub_le _ _
    omega
  have hbal' : ¬(state.getAccount message.currentTarget).balance < v := by
    simpa [BitVec.lt_def, BitVec.le_def] using hbal
  have hlen : rest.length ≠ STACK_LIMIT := by simp at hl; omega
  simp [callStep, popCallOperands, popCallValue, CallKind.sendsValue, popWord, Stack.pop, bind,
    Except.bind, pure, Except.pure, accessAddress, hfork, checkGas, hng, accessDelegation,
    accountCode, recordAccountRead, hgc, hga, hal, hcode, hdel', htw, hsd, Except.mapError,
    callExtraGas, callNewAccountCost, callNewAccountStateGas, callValueCost, hv',
    payCall, messageCallGas, chargeGas, GasMeter.charge, finishCall, genericCall, keepReads,
    GasMeter.gasLeft, GasMeter.drain, GasMeter.reservoir, hdeep, hstatic, hE,
    hgas', Nat.not_lt.mpr hmin, hbal', skipCall, refillStateGas, GasMeter.refill, GasMeter.credit,
    pushWord, Stack.push, hlen, advance, Functor.map, Except.map]

end Steps

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- From Berlin and before Glamsterdam, for every runner and every bound: a run of the loop from
a frame at a CALL with empty ranges, not static, that returns a frame `s`, in each of the four
cases where the CALL cannot send its message: the state does not give the code of the callee,
the gas is below the price, the depth is at the limit, the value is above the balance. Then `s`
has an error, or no message was sent and the loop went on from the next opcode with 0 pushed and
the same memory. -/
theorem call_bad (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {code : ByteArray} {pc : Nat} {memory : ByteArray} {gas : Nat}
    {asked to v inputStart outputStart : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf1) (hstatic : message.isStatic = false)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hbad : (∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .error e) ∨
      gas < callExtra fork state substate to v ∨ STACK_DEPTH_LIMIT < message.depth + 1 ∨
      (state.getAccount message.currentTarget).balance < v)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At code message pc (asked :: to :: v :: inputStart :: 0 :: outputStart :: 0 :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none ∨
    ∃ g st ss after, At code message (pc + 1) (0 :: rest) memory g st ss after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
  have hstep : step fork evm = callStep .call evm := step_at_call start hlt hbyte
  obtain ⟨hc, hj, hm, hp, hst, hmem, hg, hrunning, herr, hout, hs, hss⟩ := id start
  have hext : extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)] = ⟨0, 0⟩ := by
    simp [extendMemory]
  have fails : StepFails (callStep .call evm) → s.error ≠ none := fun hf =>
    error_ne_none_of_stepFails hrunning (by rw [hstep]; exact hf) hrun
  have next : (∃ after, callStep .call evm = .ok (.next after) ∧
      after.code = evm.code ∧ after.validJumpDestinations = evm.validJumpDestinations ∧
      after.message = evm.message ∧ after.pc = evm.pc + 1 ∧ after.stack.val = 0 :: rest ∧
      after.running = evm.running ∧ after.error = evm.error ∧ after.output = evm.output ∧
      after.memory = evm.memory) →
      ∃ g st ss after, At code message (pc + 1) (0 :: rest) memory g st ss after ∧
        ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
          Evm.runFrame (step fork) (step_decreases fork) bound runChild after within' = .ok s := by
    rintro ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩
    rw [← hstep] at hn
    rw [runFrame_of_step_eq_next hrunning hn] at hrun
    exact ⟨after.gas, after.state, after.substate, after,
      ⟨a1.trans hc, a2.trans hj, a3.trans hm, by rw [a4, hp], a5, a9.trans hmem, rfl,
        a6.trans hrunning, a7.trans herr, a8.trans hout, rfl, rfl⟩, _, hrun⟩
  have hcases : (∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash =
        .error e) ∨
      ∃ c, state.getCode (state.getAccount (toAddressMasked to)).codeHash = .ok c := by
    cases state.getCode (state.getAccount (toAddressMasked to)).codeHash with
    | error e => exact .inl ⟨e, rfl⟩
    | ok c => exact .inr ⟨c, rfl⟩
  rcases hcases with ⟨e, hcode⟩ | ⟨calleeCode, hcode⟩
  · exact .inl (fails (callStep_missing hfork hglam hst (by rw [hs]; exact hcode)))
  · have hd := hdel calleeCode hcode
    have hcode' : evm.state.getCode (evm.state.getAccount (toAddressMasked to)).codeHash =
        .ok calleeCode := by rw [hs]; exact hcode
    have hnc : ¬∃ e, state.getCode (state.getAccount (toAddressMasked to)).codeHash =
        .error e := by
      rintro ⟨e, he⟩
      rw [hcode] at he
      cases he
    by_cases hv : v = 0
    · subst hv
      have hx := callExtra_zero hfork hglam state substate to
      have hcb : callBaseCost fork
          (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) =
          callExtra fork state substate to 0 := by
        rw [hx, callBaseCost_of_berlin hfork hglam, hss]
      have hst0 : evm.stack.val = asked :: to ::
          ((if CallKind.call.sendsValue then [0] else []) ++
            inputStart :: 0 :: outputStart :: 0 :: rest) := hst
      by_cases hgas : callExtra fork state substate to 0 ≤ gas
      · have hdeep : STACK_DEPTH_LIMIT < message.depth + 1 := by
          rcases hbad with h | h | h | h
          · exact absurd h hnc
          · omega
          · exact h
          · exact absurd h (by simp)
        obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, -, a9, -⟩ :=
          callStep_deep_of_routes (kind := .call) (route := none) hfork hst0 hcode' hd
            (by rw [hm]; exact hdeep)
            (by
              rw [hext, hcb, hg]
              show callExtra fork state substate to 0 + 0 + 0 ≤ gas
              omega)
        refine .inr (next ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, ?_⟩)
        rw [a9, hext]
        exact memoryExtend_zero _
      · refine .inl (fails (callStep_fails_of_routes (kind := .call) (route := none) hfork hst0
          hcode' hd ?_))
        rw [hext, hcb, hg]
        show gas < callExtra fork state substate to 0 + 0 + 0
        omega
    · have hprice : (callBaseCost fork
            (decide (toAddressMasked to ∉ evm.substate.accessedAddresses)) +
          callNewAccountCost fork evm.state (toAddressMasked to) v + callValueCost fork v) +
          (extendMemory evm.memory.size [(inputStart, 0), (outputStart, 0)]).cost =
          callExtra fork state substate to v := by
        rw [hext, hs, hss]
        rfl
      by_cases hgas : callExtra fork state substate to v ≤ gas
      · by_cases hbal : v ≤ (state.getAccount message.currentTarget).balance
        · have hdeep : STACK_DEPTH_LIMIT < message.depth + 1 := by
            rcases hbad with h | h | h | h
            · exact absurd h hnc
            · omega
            · exact h
            · exact absurd hbal (BitVec.not_le.mpr h)
          obtain ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
            callStep_value_deep_mem hfork hglam hst hv
              (by rw [hm]; exact hstatic) (by rw [hs, hm]; exact hbal) hcode' hd
              (by rw [hm]; exact hdeep) (by rw [hprice, hg]; exact hgas)
          refine .inr (next ⟨after, hn, a1, a2, a3, a4, a5, a6, a7, a8, ?_⟩)
          rw [a9, hext]
          exact memoryExtend_zero _
        · obtain ⟨after, hat, w, h⟩ := callLow_ok (asked := asked) (inputStart := inputStart)
            (outputStart := outputStart) (rest := rest) hfork hglam hlt hbyte hstatic
            (BitVec.not_le.mp hbal) hcode hd hgas start within hrun
          exact .inr ⟨_, _, _, after, hat, w, h⟩
      · exact .inl (fails (callStep_value_poor hfork hglam hst hv hcode' hd
          (by rw [hprice, hg]; omega)))

/-- Every run of `withdraw(wad)` that the interpreter loop ends with no error, for every runner
and every bound, with no side condition on the depth, the gas or the code of the sender: the
state gave the code of the sender, the call depth had room, the gas reached the CALL and paid
its price, and the rest is `ok_withdraw_exact`. -/
theorem ok_withdraw_all (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d)
    (hdel : ∀ c, state.getCode (state.getAccount message.caller).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    ∃ calleeCode, state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode ∧
      message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      wPre fork message state substate +
        callExtra fork state substate (wSrc message) (wAmt message) ≤ gas ∧
      isZero message.value ≠ 0 ∧
      isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
        (wAmt message)))) ≠ 0 ∧
      message.isStatic = false ∧ hasAccount state message.currentTarget ∧
      wAmt message ≤ etherOf state message.currentTarget ∧
      ∃ caller msg child, Ran runChild caller msg child ∧ child.error = none ∧
        child.gas ≤ msg.gas ∧
        CallSend message (gas - wPre fork message state substate) (wState message state)
          (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
          calleeCode caller msg ∧
        1489 ≤ gas - wPre fork message state substate -
          (callGas fork (wState message state) (wSub fork message state substate)
            (wAsk message) (wSrc message) (wAmt message)
            (gas - wPre fork message state substate)).cost + child.gas ∧
        s.output = ByteArray.empty ∧
        s.gas = gas - wPre fork message state substate -
          (callGas fork (wState message state) (wSub fork message state substate)
            (wAsk message) (wSrc message) (wAmt message)
            (gas - wPre fork message state substate)).cost + child.gas - 1489 ∧
        s.state = (incorporateChild fork caller child).state ∧
        s.substate = logSub2 (incorporateChild fork caller child).substate message.currentTarget
          WITHDRAWAL (wSrc message) (wordBytes (wAmt message)) := by
  by_cases good : (∃ c, state.getCode (state.getAccount message.caller).codeHash = .ok c) ∧
      message.depth + 1 ≤ STACK_DEPTH_LIMIT ∧
      wPre fork message state substate +
        callExtra fork state substate (wSrc message) (wAmt message) ≤ gas ∧
      wAmt message ≤ etherOf state message.currentTarget
  · obtain ⟨⟨c, hcode⟩, hdepth, hgas, -⟩ := good
    exact ⟨c, hcode, hdepth, hgas, ok_withdraw_exact hfork hglam hsize hsize' hsel hcode
      (hdel c hcode) hdepth hgas start within hrun hok⟩
  · exfalso
    have hx := callExtra_wState (fork := fork) message state substate (wSrc message)
      (wAmt message)
    obtain ⟨hc1, hc2, hstatic, hacc, hcg, z, w, hz, hzr⟩ :=
      ok_withdraw_at hfork hsize hsize' hsel start within hrun hok
    have hcodeEq : (wState message state).getCode
        ((wState message state).getAccount (toAddressMasked (wSrc message))).codeHash =
        state.getCode (state.getAccount message.caller).codeHash := by
      rw [toAddressMasked_wSrc, getCode_wState]
    have hbad : (∃ e, (wState message state).getCode
          ((wState message state).getAccount (toAddressMasked (wSrc message))).codeHash =
          .error e) ∨
        gas - wPre fork message state substate <
          callExtra fork (wState message state) (wSub fork message state substate)
            (wSrc message) (wAmt message) ∨
        STACK_DEPTH_LIMIT < message.depth + 1 ∨
        ((wState message state).getAccount message.currentTarget).balance < wAmt message := by
      rw [hcodeEq, hx]
      have hb : ((wState message state).getAccount message.currentTarget).balance =
          etherOf state message.currentTarget := etherOf_wState message state _
      rw [hb]
      by_cases h1 : ∃ c, state.getCode (state.getAccount message.caller).codeHash = .ok c
      · by_cases h2 : message.depth + 1 ≤ STACK_DEPTH_LIMIT
        · by_cases h3 : wPre fork message state substate +
              callExtra fork state substate (wSrc message) (wAmt message) ≤ gas
          · by_cases h4 : wAmt message ≤ etherOf state message.currentTarget
            · exact absurd ⟨h1, h2, h3, h4⟩ good
            · exact .inr (.inr (.inr (BitVec.not_le.mp h4)))
          · exact .inr (.inl (by omega))
        · exact .inr (.inr (.inl (by omega)))
      · left
        cases hcd : state.getCode (state.getAccount message.caller).codeHash with
        | error e => exact ⟨e, rfl⟩
        | ok c => exact absurd ⟨c, hcd⟩ h1
    rcases call_bad (code := CODE) (pc := 2724) hfork hglam (by code_fact) (by code_fact) hstatic
        (fun c hc => hdel c (by rw [← hcodeEq]; exact hc)) hbad hz w hzr with
      he | ⟨g, st, ss, after, hat, w', h'⟩
    · exact he hok
    · obtain ⟨hy, -⟩ := ok_withdrawTail hfork hstatic hat w' h' hok
      exact absurd hy (by decide)

/-! ## The failing cases -/

section Fails

variable {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}

/-- `withdraw` called with value: the run ends with an error. From Berlin, on every fork. -/
theorem withdraw_fails_value (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x2e1a7d4d)
    (hv : message.value ≠ 0)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := fun hok =>
  (ok_withdraw_at hfork hsize hsize' hsel start within hrun hok).1
    (by unfold isZero; rw [if_neg hv])

/-- `withdraw(wad)` with `wad` above the token balance of the sender: the run ends with an
error. From Berlin, on every fork. -/
theorem withdraw_fails_balance (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x2e1a7d4d)
    (hlow : (storageAt state message.currentTarget (wKey message)).toNat <
      (wAmt message).toNat)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := fun hok => by
  have f := Supply.sub_fact_lt
    (ok_withdraw_at hfork hsize hsize' hsel start within hrun hok).2.1
  omega

variable (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
  (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
  (hsel : selector message.data = 0x2e1a7d4d)
  (hdel : ∀ c, state.getCode (state.getAccount message.caller).codeHash = .ok c →
    .pectra ≤ fork → delegatedAddress c = none)
  (start : At CODE message 0 [] .empty gas state substate evm)
  (within : GasMeter.gasHeld evm.gas ≤ bound)
  (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)

include hfork hglam hsize hsize' hsel hdel start hrun

/-- `withdraw(wad)` with `wad` above the ether of the contract: the CALL pushes 0 and the run
ends with an error. -/
theorem withdraw_fails_ether (hlow : etherOf state message.currentTarget < wAmt message) :
    s.error ≠ none := fun hok => by
  obtain ⟨c, -, -, -, -, -, -, -, hbal, -⟩ :=
    ok_withdraw_all hfork hglam hsize hsize' hsel hdel start within hrun hok
  exact absurd hlow (BitVec.not_lt.mpr hbal)

/-- `withdraw` at the depth limit: the CALL sends no message, pushes 0, and the run ends with an
error. -/
theorem withdraw_fails_depth (hdeep : STACK_DEPTH_LIMIT < message.depth + 1) :
    s.error ≠ none := fun hok => by
  obtain ⟨c, -, hdepth, -⟩ :=
    ok_withdraw_all hfork hglam hsize hsize' hsel hdel start within hrun hok
  omega

/-- `withdraw` with less gas than the code before the CALL and the price of the CALL need (out
of gas before or at the CALL): the run ends with an error. -/
theorem withdraw_fails_gas (hpoor : gas < wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message)) :
    s.error ≠ none := fun hok => by
  obtain ⟨c, -, -, hgas, -⟩ :=
    ok_withdraw_all hfork hglam hsize hsize' hsel hdel start within hrun hok
  omega

/-- `withdraw` when the state does not give the code of the sender: the run ends with an
error. -/
theorem withdraw_fails_noCode {e : State.StateError}
    (hmiss : state.getCode (state.getAccount message.caller).codeHash = .error e) :
    s.error ≠ none := fun hok => by
  obtain ⟨c, hcode, -⟩ :=
    ok_withdraw_all hfork hglam hsize hsize' hsel hdel start within hrun hok
  rw [hmiss] at hcode
  cases hcode

/-- `withdraw` when the CALL fails: if every frame that the runner gives for the message of the
CALL has an error (the callee reverts, or runs out of its 2300 gas), the run ends with an
error. -/
theorem withdraw_fails_callee
    (hfail : ∀ calleeCode caller msg child, Ran runChild caller msg child →
      CallSend message (gas - wPre fork message state substate) (wState message state)
        (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
        calleeCode caller msg → child.error ≠ none) :
    s.error ≠ none := fun hok => by
  obtain ⟨c, -, -, -, -, -, -, -, -, caller, msg, child, hran, hce, -, hsend, -⟩ :=
    ok_withdraw_all hfork hglam hsize hsize' hsel hdel start within hrun hok
  exact hfail c caller msg child hran hsend hce

end Fails

end WethVerify.Paths

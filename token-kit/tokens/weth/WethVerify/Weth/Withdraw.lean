import TokenKit.Evm.Call
import WethVerify.Weth.TotalSupply

/-!
# withdraw(uint256) of WETH9: the storage write, the CALL that sends the ether, the log

`withdraw(wad)` checks `balanceOf[msg.sender] >= wad`, writes `balanceOf[msg.sender] -= wad`,
then runs `msg.sender.transfer(wad)`: a CALL of `wad` wei to the sender with no data, which asks
for 0 gas when `wad` is not 0 (the message then gets the stipend of 2300) and for 2300 gas when
`wad` is 0. It reverts when the CALL pushes 0, and otherwise logs `Withdrawal(sender, wad)`.

The generator proves the code up to the CALL at pc 2724 (`withdraw_p3`, `ok_withdraw`) and from
pc 2725 (`withdrawTail_p0`, `withdrawTail_p1`, `ok_withdrawTail`). This file proves the CALL
between, with the rules of `Evm/Call.lean`, and joins the parts.

## Reentrancy

The storage write is before the CALL. The frame `caller` that the CALL hands to the runner of
messages has the state `wState`: the balance slot of the sender is already lowered by `wad`, and
no ether has moved (the runner moves it). The theorems hold for every runner, so also for the one
of the interpreter, whose callee may call this contract again. They say nothing of what the
callee does: the end state is the state of the frame `child` that the runner gives, whatever it
is. A statement about that state needs an assumption on the runner (see `Weth/Invariant.lean`).

## Theorems

- `withdraw_path`: under every runner that meets an assumption `callee`, from pc 0 the run ends
  after one message `msg` of `CallSend`; when the frame `child` that ends it has no error, the
  run ends with no error, an empty output, the state of `child` and one more log; when `child`
  has an error, the run reverts.
- `ok_withdraw_exact`: every run of the interpreter loop from pc 0 that returns a frame with no
  error is that success case, for every runner and every bound.

## Hypotheses that are not removed

- `hglam : fork < .glamsterdam`: EthLib's CALL rules are for the gas rules before Glamsterdam.
- `hcode`: the state holds the code of the sender (`getCode` returns it).
- `hdel`: from Pectra, the code of the sender is no EIP-7702 delegation.
- `hdepth`: the call depth is below 1024. (At the limit the CALL pushes 0 and the run reverts:
  `withdraw_fails_depth`, Weth/WithdrawAll.lean.)
- `hcall` in `ok_withdraw_exact`: the gas covers the code before the CALL and the price of the
  CALL. (With less the run fails with out of gas: `withdraw_fails_gas`, Weth/WithdrawAll.lean.)

`ok_withdraw_all` (Weth/WithdrawAll.lean) is `ok_withdraw_exact` without `hcode`, `hdepth` and
`hcall`: it proves them for every run that ends with no error.
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

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-- The sender as the code reads it: the caller of the message, masked to 160 bits. -/
abbrev wSrc (message : Message fork) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256

/-- The storage slot of `balanceOf[msg.sender]`. -/
abbrev wKey (message : Message fork) : U256 :=
  mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (wSrc message))
    (3 : U256)

/-- The argument `wad`. -/
abbrev wAmt (message : Message fork) : U256 := loadWord message.data 4 32

/-- The gas that the CALL asks for: 2300 when `wad` is 0, else 0. -/
abbrev wAsk (message : Message fork) : U256 := mul (isZero (wAmt message)) (2300 : U256)

/-- The gas of the code before the CALL. -/
def wPre (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) : Nat :=
  551 + (slotCost (coldIn substate message.currentTarget (wKey message))) +
    (slotCost (coldIn (accessSlot substate message.currentTarget (wKey message))
      message.currentTarget (wKey message))) +
    (Gas.writeCost fork
      (originalAt (readSlot (readSlot state message.currentTarget (wKey message))
        message.currentTarget (wKey message)) message.currentTarget (wKey message))
      (storageAt (readSlot (readSlot state message.currentTarget (wKey message))
        message.currentTarget (wKey message)) message.currentTarget (wKey message))
      (sub (storageAt (readSlot state message.currentTarget (wKey message)) message.currentTarget
        (wKey message)) (wAmt message))
      (coldIn (accessSlot (accessSlot substate message.currentTarget (wKey message))
        message.currentTarget (wKey message)) message.currentTarget (wKey message)))

/-- The state at the CALL: the balance slot of the sender lowered by `wad`. -/
abbrev wState (message : Message fork) (state : State.TransactionState) :
    State.TransactionState :=
  writeSlot (readSlot (readSlot state message.currentTarget (wKey message)) message.currentTarget
      (wKey message)) message.currentTarget (wKey message)
    (sub (storageAt (readSlot state message.currentTarget (wKey message)) message.currentTarget
      (wKey message)) (wAmt message))

/-- The substate at the CALL. -/
abbrev wSub (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) : Substate :=
  storeSub fork (accessSlot (accessSlot substate message.currentTarget (wKey message))
      message.currentTarget (wKey message)) message.currentTarget (wKey message)
    (originalAt (readSlot (readSlot state message.currentTarget (wKey message))
      message.currentTarget (wKey message)) message.currentTarget (wKey message))
    (storageAt (readSlot (readSlot state message.currentTarget (wKey message))
      message.currentTarget (wKey message)) message.currentTarget (wKey message))
    (sub (storageAt (readSlot state message.currentTarget (wKey message)) message.currentTarget
      (wKey message)) (wAmt message))

/-- The topic of `Withdrawal(address,uint256)`. -/
abbrev WITHDRAWAL : U256 :=
  57810043145978950376228313794938171962422655018555593468903716172405399886693

/-- The CALL goes to the caller of the message. -/
theorem toAddressMasked_wSrc (message : Message fork) :
    toAddressMasked (wSrc message) = message.caller :=
  toAddressMasked_mask_toU256 message.caller

/-- The storage write changes no ether balance. -/
theorem etherOf_wState (message : Message fork) (state : State.TransactionState) (a : Address) :
    etherOf (wState message state) a = etherOf state a := by
  unfold etherOf
  rw [getAccount_writeSlot]
  rfl

/-- The storage write keeps the code of every account. -/
theorem getCode_wState (message : Message fork) (state : State.TransactionState) (a : Address) :
    (wState message state).getCode ((wState message state).getAccount a).codeHash =
      state.getCode (state.getAccount a).codeHash := by
  rw [getAccount_writeSlot, getCode_writeSlot]
  rfl

/-- The price of the CALL is the one in the state and substate at the start. -/
theorem callExtra_wState (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (to v : U256) :
    callExtra fork (wState message state) (wSub fork message state substate) to v =
      callExtra fork state substate to v := by
  unfold callExtra callNewAccountCost State.TransactionState.isAccountAlive
    State.TransactionState.accountExists
  rw [getAccountOptional_writeSlot]
  rfl

/-- The CALL asks for at most 2300 gas. -/
theorem wAsk_le (message : Message fork) : (wAsk message).toNat ≤ 2300 := by
  unfold wAsk isZero
  split <;> decide

/-- The word that the code tests after the CALL is not 0 exactly when the callee had no error. -/
theorem callFlag_ne {e : Option EvmError} :
    isZero (isZero (if e.isNone then (1 : U256) else 0)) ≠ 0 ↔ e = none := by
  cases e <;> simp [isZero]

/-- `withdraw_p3` of the generated file, with the names of this file: from pc 0 to the CALL. -/
theorem withdraw_at (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x2e1a7d4d)
    (hstatic : message.isStatic = false) (hacc : hasAccount state message.currentTarget)
    (hc1 : isZero message.value ≠ 0)
    (hc2 : isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
      (wAmt message)))) ≠ 0)
    {gas : Nat} (hg : wPre fork message state substate + 2300 < gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 2724 [wAsk message, wSrc message, wAmt message, (96 : U256), (0 : U256),
          (96 : U256), (0 : U256), (96 : U256), wAmt message, wAsk message, wSrc message,
          wAmt message, (612 : U256), (BitVec.ofNat 256 (selector message.data))]
        (memW [bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          (wSrc message), (3 : U256), (96 : U256)])
        (gas - wPre fork message state substate) (wState message state)
        (wSub fork message state substate)) :=
  withdraw_p3 hfork hsize hsize' hsel hstatic hacc hc1 hc2 hg

/-- `ok_withdraw` of the generated file, with the names of this file. -/
theorem ok_withdraw_at (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x2e1a7d4d)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
      isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
        (wAmt message)))) ≠ 0 ∧
      message.isStatic = false ∧ hasAccount state message.currentTarget ∧
      wPre fork message state substate ≤ gas ∧
      ∃ (z : Evm fork Nat) (w : GasMeter.gasHeld z.gas ≤ bound),
        At CODE message 2724 [wAsk message, wSrc message, wAmt message, (96 : U256), (0 : U256),
            (96 : U256), (0 : U256), (96 : U256), wAmt message, wAsk message, wSrc message,
            wAmt message, (612 : U256), (BitVec.ofNat 256 (selector message.data))]
          (memW [bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
            (wSrc message), (3 : U256), (96 : U256)])
          (gas - wPre fork message state substate) (wState message state)
          (wSub fork message state substate) z ∧
        Evm.runFrame (step fork) (step_decreases fork) bound runChild z w = .ok s :=
  ok_withdraw hfork hsize hsize' hsel start within hrun hok

/-- `withdraw(wad)` from pc 0, under every runner that meets `callee`. -/
theorem withdraw_path (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hc1 : isZero message.value ≠ 0)
    (hc2 : isZero (isZero (isZero (lessThan (storageAt state message.currentTarget (wKey message))
      (wAmt message)))) ≠ 0)
    (hbal : wAmt message ≤ etherOf state message.currentTarget)
    {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {callee : Evm fork Nat → Message fork → Evm fork Nat → Prop} {gas : Nat}
    (hg : wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message) + 2300 + 1489 ≤ gas) :
    SpecUnder fork callee (At CODE message 0 [] .empty gas state substate)
      fun s => ∃ caller msg child, callee caller msg child ∧ child.gas ≤ msg.gas ∧
        CallSend message (gas - wPre fork message state substate) (wState message state)
          (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
          calleeCode caller msg ∧
        (child.error = none → Halted false ByteArray.empty
          (gas - wPre fork message state substate -
            (callGas fork (wState message state) (wSub fork message state substate)
              (wAsk message) (wSrc message) (wAmt message)
              (gas - wPre fork message state substate)).cost + child.gas - 1489)
          (incorporateChild fork caller child).state
          (logSub2 (incorporateChild fork caller child).substate message.currentTarget WITHDRAWAL
            (wSrc message) (wordBytes (wAmt message))) s) ∧
        (child.error ≠ none → Halted true ByteArray.empty
          (gas - wPre fork message state substate -
            (callGas fork (wState message state) (wSub fork message state substate)
              (wAsk message) (wSrc message) (wAmt message)
              (gas - wPre fork message state substate)).cost + child.gas - 36)
          (incorporateChild fork caller child).state
          (incorporateChild fork caller child).substate s) := by
  have hx := callExtra_wState (fork := fork) message state substate (wSrc message) (wAmt message)
  have hcl := callGas_cost_le fork (wState message state) (wSub fork message state substate)
    (wAsk message) (wSrc message) (wAmt message) (gas - wPre fork message state substate)
  have hask := wAsk_le message
  have hbal' : wAmt message ≤ etherOf (wState message state) message.currentTarget :=
    le_of_le_of_eq hbal (etherOf_wState message state message.currentTarget).symm
  have hcode' : (wState message state).getCode
      ((wState message state).getAccount (toAddressMasked (wSrc message))).codeHash =
        .ok calleeCode := by
    rw [toAddressMasked_wSrc, getCode_wState]
    exact hcode
  refine HoareUnder.seq (HoareUnder.of_hoare
    (withdraw_at hfork hsize hsize' hsel hstatic hacc hc1 hc2 (by omega)).toHoare) ?_
  refine HoareUnder.seq (callL (callee := callee) (calleeCode := calleeCode) hfork hglam
    (by code_fact) (by code_fact) hstatic hbal' hcode' hdel hdepth
    (by rw [hx]; omega)) ?_
  rintro bound runChild meets evm ⟨caller, msg, child, hc, hle, hsend, hat⟩ within
  by_cases he : child.error = none
  · obtain ⟨after, hr, hq | hab⟩ := HoareUnder.of_hoare (callee := callee)
      (withdrawTail_p1 hfork hstatic (callFlag_ne.mpr he) (by omega)).toSpec bound runChild meets
      evm hat within
    · exact ⟨after, hr, .inl ⟨hq.1, caller, msg, child, hc, hle, hsend, fun _ => hq.2,
        fun hne => absurd he hne⟩⟩
    · exact ⟨after, hr, .inr hab⟩
  · obtain ⟨after, hr, hq | hab⟩ := HoareUnder.of_hoare (callee := callee)
      (withdrawTail_p0 hfork hstatic
        (Classical.not_not.mp fun h => he (callFlag_ne.mp h)) (by omega)).toSpec bound runChild
      meets evm hat within
    · exact ⟨after, hr, .inl ⟨hq.1, caller, msg, child, hc, hle, hsend,
        fun h => absurd h he, fun _ => hq.2⟩⟩
    · exact ⟨after, hr, .inr hab⟩

/-- Every run of `withdraw(wad)` that the interpreter loop ends with no error: no value sent
with the call, `wad` at most the token balance of the sender and at most the ether of the
contract, one message `msg` to the sender that the runner ended in a frame `child` with no
error, and the end state is the state of `child`, with the `Withdrawal` log after its logs. -/
theorem ok_withdraw_exact (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize : 4 ≤ message.data.size) (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x2e1a7d4d) {calleeCode : ByteArray}
    (hcode : state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode)
    (hdel : .pectra ≤ fork → delegatedAddress calleeCode = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (hcall : wPre fork message state substate +
      callExtra fork state substate (wSrc message) (wAmt message) ≤ gas)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
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
  have hx := callExtra_wState (fork := fork) message state substate (wSrc message) (wAmt message)
  obtain ⟨hc1, hc2, hstatic, hacc, hcg, z, w, hz, hzr⟩ :=
    ok_withdraw_at hfork hsize hsize' hsel start within hrun hok
  have hcode' : (wState message state).getCode
      ((wState message state).getAccount (toAddressMasked (wSrc message))).codeHash =
        .ok calleeCode := by
    rw [toAddressMasked_wSrc, getCode_wState]
    exact hcode
  have hbalEq := etherOf_wState message state message.currentTarget
  by_cases hbal : wAmt message ≤ etherOf state message.currentTarget
  · obtain ⟨caller, msg, child, after, hran, hle, hsend, hat, w', h'⟩ :=
      call_ok hfork hglam (by code_fact) (by code_fact) hstatic
        (le_of_le_of_eq hbal hbalEq.symm) hcode' hdel hdepth (by rw [hx]; omega) hz w hzr
    obtain ⟨hy, hcg2, ho, hgs, hst, hss⟩ := ok_withdrawTail hfork hstatic hat w' h' hok
    exact ⟨hc1, hc2, hstatic, hacc, hbal, caller, msg, child, hran, callFlag_ne.mp hy, hle,
      hsend, hcg2, ho, hgs, hst, hss⟩
  · obtain ⟨after, hat, w', h'⟩ :=
      callLow_ok hfork hglam (by code_fact) (by code_fact) hstatic
        (lt_of_eq_of_lt hbalEq (BitVec.not_le.mp hbal)) hcode' hdel (by rw [hx]; omega)
        hz w hzr
    obtain ⟨hy, -⟩ := ok_withdrawTail hfork hstatic hat w' h' hok
    exact absurd hy (by decide)

end WethVerify.Paths

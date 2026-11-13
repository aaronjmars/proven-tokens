import WethVerify.Weth.Solvent
import WethVerify.Weth.WithdrawAll
import WethVerify.Weth.TotalSupply

/-!
# Every successful run of WETH9 keeps the contract solvent

`Solvent C S`: the sum of the balance words of the 2^160 addresses is at most the ether of the
contract (Weth/Sep.lean says why it is an inequality and not an equality).

- `solvent_totalSupply`: `totalSupply()` (the hand-proved path with ADDRESS and BALANCE).
- `CalleeQuiet runChild message state substate gas code`: the assumption on the message runner
  that `withdraw` needs. It is about the ONE message that the CALL of this run of `withdraw`
  sends (`CallSend`, Evm/Call.lean): from the contract to the caller of `withdraw`, with the
  code `code`, empty call data, `wad` wei, exactly the gas that the bytes of the CALL give it
  (2300 when `wad` is not 0: asked 0 plus the stipend; at most 2300 when `wad` is 0), sent from
  a frame whose state is the start state with the balance slot of the caller lowered. It says:
  when the runner ends that message with no error, every storage word of the contract reads as
  before the message, and the ether of the contract fell by at most `wad`. It does NOT mention
  the invariant: it is a statement about what the callee does to the contract.
  It is PROVED for the runner of the interpreter and EVERY code of the callee in
  Weth/Reenter.lean (`calleeQuiet_process`): a message with 2300 gas cannot write storage and
  cannot send value, so a callee that calls back into the contract (reentrancy) changes nothing.
- `WithdrawReady`: the two facts under which `withdraw` is proved (Weth/WithdrawAll.lean): the
  fork is before Glamsterdam, and from Prague the code of the caller is no EIP-7702 delegation.
  Before Prague the second holds for every caller (`withdrawReady_prePrague`). The call depth,
  the gas and the code of the caller are NOT assumed any more: a run where the depth is at the
  limit, or the gas does not pay for the CALL, or the code is missing, ends with an error
  (`ok_withdraw_all`), and a run that ends with an error is not a case of this file.
- `solvent_withdraw`: `withdraw(wad)` under those two. The proof uses that the code lowers
  `balanceOf[msg.sender]` BEFORE the CALL: at the CALL the sum of the balances plus `wad` is at
  most the ether of the contract, so after a message that takes at most `wad` and writes no
  balance the sum is at most the ether.
- `solvent_preserved`: every run of the interpreter loop from pc 0, for any call data (the
  11 functions and the fallback), that ends with no error.

Hypotheses of `solvent_preserved`, all named: `hfork` (Berlin or later), `hsize'` (call data
shorter than 2^256 bytes), `hsep` (keccak separation, not proved), `hinv` (the invariant before,
with the value of the message already credited), `hw` (`WithdrawReady` and `CalleeQuiet`, asked
only for the selector of withdraw with no value). For the runner of the interpreter `CalleeQuiet`
is a theorem, and `solvent_preserved_process` (Weth/Reenter.lean) has no assumption on the callee.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace WethVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WethVerify.Paths WethVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-- The caller takes the state of the frame that ended the message it sent. -/
theorem incorporateChild_state (caller child : Evm fork Nat) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

/-- The assumption on the message runner, about the one message that the CALL of this run of
`withdraw` sends (`CallSend`: its gas, its value, its code, its caller, its target and the state
of the frame that sends it are all fixed by `message`, `state`, `substate` and `gas`): when the
runner ends it with no error, every storage word of the contract reads as before the message,
and the ether of the contract fell by at most `wad`. -/
def CalleeQuiet {bound : Nat} (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) (substate : Substate) (gas : Nat) (calleeCode : ByteArray) :
    Prop :=
  ∀ caller msg child, Ran runChild caller msg child → child.error = none →
    CallSend message (gas - wPre fork message state substate) (wState message state)
      (wSub fork message state substate) (wAsk message) (wSrc message) (wAmt message)
      calleeCode caller msg →
    (∀ n, storageAt child.state message.currentTarget n =
        storageAt caller.state message.currentTarget n) ∧
      (etherOf caller.state message.currentTarget).toNat ≤
        (etherOf child.state message.currentTarget).toNat + (wAmt message).toNat

/-- The facts about the fork and the caller under which `withdraw` is proved. -/
structure WithdrawReady (fork : Fork) (message : Message fork) (state : State.TransactionState) :
    Prop where
  /-- The fork is before Glamsterdam (one gas counter). -/
  glam : fork < .glamsterdam
  /-- From Prague, the code of the caller is no delegation (EIP-7702). -/
  del : ∀ c, state.getCode (state.getAccount message.caller).codeHash = .ok c →
    .pectra ≤ fork → delegatedAddress c = none

/-- Before Prague, `WithdrawReady` asks nothing of the caller. -/
theorem withdrawReady_prePrague (hglam : fork < .glamsterdam) (hpre : fork < .pectra) :
    WithdrawReady fork message state :=
  ⟨hglam, fun _ _ hp => absurd hp (Nat.not_le_of_lt hpre)⟩

/-- A successful call of `totalSupply` keeps the contract solvent. -/
theorem solvent_totalSupply (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x18160ddd)
    (hinv : Backed message.value message.currentTarget state)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Solvent message.currentTarget s.state := by
  obtain ⟨-, -, -, -, hst, -⟩ := ok_totalSupply_exact hfork hsize hsize' hsel start within hrun hok
  rw [hst]
  exact Supply.solvent_congr (fun _ => rfl) (Nat.le_refl _) hinv.solvent

/-- A successful call of `withdraw` keeps the contract solvent, when the message that its CALL
sends writes no storage of the contract and takes at most `wad` of its ether (`CalleeQuiet`). -/
theorem solvent_withdraw (hfork : .berlin ≤ fork) (hsize : 4 ≤ message.data.size)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x2e1a7d4d)
    (hsep : Sep (callKeys message))
    (hinv : Backed message.value message.currentTarget state)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (hw : WithdrawReady fork message state)
    (hkeep : ∀ calleeCode,
      state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode →
      CalleeQuiet runChild message state substate gas calleeCode)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Solvent message.currentTarget s.state := by
  obtain ⟨calleeCode, hcode, -, -, hc1, hc2, hstatic, hacc, hbal, caller, msg, child, hran, hce,
      hle, hsend, -, -, -, hst, -⟩ :=
    ok_withdraw_all hfork hw.glam hsize hsize' hsel hw.del start within hrun hok
  rw [hst, incorporateChild_state]
  obtain ⟨hstor, heth⟩ := hkeep calleeCode hcode caller msg child hran hce hsend
  have hcs := hsend.1
  have hb : Backed (wAmt message) message.currentTarget caller.state := by
    rw [hcs, toAddressMasked_wSrc]
    have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        message.caller.toU256 ∈ callKeys message := by
      simp [callKeys]
    simp only [wState, wKey, wSrc, wAmt, mask_idem, storageAt_readSlot] at hc2 ⊢
    have f := Supply.sub_fact_lt hc2
    unfold Backed Supply.Backed etherOf at *
    simp (disch := supply_side) only
      [Supply.sumBal_recordAccountRead, State.TransactionState.getAccount_recordAccountRead,
        Supply.sumBal_read, sum_bal hsep, storageAt_readSlot, getAccount_writeSlot,
        getAccount_readSlot]
    omega
  unfold Backed Supply.Backed at hb
  unfold Solvent Supply.Solvent
  rw [Supply.sumBal_congr hstor]
  omega

/-- From Berlin, every run of the interpreter loop over `CODE` from pc 0 that ends with no
error keeps the contract solvent: if the sum of the balances plus the value of the message was
at most the ether of the contract at the start of the frame, the sum of the balances is at most
the ether of the contract at its end. Any call data: the 11 functions and the fallback. -/
theorem solvent_preserved (hfork : .berlin ≤ fork) (hsize' : message.data.size < 2 ^ 256)
    (hsep : Sep (callKeys message))
    (hinv : Backed message.value message.currentTarget state)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (hw : selector message.data = 0x2e1a7d4d → message.value = 0 →
      WithdrawReady fork message state ∧ ∀ calleeCode,
        state.getCode (state.getAccount message.caller).codeHash = .ok calleeCode →
        CalleeQuiet runChild message state substate gas calleeCode)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Solvent message.currentTarget s.state := by
  have he : Ends fork evm s := Ends.run hrun
  rcases selector_cases message.data with hs | ⟨hs, hn⟩ | ⟨hs, i, hi⟩
  · exact solvent_fallbackShort hfork hs hsep hinv start he hok
  · exact solvent_fallbackOther hfork hs hsize' hn hsep hinv start he hok
  · match i, hi with
    | ⟨0, _⟩, hi =>
      have h : selector message.data = 0x06fdde03 := hi
      exact solvent_name hfork hs hsize' h hinv start he hok
    | ⟨1, _⟩, hi =>
      have h : selector message.data = 0x095ea7b3 := hi
      exact solvent_approve hfork hs hsize' h hsep hinv start he hok
    | ⟨2, _⟩, hi =>
      have h : selector message.data = 0x18160ddd := hi
      exact solvent_totalSupply hfork hs hsize' h hinv start within hrun hok
    | ⟨3, _⟩, hi =>
      have h : selector message.data = 0x23b872dd := hi
      exact solvent_transferFrom hfork hs hsize' h hsep hinv start he hok
    | ⟨4, _⟩, hi =>
      have h : selector message.data = 0x2e1a7d4d := hi
      have hc1 := (ok_withdraw_at hfork hs hsize' h start within hrun hok).1
      have hv : message.value = 0 := Classical.byContradiction fun hv => hc1 (by unfold isZero; rw [if_neg hv])
      obtain ⟨hr, hkeep⟩ := hw h hv
      exact solvent_withdraw hfork hs hsize' h hsep hinv hr hkeep start within hrun hok
    | ⟨5, _⟩, hi =>
      have h : selector message.data = 0x313ce567 := hi
      exact solvent_decimals hfork hs hsize' h hsep hinv start he hok
    | ⟨6, _⟩, hi =>
      have h : selector message.data = 0x70a08231 := hi
      exact solvent_balanceOf hfork hs hsize' h hsep hinv start he hok
    | ⟨7, _⟩, hi =>
      have h : selector message.data = 0x95d89b41 := hi
      exact solvent_symbol hfork hs hsize' h hinv start he hok
    | ⟨8, _⟩, hi =>
      have h : selector message.data = 0xa9059cbb := hi
      exact solvent_transfer hfork hs hsize' h hsep hinv start he hok
    | ⟨9, _⟩, hi =>
      have h : selector message.data = 0xd0e30db0 := hi
      exact solvent_deposit hfork hs hsize' h hsep hinv start he hok
    | ⟨10, _⟩, hi =>
      have h : selector message.data = 0xdd62ed3e := hi
      exact solvent_allowance hfork hs hsize' h hsep hinv start he hok
    | ⟨n + 11, hn⟩, _ => exact absurd hn (by omega)

end WethVerify

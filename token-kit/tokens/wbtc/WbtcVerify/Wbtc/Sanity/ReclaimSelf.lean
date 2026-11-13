import WbtcVerify.Wbtc.Sanity.Reclaim
import WbtcVerify.Wbtc.Gen.PBalanceOf
import WbtcVerify.Wbtc.Gen.PTransfer
import TokenKit.Evm.Readable
import TokenKit.Evm.Supply

/-!
# The reentrancy witness: reclaimToken(WBTC) under EthLib's real interpreter

Written by hand (not generated). A complete concrete run of `processMessage` where the token is
WBTC itself: the owner calls reclaimToken(address of WBTC) while WBTC holds 7 of its own tokens
(in its own balance slot) and the owner holds 5. The first CALL is a real direct self call of
balanceOf(WBTC), the second a real direct self call of transfer(owner, 7) with msg.sender = WBTC;
both are run by the real runner `processRunner` on the code of WBTC.

Proved:
- `runner_of_reaches`: the real runner on a message whose start frame reaches a stopped frame.
- `self_balanceOf_runs`: the real runner on the message balanceOf(WBTC) to WBTC.
- `self_transfer_runs`: the real runner on the message transfer(owner, 7) from WBTC to WBTC:
  no error, the word 1, the balance of WBTC 0, the balance of the owner 12, every other storage
  word of WBTC as before, one Transfer log.
- `reclaimToken_self_runs`: the whole run: no error, no output; after it the balance slot of
  WBTC holds 0 and the balance slot of the owner 12 (7 + 5: the sum is unchanged), every other
  storage word of WBTC (totalSupply_ in slot 1 too) reads as before, and the logs are those
  before plus the one Transfer(WBTC, owner, 7) log of the inner transfer.
- `reclaimToken_self_runs_closed`: the same at `WBTC_ADDRESS` on the concrete state `selfState`
  (the account of WBTC holds `CODE` under its keccak hash); the only hypothesis left beside the
  fork bounds is that the keccak hash of `CODE` is not the hash of the empty code
  (`hashOf CODE ≠ EMPTY_CODE_HASH`). It is true but stays a hypothesis: one try to let the kernel
  compute the keccak hash of the 4582 bytes ran the build box out of memory.

Assumed in the general form: the fork bounds (from Paris, before Glamsterdam), the word of the
contract address, the account of the contract with the code `CODE`, slot 5 (owner
`Witness.CALLER1`, not paused), the two balances, at least 16,000,000 gas, under 2^64.
Not covered: the exact gas left; the storage of other addresses after the run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace WbtcVerify.Sanity

open UsdtVerify
open TokenKit
open WbtcVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {bound : Nat}

/-! ## Words -/

/-- The word of the address of WBTC. -/
abbrev WBTCW : U256 := 0x2260fac5e5542a773aa44fbcfedf7c193bc2c599

/-- The selector of balanceOf(address). -/
def SEL_BALANCEOF : ByteArray := ⟨#[0x70, 0xa0, 0x82, 0x31]⟩

/-- The selector of transfer(address,uint256). -/
def SEL_TRANSFER : ByteArray := ⟨#[0xa9, 0x05, 0x9c, 0xbb]⟩

theorem size_SEL_BALANCEOF : SEL_BALANCEOF.size = 4 := by decide

theorem size_SEL_TRANSFER : SEL_TRANSFER.size = 4 := by decide

/-- The topic of the Transfer event. -/
abbrev TRANSFER_TOPIC : U256 :=
  100389287136786176327247604509743168900146139575972864366142685224231313322991

theorem self_m : bitwiseAnd WBTCW MASK = WBTCW := by decide

theorem self_m2 : bitwiseAnd MASK WBTCW = WBTCW := by decide

theorem self_addr {C : Address} (hC : C.toU256 = WBTCW) : toAddressMasked WBTCW = C := by
  rw [← hC]
  exact EthLib.Base.toAddressMasked_toU256 C

theorem code_size_ne : isZero (isZero (BitVec.ofNat 256 CODE.size)) ≠ 0 := by
  rw [size_CODE]
  decide

theorem delegatedAddress_CODE : delegatedAddress CODE = none := by
  have h : ¬(isValidDelegation CODE = true) := by
    simp [isValidDelegation, size_CODE, CODE_SIZE, DELEGATION_SIZE]
  unfold delegatedAddress
  rw [dif_neg h]

/-- The call data of the first CALL when the contract is WBTC: balanceOf(WBTC). -/
theorem self_data1 {C : Address} (hC : C.toU256 = WBTCW) :
    memoryReadBytes (mem1 C) 128 36 = data1 SEL_BALANCEOF WBTCW := by
  unfold mem1
  rw [hC]
  decide +kernel

/-- The call data of the second CALL when the contract is WBTC, the owner is `Witness.CALLER1`
and the first call returned 7: transfer(owner, 7). -/
theorem self_data2 {C : Address} (hC : C.toU256 = WBTCW) :
    memoryReadBytes (mem2 (memoryWrite (mem1 C) 128 (wordBytes 7))
      (bitwiseAnd (div OWNER_SLOT (256 : U256)) MASK) 7) 128 68 =
      data2 SEL_TRANSFER Witness.CALLER1W 7 := by
  unfold mem2 mem1
  rw [hC]
  decide +kernel

theorem hasAccount_callSt {S : State.TransactionState} {C A T : Address}
    (h : hasAccount S T) : hasAccount (callSt S C A) T :=
  hasAccount_readSlot (target := T) (other := C) (n := 5) h

theorem slotCost_le2100 (c : Bool) : slotCost c ≤ 2100 := by
  unfold slotCost
  split <;> omega

/-! ## The real runner on a message whose code reaches a stopped frame -/

/-- From Paris, `processRunner` on a message with a target, no value and no precompile, whose
start frame reaches a stopped frame `s` by steps with no call: it gives `s`, rolled back on an
error. -/
theorem runner_of_reaches (hparis : .paris ≤ fork) {caller : Evm fork Nat} {msg : Message fork}
    {to : Address} (lt : msg.gas < bound) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) {s : Evm fork Nat}
    (hr : Reaches (Step fork)
      (startFrame msg caller.state caller.substate.child (GasMeter.start msg.gas msg.reservoir))
      s)
    (hs : s.running = false) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1 = rollbackOnError caller.state s := by
  have hrf := (Goes.of_reaches (processRunner fork msg.gas) hr).result hs
    (start_within msg caller.state caller.substate.child)
  have hst := startState_of_paris hparis msg caller.state
  have hrf2 : Evm.runFrame (step fork) (step_decreases fork) msg.gas (processRunner fork msg.gas)
      (startFrame msg (startState fork msg caller.state) caller.substate.child
        (GasMeter.start msg.gas msg.reservoir))
      (start_within msg (startState fork msg caller.state) caller.substate.child) = .ok s := by
    rw [hst]
    exact hrf
  exact runner_of_run lt htarget noPre hv hrf2

/-! ## The two inner messages -/

/-- The real runner on balanceOf(WBTC) sent to the code of WBTC at `C`: no error, the balance
word of WBTC as output, one more read recorded in the state, no log. -/
theorem self_balanceOf_runs (hparis : .paris ≤ fork) {caller : Evm fork Nat}
    {msg : Message fork} {C : Address} (lt : msg.gas < bound)
    (hcode : msg.code = CODE) (htarget : msg.target = some C)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (hct : msg.currentTarget = C) (hdata : msg.data = data1 SEL_BALANCEOF WBTCW)
    (hg : 3000 ≤ msg.gas) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧
      child.1.output = wordBytes (storageAt caller.state C (mapSlot WBTCW (0 : U256))) ∧
      child.1.state = readSlot caller.state C (mapSlot WBTCW (0 : U256)) ∧
      child.1.substate.logs = #[] := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz : msg.data.size = 36 := by
    rw [hdata]
    exact size_data1 size_SEL_BALANCEOF _
  have hsel : selector msg.data = 0x70a08231 := by
    rw [hdata, selector_data1 size_SEL_BALANCEOF]
    decide
  have hA1 : loadWord msg.data 4 32 = WBTCW := by
    rw [hdata]
    exact Witness.arg1_data1 size_SEL_BALANCEOF _
  have hmask : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (bitwiseAnd WBTCW (1461501637330902918203684832716283019655932542975 : U256)) = WBTCW := by
    decide
  have hat := At.startFrame (message := msg) hcode caller.state caller.substate.child
  obtain ⟨s, hr, hrun, -, he, ho, -, hs, hss⟩ := (Paths.balanceOf_p1 (fork := fork)
    (message := msg) (state := caller.state) (substate := caller.substate.child) hberlin
    (by rw [hsz]; decide) (by rw [hsz]; decide) hsel (by rw [hv]; decide) (gas := msg.gas)
    (Nat.le_trans (Nat.add_le_add_left (slotCost_le2100 _) 695) (by omega))).toSpec _ hat
  have he2 : s.error = none := by simpa using he
  obtain ⟨child, hrun2, hc⟩ := runner_of_reaches hparis lt htarget noPre hv hr hrun
  rw [rollbackOnError_of_error_eq_none he2] at hc
  rw [hct, hA1, hmask] at ho hs
  refine ⟨child, hrun2, by rw [hc]; exact he2, by rw [hc]; exact ho, by rw [hc]; exact hs, ?_⟩
  rw [hc, hss]
  rfl

set_option hygiene false in
/-- Rewrites the words of the inner transfer to literals and decides. -/
local macro "self_tac" : tactic =>
  `(tactic| (simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, h5, hbC, hbO] <;> decide +kernel))

set_option maxHeartbeats 1000000 in
/-- The real runner on transfer(owner, 7) sent by WBTC to the code of WBTC at `C`, when WBTC
holds 7 tokens and the owner 5 and the token is not paused: no error, the word 1 as output; after
it the balance of WBTC is 0, the balance of the owner 12, every other storage word of `C` is as
before, and the child logged one Transfer(WBTC, owner, 7). -/
theorem self_transfer_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {caller : Evm fork Nat} {msg : Message fork} {C : Address} (hC : C.toU256 = WBTCW)
    (lt : msg.gas < bound)
    (hcode : msg.code = CODE) (htarget : msg.target = some C)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (hcaller : msg.caller = C) (hct : msg.currentTarget = C) (hstatic : msg.isStatic = false)
    (hdata : msg.data = data2 SEL_TRANSFER Witness.CALLER1W 7)
    (hacc : hasAccount caller.state C)
    (h5 : storageAt caller.state C (5 : U256) = OWNER_SLOT)
    (hbC : storageAt caller.state C (mapSlot WBTCW (0 : U256)) = 7)
    (hbO : storageAt caller.state C (mapSlot Witness.CALLER1W (0 : U256)) = 5)
    (hg : 60000 ≤ msg.gas) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = wordBytes 1 ∧
      storageAt child.1.state C (mapSlot WBTCW (0 : U256)) = 0 ∧
      storageAt child.1.state C (mapSlot Witness.CALLER1W (0 : U256)) = 12 ∧
      (∀ n : U256, n ≠ mapSlot WBTCW (0 : U256) → n ≠ mapSlot Witness.CALLER1W (0 : U256) →
        storageAt child.1.state C n = storageAt caller.state C n) ∧
      child.1.substate.logs =
        #[Readable.log3 C TRANSFER_TOPIC WBTCW Witness.CALLER1W (wordBytes 7)] := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz : msg.data.size = 68 := by
    rw [hdata]
    exact size_data2 size_SEL_TRANSFER _ _
  have hsel : selector msg.data = 0xa9059cbb := by
    rw [hdata, selector_data2 size_SEL_TRANSFER]
    decide
  have hA1 : loadWord msg.data 4 32 = Witness.CALLER1W := by
    rw [hdata]
    exact Witness.arg1_data2 size_SEL_TRANSFER _ _
  have hA2 : loadWord msg.data 36 32 = 7 := by
    rw [hdata]
    exact Witness.arg2_data2 size_SEL_TRANSFER _ _
  have hcw : msg.caller.toU256 = WBTCW := by rw [hcaller, hC]
  have hmO : bitwiseAnd (bitwiseAnd Witness.CALLER1W
      (1461501637330902918203684832716283019655932542975 : U256))
      (1461501637330902918203684832716283019655932542975 : U256) = Witness.CALLER1W := by decide
  have hacc2 : hasAccount caller.state msg.currentTarget := by
    rw [hct]
    exact hacc
  have hW : Gas.writeMax fork = 22100 := by
    show (if fork ≥ Fork.glamsterdam then 110020 else 22100) = 22100
    exact if_neg (Nat.not_le.mpr hglam)
  have hat := At.startFrame (message := msg) hcode caller.state caller.substate.child
  obtain ⟨s, hr, hrun, -, he, ho, -, hs, hss⟩ := (Paths.transfer_p6 (fork := fork)
    (message := msg) (state := caller.state) (substate := caller.substate.child) hberlin
    (by rw [hsz]; decide) (by rw [hsz]; decide) hsel hstatic hacc2
    (by rw [hv]; decide) (by self_tac) (by self_tac) (by self_tac) (by self_tac)
    (gas := msg.gas)
    (Nat.lt_of_le_of_lt
      (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.le_refl 3503) (slotCost_le2100 _)) (slotCost_le2100 _))
          (slotCost_le2100 _)) (Gas.writeCost_le hberlin _ _ _ _)) (slotCost_le2100 _))
          (Gas.writeCost_le hberlin _ _ _ _)) 2300)
      (by rw [hW]; omega))).toSpec _ hat
  have he2 : s.error = none := by simpa using he
  obtain ⟨child, hrun2, hc⟩ := runner_of_reaches hparis lt htarget noPre hv hr hrun
  rw [rollbackOnError_of_error_eq_none he2] at hc
  refine ⟨child, hrun2, by rw [hc]; exact he2, by rw [hc]; exact ho, ?_, ?_, ?_, ?_⟩
  · rw [hc, hs]
    self_tac
  · rw [hc, hs]
    self_tac
  · intro n h1 h2
    rw [hc, hs]
    simp (disch := supply_side) only [hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, h1, h2, ↓reduceIte]
  · rw [hc, hss, Readable.logs_logSub]
    simp only [Readable.logs_storeSub, Readable.logs_accessSlot, hA1, hA2, hcw, hct, hmO]
    rfl

/-! ## The whole run -/

set_option maxHeartbeats 1000000 in
/-- The reentrancy witness. reclaimToken(WBTC) sent to WBTC by its owner, when WBTC holds 7 of
its own tokens and the owner 5: `processMessage` gives a frame with no error and no output;
after it the balance slot of WBTC holds 0 and the balance slot of the owner 12, every other
storage word of WBTC reads as before, and the logs are those before plus the Transfer log of the
inner transfer. Both inner messages are real direct self calls run by the real runner. -/
theorem reclaimToken_self_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = WBTCW) {S : State.TransactionState}
    (hacc : hasAccount S C) (hcode : S.getCode (S.getAccount C).codeHash = .ok CODE)
    (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hbC : storageAt S C (mapSlot WBTCW (0 : U256)) = 7)
    (hbO : storageAt S C (mapSlot Witness.CALLER1W (0 : U256)) = 5)
    {G : Nat} (hG : 16000000 ≤ G) (hG64 : G < 2 ^ 64) :
    ∃ r, processMessage (Meter := Nat) fork (rcMsg b t C Witness.CALLER1 WBTCW G) S ss = .ok r ∧
      r.1.error = none ∧ r.1.output = ByteArray.empty ∧
      storageAt r.1.state C (mapSlot WBTCW (0 : U256)) = 0 ∧
      storageAt r.1.state C (mapSlot Witness.CALLER1W (0 : U256)) = 12 ∧
      (∀ n : U256, n ≠ mapSlot WBTCW (0 : U256) → n ≠ mapSlot Witness.CALLER1W (0 : U256) →
        storageAt r.1.state C n = storageAt S C n) ∧
      r.1.substate.logs = ss.logs ++
        #[Readable.log3 C TRANSFER_TOPIC WBTCW Witness.CALLER1W (wordBytes 7)] := by
  have hTA := self_addr hC
  have hGe : (rcMsg b t C Witness.CALLER1 WBTCW G).gas = G := rfl
  have hnpC : Precompiles.isPrecompile fork (toAddressMasked WBTCW).toU256.toNat = false := by
    rw [hTA]
    exact notPrecompile_wbtc hC
  have hcodeA : S.getCode (S.getAccount (toAddressMasked WBTCW)).codeHash = .ok CODE := by
    rw [hTA]
    exact hcode
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 WBTCW G) (code := CODE)
    rfl S ss
  -- the first call: balanceOf(WBTC), a self call
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, m_code, m_target, -, m_ct, m_np, m_val, m_data, -,
      -, hk⟩ :=
    first_call (bound := (rcMsg b t C Witness.CALLER1 WBTCW G).gas) hparis hglam
      (tok := WBTCW) rfl self_m rfl (owner_yes h5) hcodeA code_size_ne
      (fun _ => delegatedAddress_CODE) hnpC
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) hG64 (Nat.le_refl _) hstart
  rw [hTA] at m_target m_ct hcst hcss
  have hcst1 : caller.state = callSt S C C := hcst
  have m_data1 : msg.data = data1 SEL_BALANCEOF WBTCW := by
    rw [m_data]
    exact self_data1 hC
  obtain ⟨child, hrun, cerr, cout, cst, clogs⟩ :=
    self_balanceOf_runs hparis (caller := caller) hlt m_code m_target m_np m_val m_ct m_data1
      (by omega)
  obtain ⟨a1, hga1, hba1, hgo1, hat1⟩ := hk hlt child hrun
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr]
    rfl
  have hout1 : child.1.output = wordBytes 7 := by
    rw [cout, hcst1, storageAt_callSt, hbC]
  have hl1 : (incorporateChild fork caller child.1).substate.logs = ss.logs := by
    rw [inc_logs cerr, clogs, hcss]
    simp
  rw [hflag, hout1, extract_word, cst, hcst1] at hat1
  obtain ⟨hM1s, hM1fp, hM1w⟩ := mem_after (7 : U256) (mem1_size C) (by decide) (mem1_fp C)
  have hrd : isZero (lessThan (BitVec.ofNat 256 (wordBytes 7).size) (32 : U256)) ≠ 0 := by
    rw [size_wordBytes]
    decide
  -- the state after the first call
  have hacc1 : hasAccount (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C :=
    hasAccount_readSlot (hasAccount_callSt hacc)
  have hcode2 : (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))).getCode
      ((readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))).getAccount
        (toAddressMasked WBTCW)).codeHash = .ok CODE := hcodeA
  -- the second call: transfer(owner, 7), a self call with msg.sender = WBTC
  obtain ⟨caller2, msg2, hlt2, hmg2, hcst2, hcss2, n_code, n_target, n_caller, n_ct, n_np,
      n_val, n_data, -, n_static, hk2⟩ :=
    second_call (bound := (rcMsg b t C Witness.CALLER1 WBTCW G).gas) hparis hglam
      (st := readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) self_m2 hM1s hM1fp hM1w hrd
      (c := CODE) hcode2 code_size_ne (fun _ => delegatedAddress_CODE) hnpC
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) (by omega) hba1 hat1
  rw [hTA] at n_target n_ct hcst2 hcss2
  have hcst3 : caller2.state =
      callSt (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C C := hcst2
  have hown : ownW (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C =
      bitwiseAnd (div OWNER_SLOT (256 : U256)) MASK := by
    show bitwiseAnd (div (storageAt (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C
      (5 : U256)) (256 : U256)) MASK = _
    rw [storageAt_readSlot, storageAt_callSt, h5]
  have n_data1 : msg2.data = data2 SEL_TRANSFER Witness.CALLER1W 7 := by
    rw [n_data]
    show memoryReadBytes (mem2 (memoryWrite (mem1 C) 128 (wordBytes 7))
      (ownW (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C) 7) 128 68 = _
    rw [hown]
    exact self_data2 hC
  obtain ⟨child2, hrun2, cerr2, cout2, c2C, c2O, c2other, c2logs⟩ :=
    self_transfer_runs hparis hglam (caller := caller2) hC hlt2 n_code n_target n_np n_val
      n_caller n_ct n_static n_data1
      (by rw [hcst3]; exact hasAccount_callSt hacc1)
      (by rw [hcst3, storageAt_callSt, storageAt_readSlot, storageAt_callSt, h5])
      (by rw [hcst3, storageAt_callSt, storageAt_readSlot, storageAt_callSt, hbC])
      (by rw [hcst3, storageAt_callSt, storageAt_readSlot, storageAt_callSt, hbO])
      (by omega)
  obtain ⟨a2, y1, y2, y3, t2, hga2, hgo2, hat2⟩ := hk2 hlt2 child2 hrun2
  have hflag2 : (if child2.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr2]
    rfl
  have hl2 : (incorporateChild fork caller2 child2.1).substate.logs = ss.logs ++
      #[Readable.log3 C TRANSFER_TOPIC WBTCW Witness.CALLER1W (wordBytes 7)] := by
    rw [inc_logs cerr2, c2logs, hcss2]
    show (incorporateChild fork caller child.1).substate.logs ++ _ = _
    rw [hl1]
  rw [hflag2, cout2, extract_word] at hat2
  obtain ⟨hM2s, hM2fp⟩ := mem2_facts
    (ownW (readSlot (callSt S C C) C (mapSlot WBTCW (0 : U256))) C) 7 hM1s hM1fp
  obtain ⟨hM3s, hM3fp, hM3w⟩ := mem_after (1 : U256) hM2s (by decide) hM2fp
  have hrd2 : isZero (lessThan (BitVec.ofNat 256 (wordBytes 1).size) (32 : U256)) ≠ 0 := by
    rw [size_wordBytes]
    decide
  obtain ⟨s, hr, hrun3, herr, hout, hst, hsub⟩ :=
    seg3_ok (Nat.le_trans (by decide) hparis) hM3s hM3fp hM3w hrd2 (by decide) (by omega) hat2
  obtain ⟨r, hpm, hr1⟩ := message_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC))
    rfl ((hgo1.trans hgo2).trans (Goes.of_reaches _ hr)) hrun3
  rw [rollbackOnError_of_error_eq_none herr] at hr1
  have hsame : ∀ n : U256, storageAt caller2.state C n = storageAt S C n := fun n => by
    rw [hcst3, storageAt_callSt, storageAt_readSlot, storageAt_callSt]
  refine ⟨r, hpm, by rw [hr1]; exact herr, by rw [hr1]; exact hout, by rw [hr1, hst]; exact c2C,
    by rw [hr1, hst]; exact c2O, ?_, by rw [hr1, hsub]; exact hl2⟩
  intro n h1 h2
  rw [hr1, hst, c2other n h1 h2]
  exact hsame n

/-! ## The closed form -/

/-- The state of the reentrancy witness: at `WBTC_ADDRESS` the account holds `CODE`, the owner
is `Witness.CALLER1`, WBTC holds 7 of its own tokens and the owner 5. -/
abbrev selfState : State.TransactionState :=
  codeState WBTC_ADDRESS
    [((5 : U256), OWNER_SLOT), (mapSlot WBTCW (0 : U256), (7 : U256)),
      (mapSlot Witness.CALLER1W (0 : U256), (5 : U256))] WBTC_ADDRESS CODE

/-- `codeState` has the account that holds the code. -/
theorem hasAccount_codeState_self (C : Address) (kvs : List (U256 × U256)) (code : ByteArray) :
    hasAccount (codeState C kvs C code) C := by
  have e : (codeState C kvs C code).getAccountOptional C = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self (sState C kvs) C (some ⟨1, 0, hashOf code⟩)
  unfold hasAccount
  rw [e]
  simp

theorem selfState_5 : storageAt selfState WBTC_ADDRESS (5 : U256) = OWNER_SLOT := by
  rw [storageAt_codeState, storageAt_sState_cons, if_pos rfl]

theorem selfState_C : storageAt selfState WBTC_ADDRESS (mapSlot WBTCW (0 : U256)) = 7 := by
  simp only [storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil] <;>
    decide +kernel

theorem selfState_O :
    storageAt selfState WBTC_ADDRESS (mapSlot Witness.CALLER1W (0 : U256)) = 5 := by
  simp only [storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil] <;>
    decide +kernel

/-- The reentrancy witness, closed at `WBTC_ADDRESS` on `selfState`. The one hypothesis beside
the fork bounds: the keccak hash of the code of WBTC is not the hash of the empty code. -/
theorem reclaimToken_self_runs_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ r, processMessage (Meter := Nat) fork
        (rcMsg b t WBTC_ADDRESS Witness.CALLER1 WBTCW 16000000) selfState ss = .ok r ∧
      r.1.error = none ∧ r.1.output = ByteArray.empty ∧
      storageAt r.1.state WBTC_ADDRESS (mapSlot WBTCW (0 : U256)) = 0 ∧
      storageAt r.1.state WBTC_ADDRESS (mapSlot Witness.CALLER1W (0 : U256)) = 12 ∧
      (∀ n : U256, n ≠ mapSlot WBTCW (0 : U256) → n ≠ mapSlot Witness.CALLER1W (0 : U256) →
        storageAt r.1.state WBTC_ADDRESS n = storageAt selfState WBTC_ADDRESS n) ∧
      r.1.substate.logs = ss.logs ++
        #[Readable.log3 WBTC_ADDRESS TRANSFER_TOPIC WBTCW Witness.CALLER1W (wordBytes 7)] :=
  reclaimToken_self_runs hparis hglam b t ss wbtc_address_word
    (hasAccount_codeState_self _ _ _) (getCode_codeState _ _ _ hH) selfState_5 selfState_C
    selfState_O (Nat.le_refl _) (by decide)

end WbtcVerify.Sanity

import BnbVerify.Bnb.Seq
import TokenKit.Evm.Payee

/-!
# Sanity: the local assumption of withdrawEther holds for EthLib's real runner

`Withdraw.supply_withdrawEther` and the sequence theorems of Bnb/Seq.lean take the local
assumption `Withdraw.KeepsInv runChild message S` on the runner: the one message that the CALL of
`withdrawEther` sends, when it ends with no error, keeps `Inv`. This file shows that the
assumption is TRUE for `processRunner`, the runner of EthLib's interpreter, for two real callees,
as upstream's `Usdt/Sanity/Process.lean` does for USDT, and gives a full run.

Written by hand (not generated).

- `PlainOwner fork message S`: in the state `S`, the owner (slot 4) has no code or the code of
  one byte STOP, and is no precompile.
- `processRunner_keepsInv`: from Paris, for a contract account that holds code and a
  `PlainOwner`, `KeepsInv (processRunner fork bound) message S` holds, for every bound. The only
  change of state that such a message makes is the move of its value, and a move of ether keeps
  the storage of a contract with code (TokenKit's `payee_keeps_storage`).
  `keepsInv_noCode` and `keepsInv_stop` are the two cases by name.
- `supply_withdrawEther_plain`: `supply_withdrawEther` for `processRunner` with no assumption
  on the runner.
- `process_step_inv_plain`: from Paris, EVERY top-level message of `CODE` to the contract (any
  selector, `withdrawEther` too) that `processMessage` ends keeps `Inv`, with no assumption on
  the runner; a call of `withdrawEther` asks for a fork before Glamsterdam and a `PlainOwner`.
- `withdrawEther_pays`: a full run with the real runner and a nonzero amount. From Paris and
  before Glamsterdam, in any state where slot 4 holds the word of `caller`, `caller` has no
  code, is not the contract and is no precompile, the contract holds at least 1 wei: the call
  `withdrawEther(1)` from `caller`, run by the interpreter loop under `processRunner` from pc 0,
  ends with no error and no output; the owner has 1 wei more and the contract 1 wei less.
- `withdrawEther_pays_sample`: the same in a concrete state (one account at the contract with
  1 wei and any code hash `H`), so the hypotheses on the state of `withdrawEther_pays` can all
  hold at once. What is left as a hypothesis: the two addresses differ and the owner is no
  precompile.
- `withdrawEther_pays_closed`: the same for two fixed addresses, with no hypothesis left but
  the fork range (from Paris, before Glamsterdam).

Amount 0 and the failure cases need no separate statement: `withdrawEther_run`,
`supply_withdrawEther` and `process_step_withdraw` have no side condition on the amount, the
balance, the depth or the gas. With amount 0 the message moves no value and `KeepsInv` holds as
for any amount (`payee_keeps_storage` covers a message that moves nothing). A run where the CALL
sends no message or its message fails has an error (`withdrawEther_run`), and the message layer
rolls such a call back (`untouched_process_failed`, an `Untouched` step).

Not covered: an owner with other code (a contract that runs opcodes on receipt). For such an
owner `KeepsInv` stays an assumption; it is true when the 2300 gas of the message cannot write
the storage of the contract, which is not proved here.
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
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The assumption holds for `processRunner` -/

/-- In the state `S` the owner has no code, or the code of one byte STOP, and is no
precompile. -/
def PlainOwner (fork : Fork) (message : Message fork) (S : State.TransactionState) : Prop :=
  (S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok .empty ∨
    S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok Payee.STOP_CODE) ∧
  Precompiles.isPrecompile fork (ownerOf message S).toU256.toNat = false

/-- The code of a plain owner is no EIP-7702 delegation. -/
theorem hdel_of_plain {message : Message fork} {S : State.TransactionState}
    (h : PlainOwner fork message S) :
    ∀ c, S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none := by
  intro c hc _
  rcases h.1 with h | h
  · rw [hc] at h
    cases h
    exact Payee.delegatedAddress_empty
  · rw [hc] at h
    cases h
    exact Payee.delegatedAddress_stop

/-- From Paris, the local assumption of `withdrawEther` is true for EthLib's real runner, for
every bound, when the contract account holds code and the owner is plain. -/
theorem processRunner_keepsInv (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState} (hown : PlainOwner fork message S)
    (hC : (S.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    KeepsInv (processRunner (Meter := Nat) fork bound) message S := by
  refine fun caller msg lt child hch hpay herr hinv => ?_
  obtain ⟨c, hc, hreads, -, -, mt, mca, mcode, -⟩ := hpay
  have hcode' : msg.code = .empty ∨ msg.code = Payee.STOP_CODE := by
    rw [mcode]
    rcases hown.1 with h | h
    · rw [hc] at h
      exact .inl (Except.ok.inj h)
    · rw [hc] at h
      exact .inr (Except.ok.inj h)
  have hpre : precompileAddress fork msg = none := by
    simp [precompileAddress, mca, hown.2]
  have hC' : (caller.state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH := by
    rw [readsAs_getAccount hreads]
    exact hC
  exact (Supply.inv2_congr (fun n => Payee.payee_keeps_storage hparis ⟨lt, child, hch, rfl⟩
    hcode' mt hpre hC' herr n)).mpr hinv

/-- Case (a): the owner has no code. -/
theorem keepsInv_noCode (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok .empty)
    (hnp : Precompiles.isPrecompile fork (ownerOf message S).toU256.toNat = false)
    (hC : (S.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    KeepsInv (processRunner (Meter := Nat) fork bound) message S :=
  processRunner_keepsInv hparis ⟨.inl hcode, hnp⟩ hC

/-- Case (b): the code of the owner is the one byte STOP. -/
theorem keepsInv_stop (hparis : .paris ≤ fork) {bound : Nat} {message : Message fork}
    {S : State.TransactionState}
    (hcode : S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok Payee.STOP_CODE)
    (hnp : Precompiles.isPrecompile fork (ownerOf message S).toU256.toNat = false)
    (hC : (S.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH) :
    KeepsInv (processRunner (Meter := Nat) fork bound) message S :=
  processRunner_keepsInv hparis ⟨.inr hcode, hnp⟩ hC

/-- The supply invariant through `withdrawEther` under EthLib's real runner, from Paris and
before Glamsterdam, with NO assumption on the runner: the contract account holds code and the
owner is plain. -/
theorem supply_withdrawEther_plain (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hown : PlainOwner fork message state)
    (hC : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (hinv : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_withdrawEther (Nat.le_trans (by decide) hparis) hglam hsize' hsel (hdel_of_plain hown)
    (processRunner_keepsInv hparis hown hC) hinv start within hrun hok

/-- From Paris, EVERY top-level message of `CODE` to the contract (any selector) that EthLib's
`processMessage` ends keeps `Inv`, with no assumption on the runner. `K`: the hypothesis on
keccak, for a selector other than `withdrawEther`. `hw`: for `withdrawEther`, the fork is before
Glamsterdam and the owner is plain. `hcode`: the contract account holds code. -/
theorem process_step_inv_plain (hparis : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hmc : message.code = CODE)
    (noPrecompile : precompileAddress fork message = none)
    (hsize : message.data.size < 2 ^ 256)
    (hcode : (state.getAccount message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (K : selector message.data ≠ 0x3bed33ce → Sep (callKeys message))
    (hw : selector message.data = 0x3bed33ce →
      fork < .glamsterdam ∧ PlainOwner fork message state)
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ message.gas }}
    (hproc : processMessage fork message state substate = .ok ended)
    (hI : Inv message.currentTarget state) : Inv message.currentTarget ended.val.state :=
  process_step_inv_all hparis hmc noPrecompile hsize hcode K
    (fun hsel => ⟨(hw hsel).1, hdel_of_plain (hw hsel).2,
      processRunner_keepsInv hparis (hw hsel).2 hcode⟩) hproc hI

/-! ## A full run under `processRunner`, with a nonzero amount -/

/-- From Paris and before Glamsterdam, a full run of `withdrawEther(1)` under EthLib's real
runner. In any state `S` where slot 4 of the contract `C` holds the word of `caller`, `caller`
has no code, is not `C` and is no precompile, and `C` holds at least 1 wei: the interpreter loop
under `processRunner`, from pc 0, ends with no error and no output; the owner has 1 wei more and
the contract 1 wei less. -/
theorem withdrawEther_pays (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (S : State.TransactionState) (ss : Substate)
    (hne : C ≠ caller)
    (hk : storageAt S C 4 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)
    (hcodeO : S.getCode (S.getAccount caller).codeHash = .ok .empty)
    (hnp : Precompiles.isPrecompile fork caller.toU256.toNat = false)
    (hbal : (1 : U256) ≤ (S.getAccount C).balance)
    (hfit : (S.getAccount caller).balance.toNat + (1 : U256).toNat < 2 ^ 256) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_withdrawEther b t C caller) 0 [] .empty gas S ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = none ∧ s.output = ByteArray.empty ∧
      (s.state.getAccount caller).balance = (S.getAccount caller).balance + 1 ∧
      (s.state.getAccount C).balance = (S.getAccount C).balance - 1 := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hdata : (m_withdrawEther b t C caller).data = data1 SEL_withdrawEther 1 := rfl
  have hsz : (m_withdrawEther b t C caller).data.size = 36 := by
    rw [hdata]; exact size_data1 size_SEL_withdrawEther _
  have hsl : selector (m_withdrawEther b t C caller).data = selector SEL_withdrawEther := by
    rw [hdata]; exact selector_data1 size_SEL_withdrawEther _
  have hA1 : loadWord (m_withdrawEther b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data1 size_SEL_withdrawEther _
  have hk' : storageAt S (m_withdrawEther b t C caller).currentTarget 4 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 := hk
  have e1 : askedWord (m_withdrawEther b t C caller) = 0 := by
    show mul (isZero (loadWord (m_withdrawEther b t C caller).data 4 32)) (2300 : U256) = 0
    rw [hA1]; decide
  have hown : toAddressMasked (ownerWord (m_withdrawEther b t C caller) S) = caller := by
    rw [ownerWord_eq, hk', mask_idem]
    exact toAddressMasked_mask_toU256 caller
  -- the gas of the run: the path to the CALL, the price of the CALL, and 2400 more
  obtain ⟨E, hE⟩ : ∃ E, E = callExtra fork (atCall (m_withdrawEther b t C caller) S)
      (subAtCall (m_withdrawEther b t C caller) ss)
      (ownerWord (m_withdrawEther b t C caller) S) 1 := ⟨_, rfl⟩
  have hspec := withdrawEther_to_call (fork := fork) (message := m_withdrawEther b t C caller)
    (state := S) (substate := ss) hberlin
    (by rw [hsz]; decide) (by rw [hsl]; decide) rfl
    (by rw [hk']; exact (mask_idem _).symm)
    (gas := prefixCost (m_withdrawEther b t C caller) ss + E + 2400) (by omega)
  obtain ⟨z, hr, hz⟩ := hspec
    (sFrame (m_withdrawEther b t C caller) S ss _) (at_sFrame _ rfl _ _ _)
  rw [e1, hA1] at hz
  obtain ⟨zc, zj, zm, zp, zst, zmem, zg, zrun, zerr, zout, zs, zss⟩ := id hz
  -- the loop runs the start frame as it runs the frame at the CALL
  have hrun1 := runFrame_eq_of_reaches
    (bound := prefixCost (m_withdrawEther b t C caller) ss + E + 2400)
    (runChild := processRunner fork (prefixCost (m_withdrawEther b t C caller) ss + E + 2400))
    Step.gasHeld_le Step.runFrame_eq (reaches_toStep hr) (Nat.le_refl _)
  -- the step of the CALL sends the message
  have hstep : step fork z = callStep .call z := step_at_call hz (by code_fact) (by code_fact)
  have hext : extendMemory z.memory.size [((96 : U256), (0 : U256)), ((96 : U256), (0 : U256))] =
      ⟨0, 0⟩ := by
    simp [extendMemory]
  have hprice : (callBaseCost fork (decide (toAddressMasked
        (ownerWord (m_withdrawEther b t C caller) S) ∉ z.substate.accessedAddresses)) +
      callNewAccountCost fork z.state
        (toAddressMasked (ownerWord (m_withdrawEther b t C caller) S)) 1 +
      callValueCost fork 1) +
      (extendMemory z.memory.size [((96 : U256), (0 : U256)), ((96 : U256), (0 : U256))]).cost =
      E := by
    rw [hext, zs, zss, hE]
    rfl
  have h0 : (0 : U256).toNat = 0 := by decide
  obtain ⟨cl, msg, hsent, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, m0, m1, m2, m3, m4,
      m5, m6, m7, m8, m9, m10⟩ :=
    callStep_value hberlin hglam zst (by decide)
      (by rw [zm]; rfl)
      (by rw [zs, zm]; exact hbal)
      (calleeCode := ByteArray.empty) (by rw [zs, hown]; exact hcodeO)
      (fun _ => Payee.delegatedAddress_empty)
      (by rw [zm]; show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide)
      (by rw [hprice, zg]; omega)
  -- the gas of the message and of the calling frame
  have hmg : msg.gas = (TokenKit.callGas fork (atCall (m_withdrawEther b t C caller) S)
      (subAtCall (m_withdrawEther b t C caller) ss) 0
      (ownerWord (m_withdrawEther b t C caller) S) 1 z.gas).subCall := by
    rw [m0, hext, zs, zss]
  have hcl : cl.gas = z.gas - (TokenKit.callGas fork (atCall (m_withdrawEther b t C caller) S)
      (subAtCall (m_withdrawEther b t C caller) ss) 0
      (ownerWord (m_withdrawEther b t C caller) S) 1 z.gas).cost := by
    rw [c7, hext, zs, zss]
    rfl
  have hsub := callGas_subCall_le fork (atCall (m_withdrawEther b t C caller) S)
    (subAtCall (m_withdrawEther b t C caller) ss) 0
    (ownerWord (m_withdrawEther b t C caller) S) 1 z.gas
  have hcost := callGas_cost_le fork (atCall (m_withdrawEther b t C caller) S)
    (subAtCall (m_withdrawEther b t C caller) ss) 0
    (ownerWord (m_withdrawEther b t C caller) S) 1 z.gas
  rw [← hE, h0] at hcost
  have hstip : (0 : U256).toNat + (if (1 : U256) = 0 then 0 else CALL_STIPEND) = 2300 := by
    decide
  rw [hstip] at hsub
  have hlt : msg.gas < prefixCost (m_withdrawEther b t C caller) ss + E + 2400 := by omega
  have hclg : 2400 ≤ cl.gas := by omega
  -- the runner runs the message: it moves 1 wei and stops
  have hcs : ∀ a, cl.state.getAccount a = S.getAccount a := by
    intro a
    rw [c11, zs]
    rfl
  obtain ⟨moved, hm⟩ := (moveEther_isOk_iff (fork := fork) (tx := cl.state) (sender := C)
    (recipient := caller) (amount := 1) hne).mpr
    ⟨by rw [hcs]; exact BitVec.not_lt.mpr hbal, by rw [hcs]; exact hfit⟩
  have hm' : cl.state.moveEther fork msg.caller msg.currentTarget msg.value = .ok moved := by
    rw [m1, m2, m7, zm, hown]
    exact hm
  have hpre : precompileAddress fork msg = none := by
    simp [precompileAddress, m4, hown, hnp]
  obtain ⟨child, hch, hce, hcst⟩ := Payee.noCode_message_runs hparis hlt m5 m3 hpre
    ⟨m8, by rw [m7]; decide⟩ hm'
  -- the calling frame resumes
  obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    resumeCall_eq (fork := fork) (caller := cl) (child := child.1) (o := 96) (osz := 0)
      (by rw [c5]; first | decide | simp [STACK_LIMIT])
  obtain ⟨wafter, hrun2⟩ : ∃ w : GasMeter.gasHeld after.gas ≤
      prefixCost (m_withdrawEther b t C caller) ss + E + 2400,
      Evm.runFrame (step fork) (step_decreases fork)
        (prefixCost (m_withdrawEther b t C caller) ss + E + 2400)
        (processRunner fork (prefixCost (m_withdrawEther b t C caller) ss + E + 2400)) z
        (Nat.le_trans ((reaches_toStep hr).gasHeld_le Step.gasHeld_le) (Nat.le_refl _)) =
      Evm.runFrame (step fork) (step_decreases fork)
        (prefixCost (m_withdrawEther b t C caller) ss + E + 2400)
        (processRunner fork (prefixCost (m_withdrawEther b t C caller) ss + E + 2400)) after w :=
    ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) hlt hch hres⟩
  have hat : At CODE (m_withdrawEther b t C caller) 3011
      ((1 : U256) :: (96 : U256) :: (1 : U256) :: (0 : U256) ::
        ownerWord (m_withdrawEther b t C caller) S :: (1 : U256) :: (701 : U256) ::
        BitVec.ofNat 256 (selector (m_withdrawEther b t C caller).data) :: [])
      after.memory after.gas after.state after.substate after :=
    ⟨a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
      by rw [a4, c4, zp], by rw [a5, c5, hce]; rfl, rfl, rfl, a8.trans (c8.trans zrun),
      a9.trans (c9.trans zerr), a10.trans (c10.trans zout), rfl, rfl⟩
  obtain ⟨s, hrf, hq⟩ := Gas.SpecG.runFrame
    (tail_ok (fork := fork) (message := m_withdrawEther b t C caller) (state := after.state)
      (substate := after.substate) (mem := after.memory) (gas := after.gas)
      (f := 1) (by decide) (by simp) (by rw [a7]; omega))
    (bound := prefixCost (m_withdrawEther b t C caller) ss + E + 2400)
    (runChild := processRunner fork (prefixCost (m_withdrawEther b t C caller) ss + E + 2400))
    hat wafter
  obtain ⟨-, he, ho, -, hs, -⟩ := hq
  have hsm : s.state = moved := by
    rw [hs, a11, incorporateChild_state, hcst]
  obtain ⟨-, -, hbs, hbr, -⟩ := moveEther_eq_ok hne hm
  refine ⟨prefixCost (m_withdrawEther b t C caller) ss + E + 2400,
    sFrame (m_withdrawEther b t C caller) S ss
      (prefixCost (m_withdrawEther b t C caller) ss + E + 2400), s, at_sFrame _ rfl _ _ _,
    ⟨Nat.le_refl _, ?_⟩, by simpa using he, ho, ?_, ?_⟩
  · exact (hrun1.trans hrun2).trans hrf
  · rw [hsm, hbr, hcs]
  · rw [hsm, hbs, hcs]

/-! ## A concrete state for the run -/

/-- The state of the witness: `s_withdrawEther` (slot 4 holds the word of `caller`) where the
account of `C` holds 1 wei and has the code hash `H`. -/
abbrev s_pays (C caller : Address) (H : EthLib.Base.Hash32) : State.TransactionState :=
  (s_withdrawEther C caller).setAccount C (some ⟨1, 1, H⟩)

/-- The run of `withdrawEther_pays` in the concrete state `s_pays C caller H`, for any code hash
`H` of the contract account: the hypotheses on the state all hold. Left as hypotheses: `C` is
not `caller`, and `caller` is no precompile. -/
theorem withdrawEther_pays_sample (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (H : EthLib.Base.Hash32) (ss : Substate) (hne : C ≠ caller)
    (hnp : Precompiles.isPrecompile fork caller.toU256.toNat = false) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_withdrawEther b t C caller) 0 [] .empty gas (s_pays C caller H) ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = none ∧ s.output = ByteArray.empty ∧
      (s.state.getAccount caller).balance = 1 ∧ (s.state.getAccount C).balance = 0 := by
  have hC : (s_pays C caller H).getAccount C = ⟨1, 1, H⟩ := by
    simp [State.TransactionState.getAccount, getAccountOptional_setAccount_self]
  have hO : (s_pays C caller H).getAccount caller = State.EMPTY_ACCOUNT := by
    unfold State.TransactionState.getAccount
    rw [getAccountOptional_setAccount_of_ne _ _ (Ne.symm hne)]
    have hnone : (s_withdrawEther C caller).getAccountOptional caller = none := by
      simp [sState, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
        State.State.getAccountOptional, Std.ExtTreeMap.getElem?_insert, hne]
    rw [hnone]
    rfl
  have hk : storageAt (s_pays C caller H) C 4 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 := by
    show storageAt (sState C [((4 : U256),
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)]) C 4 = _
    rw [storageAt_sState_cons, if_pos rfl]
  obtain ⟨gas, evm, s, hat, hrun, he, ho, h1, h2⟩ := withdrawEther_pays hparis hglam b t C caller
    (s_pays C caller H) ss hne hk
    (by rw [hO]; simp [State.TransactionState.getCode, State.EMPTY_ACCOUNT])
    hnp (by rw [hC]; show (1 : U256) ≤ 1; decide) (by rw [hO]; decide)
  refine ⟨gas, evm, s, hat, hrun, he, ho, ?_, ?_⟩
  · rw [h1, hO]
    decide
  · rw [h2, hC]
    show (1 : U256) - 1 = 0
    decide

/-- The address of the word 0x1000 is no precompile, at any fork. -/
theorem notPrecompile_sample :
    Precompiles.isPrecompile fork (toAddressMasked (0x1000 : U256)).toU256.toNat = false := by
  rw [EthLib.Base.toNat_toU256_toAddressMasked]
  have h : (0x1000 : U256).toNat % 2 ^ 160 = 4096 := by decide
  rw [h]
  rfl

/-- The addresses of the words 0x2000 and 0x1000 differ. -/
theorem ne_sample : toAddressMasked (0x2000 : U256) ≠ toAddressMasked (0x1000 : U256) := by
  intro h
  have h2 := congrArg (fun a : Address => a.toU256.toNat) h
  simp only [EthLib.Base.toNat_toU256_toAddressMasked] at h2
  exact absurd h2 (by decide)

/-- A full run with no hypothesis left but the fork range: the contract at the address of the
word 0x2000, the owner at the address of the word 0x1000 (no code, no precompile). The call
`withdrawEther(1)` from the owner, run by the interpreter loop under EthLib's `processRunner`
from pc 0, ends with no error; the owner ends with 1 wei and the contract with 0. -/
theorem withdrawEther_pays_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (H : EthLib.Base.Hash32)
    (ss : Substate) :
    ∃ (C caller : Address) (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_withdrawEther b t C caller) 0 [] .empty gas (s_pays C caller H) ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = none ∧ s.output = ByteArray.empty ∧
      (s.state.getAccount caller).balance = 1 ∧ (s.state.getAccount C).balance = 0 :=
  ⟨_, _, withdrawEther_pays_sample hparis hglam b t _ _ H ss ne_sample notPrecompile_sample⟩

end BnbVerify.Withdraw

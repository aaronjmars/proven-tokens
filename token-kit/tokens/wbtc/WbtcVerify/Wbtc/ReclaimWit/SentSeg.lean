import WbtcVerify.Wbtc.Trace
import WbtcVerify.Wbtc.Sanity.ReclaimRun

/-!
# The two calls of reclaimToken, with the messages that the frame sends

Fix of audit 4 (the gap of LINK-4, here for WBTC). The lemmas `call_run`, `seg1`, `seg2`
(`Sanity/ReclaimSeg.lean`) and `first_call`, `second_call` (`Sanity/ReclaimRun.lean`) say where
the frame of reclaimToken goes after each of its two CALLs. Here are the same lemmas with one
more fact (same statements, same proofs, made from those by a script; the old lemmas
are kept): every message that the frame sends (`Trace.Sent`) is the message of the CALL, or a
message that the frame after the call sends.

- `call_run_s`: the step of a CALL.
- `seg1_s`, `seg2_s`: from pc 0 to the frame after the first CALL; from there to the frame after
  the second CALL.
- `first_call_s`, `second_call_s`: the same under the real runner `processRunner`.

With these the run-local condition `Trace.CleanFrame` of a concrete run of reclaimToken needs
only the two messages of the two CALLs.

Assumed: as in the lemmas that they copy (Paris or Berlin ≤ fork < Glamsterdam).
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

theorem call_run_s (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {code : ByteArray} {message : Message fork} {pc : Nat} {g a i isz o osz : U256}
    {rest : List U256} {mem : ByteArray} {gas : Nat} {state : State.TransactionState}
    {substate : Substate} {z : Evm fork Nat}
    (hz : UsdtVerify.At code message pc (g :: a :: 0 :: i :: isz :: o :: osz :: rest) mem gas
      state substate z)
    (hstep : step fork z = callStep .call z)
    (hext : extendMemory mem.size [(i, isz), (o, osz)] = ⟨0, 0⟩)
    {c : ByteArray}
    (hcode : state.getCode (state.getAccount (toAddressMasked a)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hrest : rest.length < STACK_LIMIT)
    (hgas : 2600 ≤ gas) (hask : gas ≤ g.toNat)
    (runChild : MessageRunner fork Nat bound) (hb : gas ≤ bound) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (gas - 2600) / 2 ≤ msg.gas ∧
      caller.state = (state.recordAccountRead (toAddressMasked a)).recordAccountRead
        message.currentTarget ∧
      caller.substate = warm substate (toAddressMasked a) ∧
      Sent msg message.currentTarget (toAddressMasked a) c
        (memoryReadBytes mem i.toNat isz.toNat) (message.depth + 1) message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (gas - 2600) / 64 ≤ after.gas ∧ Goes runChild z after ∧
          (∀ c0 m0, Trace.Sent runChild z c0 m0 →
            (c0 = caller ∧ m0 = msg) ∨ Trace.Sent runChild after c0 m0) ∧
          Logic.At code message (pc + 1) ((if child.1.error.isNone then 1 else 0) :: rest)
            (memoryWrite mem o.toNat
              (child.1.output.extract 0 (min osz.toNat child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨zc, zj, zm, zp, zst, zmem, zg, zrun, zerr, zout, zs, zss⟩ := id hz
  have h0 : extendMemory z.memory.size [(i, isz), (o, osz)] = ⟨0, 0⟩ := by
    rw [zmem]
    exact hext
  have h0c : (extendMemory z.memory.size [(i, isz), (o, osz)]).cost = 0 := by rw [h0]
  have h0e : (extendMemory z.memory.size [(i, isz), (o, osz)]).expandBy = 0 := by rw [h0]
  have hE : 100 ≤ callBaseCost fork
        (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) ∧
      callBaseCost fork (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) ≤ 2600 := by
    rw [callBaseCost_of_berlin hfork hglam]
    split <;> omega
  generalize hEdef : callBaseCost fork
    (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) = E at hE
  obtain ⟨cl, msg, hsent, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ :=
    callStep_call hfork zst (by rw [zs]; exact hcode) hdel (by rw [zm]; exact hdepth)
      (by rw [h0c, hEdef, zg]; omega)
  rw [h0c, hEdef] at m1 c7
  rw [h0e, memoryExtend_zero] at c6 m7
  obtain ⟨k1, k2⟩ := mcg_exact (fork := fork) htw (asked := g.toNat) (gas := z.gas) (E := E)
    (by rw [zg]; omega) (by rw [zg]; omega)
  rw [k1, zg] at m1
  rw [k2, zg] at c7
  have hlt : msg.gas < bound := by
    rw [m1]
    omega
  refine ⟨cl, msg, hlt, by rw [m1]; omega, by rw [c11, zs, zm], by rw [c12, zss],
    ⟨by rw [m2, zm], m3, m4, m5, m6, by rw [m7, zmem], m8, by rw [m9, zm], by rw [m10, zm]⟩,
    ?_⟩
  intro lt child hch
  obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    resumeCall_eq (fork := fork) (caller := cl) (child := child.1) (o := o) (osz := osz)
      (by rw [c5]; exact hrest)
  refine ⟨after, by rw [a7, c7]; omega,
    fun within => ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) lt hch hres⟩,
    fun c0 m0 hs0 => by
      rcases Trace.Sent.of_step_child (by rw [hstep]; exact hsent) hs0 with
        h | ⟨lt', ch', af', hr', hres', hs'⟩
      · exact .inl h
      · have e1 : ch' = child := Except.ok.inj (hr'.symm.trans hch)
        subst e1
        have e2 : af' = after := Except.ok.inj (hres'.symm.trans hres)
        subst e2
        exact .inr hs',
    a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
    by rw [a4, c4, zp], by rw [a5, c5], by rw [a6, c6, zmem], rfl, a8.trans (c8.trans zrun),
    a9.trans (c9.trans zerr), a10.trans (c10.trans zout), a11, a12, a13⟩

theorem seg1_s (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize : 4 ≤ message.data.size) (hsize2 : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x17ffc320) (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) ≠
        0)
    {c : ByteArray}
    (hcode : state.getCode (state.getAccount (tokA message.data)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas : Nat} (hg : 8000 ≤ gas) (hg64 : gas < 2 ^ 64)
    (runChild : MessageRunner fork Nat bound) (hb : gas ≤ bound)
    {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas state substate evm) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (gas - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt state message.currentTarget (tokA message.data) ∧
      caller.substate = callSs substate message.currentTarget (tokA message.data) ∧
      Sent msg message.currentTarget (tokA message.data) c
        (memoryReadBytes (mem1 message.currentTarget) 128 36) (message.depth + 1)
        message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (gas - 8000) / 64 ≤ after.gas ∧ Goes runChild evm after ∧
          (∀ c0 m0, Trace.Sent runChild evm c0 m0 →
            (c0 = caller ∧ m0 = msg) ∨ Trace.Sent runChild after c0 m0) ∧
          Logic.At CODE message 1537
            ((if child.1.error.isNone then 1 else 0) ::
              [(164 : U256), (1889567281 : U256), bitwiseAnd (tokW message.data) MASK,
                (0 : U256), tokW message.data, (570 : U256),
                BitVec.ofNat 256 (selector message.data)])
            (memoryWrite (mem1 message.currentTarget) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have hkb : slotCost (coldIn substate message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨z1, hr1, hz1⟩ := (Paths.reclaimToken_p2 (fork := fork) (message := message)
    (state := state) (substate := substate) hfork hsize hsize2 hsel (by rw [hval]; decide) hown
    (gas := gas) (by omega)).toHoare evm start
  generalize slotCost (coldIn substate message.currentTarget (5 : U256)) = k5 at hkb hz1
  obtain ⟨hms, hmfp, -⟩ := Paths.reclaimToken_p2_mem (message := message)
  have hcode1 : (readSlot state message.currentTarget (5 : U256)).getCode
      ((readSlot state message.currentTarget (5 : U256)).getAccount
        (tokA message.data)).codeHash = .ok c := hcode
  obtain ⟨z2, k2, hk2, hr2, hz2⟩ := ext_step hfork hglam (by code_fact) (by code_fact) hcode1
    (by omega) hz1
  obtain ⟨z3, hr3, hz3⟩ := (Paths.reclaimCodeA_p1 (fork := fork) (message := message) hfork hms
    hmfp hcs (gas := gas - (567 + k5) - k2) (by omega)).toHoare z2 hz2
  obtain ⟨z4, hr4, hz4⟩ := UsdtVerify.At.gas_rule (fork := fork) (by code_fact) (by code_fact)
    (show 2 ≤ gas - (567 + k5) - k2 - 25 by omega) (by simp [STACK_LIMIT]) z3 hz3
  have hcode4 : ((readSlot state message.currentTarget (5 : U256)).recordAccountRead
      (tokA message.data)).getCode
      (((readSlot state message.currentTarget (5 : U256)).recordAccountRead
        (tokA message.data)).getAccount (tokA message.data)).codeHash = .ok c := hcode
  obtain ⟨caller, msg, hlt, hlo, hcst, hcss, hsent, hall⟩ := call_run_s hfork hglam hz4
    (step_at_call hz4 (by code_fact) (by code_fact))
    (extendMemory_in2 (by rw [hms]; decide) (by rw [hms]; decide)) hcode4 hdel hdepth
    (by simp [STACK_LIMIT]) (by omega) (Nat.le_of_eq (toNat_ofNat_of_lt64 (by omega)).symm)
    runChild (by omega)
  refine ⟨caller, msg, hlt, by omega, hcst, hcss, hsent, ?_⟩
  intro lt child hch
  obtain ⟨after, hga, hgo, hsn, hat⟩ := hall lt child hch
  exact ⟨after, by omega,
    (Goes.of_reaches runChild (hr1.trans (hr2.trans (hr3.trans hr4)))).trans hgo,
    fun c0 m0 h0 =>
      hsn c0 m0 (Trace.Sent.of_reaches (hr1.trans (hr2.trans (hr3.trans hr4))) h0), hat⟩

theorem seg2_s (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {x1 x2 x3 t sel bal : U256} {mem : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hms : mem.size = 192)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = bal)
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) ≠ 0)
    {c : ByteArray}
    (hcode : st.getCode (st.getAccount (tokB t)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hg : 8000 ≤ g) (hg64 : g < 2 ^ 64)
    (runChild : MessageRunner fork Nat bound) (hb : g ≤ bound)
    {a : Evm fork Nat}
    (ha : Logic.At CODE message 1537
      (1 :: x1 :: x2 :: x3 :: [(0 : U256), t, (570 : U256), sel]) mem g st ss rd a) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (g - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt st message.currentTarget (tokB t) ∧
      caller.substate = callSs ss message.currentTarget (tokB t) ∧
      Sent msg message.currentTarget (tokB t) c
        (memoryReadBytes (mem2 mem (ownW st message.currentTarget) bal) 128 68)
        (message.depth + 1) message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (g - 8000) / 64 ≤ after.gas ∧ Goes runChild a after ∧
          (∀ c0 m0, Trace.Sent runChild a c0 m0 →
            (c0 = caller ∧ m0 = msg) ∨ Trace.Sent runChild after c0 m0) ∧
          Logic.At CODE message 3212
            ((if child.1.error.isNone then 1 else 0) ::
              [(196 : U256), (2835717307 : U256), bitwiseAnd MASK (bitwiseAnd MASK t), bal,
                ownW st message.currentTarget, bitwiseAnd MASK t, (1617 : U256), bal, t,
                (570 : U256), sel])
            (memoryWrite (mem2 mem (ownW st message.currentTarget) bal) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  have hkb : slotCost (coldIn ss message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨z1, hr1, hz1⟩ := after1_ok (fork := fork) hbyz (by omega) (by simp) (by omega) a ha
  have hz1b : UsdtVerify.At CODE message 1562
      [BitVec.ofNat 256 rd.size, (128 : U256), (0 : U256), t, (570 : U256), sel] mem (g - 39)
      st ss z1 := by
    have h := At.ofLogic hz1
    rw [hmfp] at h
    exact h
  obtain ⟨z2, hr2, hz2⟩ := (Paths.reclaimMid_p1 (fork := fork) (message := message)
    (state := st) (substate := ss) hfork hms hmfp hw hn (gas := g - 39) (by omega)).toHoare z1
    hz1b
  generalize slotCost (coldIn ss message.currentTarget (5 : U256)) = k5 at hkb hz2
  obtain ⟨hms2, hmfp2, -⟩ := Paths.reclaimMid_p1_mem (message := message) (state := st)
    (n := 0) (t := 0) (sel := 0) (bal := bal) hms hmfp hw
  have hcode1 : (readSlot st message.currentTarget (5 : U256)).getCode
      ((readSlot st message.currentTarget (5 : U256)).getAccount (tokB t)).codeHash = .ok c :=
    hcode
  obtain ⟨z3, k2, hk2, hr3, hz3⟩ := ext_step hfork hglam (by code_fact) (by code_fact) hcode1
    (by omega) hz2
  obtain ⟨z4, hr4, hz4⟩ := (Paths.reclaimCodeB_p1 (fork := fork) (message := message) hfork hms2
    hmfp2 hcs (gas := g - 39 - (514 + k5) - k2) (by omega)).toHoare z3 hz3
  obtain ⟨z5, hr5, hz5⟩ := UsdtVerify.At.gas_rule (fork := fork) (by code_fact) (by code_fact)
    (show 2 ≤ g - 39 - (514 + k5) - k2 - 25 by omega) (by simp [STACK_LIMIT]) z4 hz4
  have hcode5 : ((readSlot st message.currentTarget (5 : U256)).recordAccountRead
      (tokB t)).getCode
      (((readSlot st message.currentTarget (5 : U256)).recordAccountRead
        (tokB t)).getAccount (tokB t)).codeHash = .ok c := hcode
  obtain ⟨caller, msg, hlt, hlo, hcst, hcss, hsent, hall⟩ := call_run_s hfork hglam hz5
    (step_at_call hz5 (by code_fact) (by code_fact))
    (extendMemory_in2 (by rw [hms2]; decide) (by rw [hms2]; decide)) hcode5 hdel hdepth
    (by simp [STACK_LIMIT]) (by omega) (Nat.le_of_eq (toNat_ofNat_of_lt64 (by omega)).symm)
    runChild (by omega)
  refine ⟨caller, msg, hlt, by omega, hcst, hcss, hsent, ?_⟩
  intro lt child hch
  obtain ⟨after, hga, hgo, hsn, hat⟩ := hall lt child hch
  exact ⟨after, by omega,
    (Goes.of_reaches runChild
      (hr1.trans (hr2.trans (hr3.trans (hr4.trans hr5))))).trans hgo,
    fun c0 m0 h0 =>
      hsn c0 m0
        (Trace.Sent.of_reaches (hr1.trans (hr2.trans (hr3.trans (hr4.trans hr5)))) h0), hat⟩

theorem first_call_s (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {S : State.TransactionState} {ss : Substate} {tok : U256}
    (hdata : message.data = data1 SEL_RECLAIM tok) (hm : bitwiseAnd tok MASK = tok)
    (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt S message.currentTarget (5 : U256)) (256 : U256))) ≠ 0)
    {c : ByteArray}
    (hcode : S.getCode (S.getAccount (toAddressMasked tok)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hnp : Precompiles.isPrecompile fork (toAddressMasked tok).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas : Nat} (hg : 8000 ≤ gas) (hg64 : gas < 2 ^ 64) (hb : gas ≤ bound)
    {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas S ss evm) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (gas - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt S message.currentTarget (toAddressMasked tok) ∧
      caller.substate = callSs ss message.currentTarget (toAddressMasked tok) ∧
      msg.code = c ∧ msg.target = some (toAddressMasked tok) ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked tok ∧
      precompileAddress fork msg = none ∧ msg.value = 0 ∧
      msg.data = memoryReadBytes (mem1 message.currentTarget) 128 36 ∧
      msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        processRunner fork bound caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (gas - 8000) / 64 ≤ after.gas ∧ after.gas ≤ bound ∧
          Goes (processRunner fork bound) evm after ∧
          (∀ c0 m0, Trace.Sent (processRunner fork bound) evm c0 m0 →
            (c0 = caller ∧ m0 = msg) ∨ Trace.Sent (processRunner fork bound) after c0 m0) ∧
          Logic.At CODE message 1537
            ((if child.1.error.isNone then 1 else 0) ::
              [(164 : U256), (1889567281 : U256), bitwiseAnd tok MASK,
                (0 : U256), tok, (570 : U256), BitVec.ofNat 256 (selector message.data)])
            (memoryWrite (mem1 message.currentTarget) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas child.1.state (incorporateChild fork caller child.1).substate
            child.1.output after := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hsz := rc_size hdata
  have hW := rc_tokW hdata hm
  have hA := rc_tokA hdata hm
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, hsent, hk⟩ :=
    seg1_s hberlin hglam (by omega) (by rw [hsz]; decide) (rc_sel hdata) hval hown
      (by rw [hA]; exact hcode) hcs hdel hdepth hg hg64 (processRunner fork bound) hb start
  obtain ⟨s_caller, s_ct, s_target, s_ca, s_code, s_data, s_val, s_depth, s_static⟩ := hsent
  refine ⟨caller, msg, hlt, hmg, by rw [hcst, hA], by rw [hcss, hA], s_code,
    by rw [s_target, hA], s_caller, by rw [s_ct, hA],
    noPre_of s_ca (by rw [hA]; exact hnp), s_val, s_data, s_depth, s_static, ?_⟩
  intro lt child hrun
  obtain ⟨a, hga, hgo, hsn, hat⟩ := hk lt child hrun
  have hw : GasMeter.gasHeld evm.gas ≤ bound := by
    rw [start.2.2.2.2.2.2.1]
    exact hb
  obtain ⟨w, -⟩ := hgo hw
  rw [inc_state, hW] at hat
  exact ⟨a, hga, w, hgo, hsn, hat⟩

theorem second_call_s (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {x1 x2 x3 tok sel bal : U256} {mem : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hm2 : bitwiseAnd MASK tok = tok)
    (hms : mem.size = 192)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = bal)
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) ≠ 0)
    {c : ByteArray}
    (hcode : st.getCode (st.getAccount (toAddressMasked tok)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hnp : Precompiles.isPrecompile fork (toAddressMasked tok).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hg : 8000 ≤ g) (hg64 : g < 2 ^ 64) (hb : g ≤ bound)
    {a : Evm fork Nat}
    (ha : Logic.At CODE message 1537
      (1 :: x1 :: x2 :: x3 :: [(0 : U256), tok, (570 : U256), sel]) mem g st ss rd a) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (g - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt st message.currentTarget (toAddressMasked tok) ∧
      caller.substate = callSs ss message.currentTarget (toAddressMasked tok) ∧
      msg.code = c ∧ msg.target = some (toAddressMasked tok) ∧
      msg.caller = message.currentTarget ∧ msg.currentTarget = toAddressMasked tok ∧
      precompileAddress fork msg = none ∧ msg.value = 0 ∧
      msg.data = memoryReadBytes (mem2 mem (ownW st message.currentTarget) bal) 128 68 ∧
      msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        processRunner fork bound caller msg lt = .ok child →
        ∃ (after : Evm fork Nat) (y1 y2 y3 t2 : U256), (g - 8000) / 64 ≤ after.gas ∧
          Goes (processRunner fork bound) a after ∧
          (∀ c0 m0, Trace.Sent (processRunner fork bound) a c0 m0 →
            (c0 = caller ∧ m0 = msg) ∨ Trace.Sent (processRunner fork bound) after c0 m0) ∧
          Logic.At CODE message 3212
            ((if child.1.error.isNone then 1 else 0) :: y1 :: y2 :: y3 ::
              [bal, ownW st message.currentTarget, t2, (1617 : U256), bal, tok, (570 : U256),
                sel])
            (memoryWrite (mem2 mem (ownW st message.currentTarget) bal) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas child.1.state (incorporateChild fork caller child.1).substate
            child.1.output after := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hB := rc_tokB hm2
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, hsent, hk⟩ :=
    seg2_s hberlin hglam hms hmfp hw hn (by rw [hB]; exact hcode) hcs hdel hdepth hg hg64
      (processRunner fork bound) hb ha
  obtain ⟨s_caller, s_ct, s_target, s_ca, s_code, s_data, s_val, s_depth, s_static⟩ := hsent
  refine ⟨caller, msg, hlt, hmg, by rw [hcst, hB], by rw [hcss, hB], s_code,
    by rw [s_target, hB], s_caller, by rw [s_ct, hB],
    noPre_of s_ca (by rw [hB]; exact hnp), s_val, s_data, s_depth, s_static, ?_⟩
  intro lt child hrun
  obtain ⟨a2, hga, hgo, hsn, hat⟩ := hk lt child hrun
  rw [inc_state] at hat
  exact ⟨a2, _, _, _, _, hga, hgo, hsn, hat⟩

end WbtcVerify.Sanity

import WbtcVerify.Wbtc.Sanity.ReclaimSeg
import WbtcVerify.Wbtc.Sanity.Addr

/-!
# reclaimToken under EthLib's real runner: the two calls and the message layer

Written by hand (not generated). `Sanity/Reclaim.lean` and `Sanity/ReclaimSelf.lean` use these
for concrete callees.

Proved:
- `message_of_goes`: from Paris, when the loop of the interpreter (with the real runner
  `processRunner`) goes from the start frame of a message with no value and no precompile to a
  stopped frame, `processMessage` gives that frame, rolled back on an error.
- `RunsOk`, `RunsRevert`: what the witnesses say about `processMessage`. `ok_of_goes`,
  `revert_of_goes`: how to get them.
- `first_call`: reclaimToken(token) sent by the owner, with any code `c` at the token: the message
  that the first CALL sends through the real runner (code, target, data = the 36 bytes of
  balanceOf(this), no value, no precompile), and the frame after any child.
- `second_call`: the same for the second CALL (data = the 68 bytes of transfer(owner, balance)).
- facts on the memory at the two calls, on the logs and on the accessed addresses after a child
  with no error.

Assumed: only the hypotheses written in each statement (fork from Paris and before Glamsterdam,
the fields of the message, enough gas, gas under 2^64, the token no precompile). Not covered:
messages with value, creation.
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

/-! ## The frame after a child -/

theorem inc_state (caller child : Evm fork Nat) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

theorem inc_logs {caller child : Evm fork Nat} (h : child.error = none) :
    (incorporateChild fork caller child).substate.logs =
      caller.substate.logs ++ child.substate.logs := by
  simp [incorporateChild, h]

theorem inc_accessed {caller child : Evm fork Nat} (h : child.error = none) :
    (incorporateChild fork caller child).substate.accessedAddresses =
      child.substate.accessedAddresses := by
  simp [incorporateChild, h]

/-- After a child with no error that started from the child substate of a frame that waits for
a CALL: the logs are those before the call. -/
theorem logs_after {caller child : Evm fork Nat} {ss0 : Substate} {C A : Address}
    (herr : child.error = none) (hss : child.substate = caller.substate.child)
    (hc : caller.substate = callSs ss0 C A) :
    (incorporateChild fork caller child).substate.logs = ss0.logs := by
  rw [inc_logs herr, hss, hc]
  simp [Substate.child, Substate.empty]

/-- After such a child the address that was called is among the accessed addresses. -/
theorem accessed_after {caller child : Evm fork Nat} {ss0 : Substate} {C A : Address}
    (herr : child.error = none) (hss : child.substate = caller.substate.child)
    (hc : caller.substate = callSs ss0 C A) :
    A ∈ (incorporateChild fork caller child).substate.accessedAddresses := by
  rw [inc_accessed herr, hss, hc]
  simp [Substate.child]

/-- The reads that a frame records up to a CALL keep every storage word. -/
theorem storageAt_callSt (S : State.TransactionState) (C A A2 : Address) (n : U256) :
    storageAt (callSt S C A) A2 n = storageAt S A2 n :=
  storageAt_readSlot S C A2 5 n

/-! ## The memory at the two calls -/

theorem mem1_size (C : Address) : (mem1 C).size = 192 :=
  size_rawW (sz := 160) (n := 32) (size_memW5 _ _ _ _ _) (by decide)

theorem mem1_fp (C : Address) : loadWord (memoryReadBytes (mem1 C) 64 32) 0 32 = (128 : U256) :=
  load64_rawW (memW_load64 _ _ _ _) (size_memW5 _ _ _ _ _) (by decide) (by decide) (by decide)

theorem mem2_facts {mem : ByteArray} (own bal : U256) (hms : mem.size = 192)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256)) :
    (mem2 mem own bal).size = 224 ∧
      loadWord (memoryReadBytes (mem2 mem own bal) 64 32) 0 32 = (128 : U256) :=
  ⟨size_rawW (size_rawW (size_rawW hms (by decide)) (by decide)) (by decide),
    load64_rawW (load64_rawW (load64_rawW hfp hms (by decide) (by decide) (by decide))
      (size_rawW hms (by decide)) (by decide) (by decide) (by decide))
      (size_rawW (size_rawW hms (by decide)) (by decide)) (by decide) (by decide) (by decide)⟩

/-- A memory with the free memory pointer 128, after a word is written at 128: its size, the
pointer, the word. -/
theorem mem_after {m : ByteArray} {N : Nat} (v : U256) (hs : m.size = N) (hN : 160 ≤ N)
    (hfp : loadWord (memoryReadBytes m 64 32) 0 32 = (128 : U256)) :
    (memoryWrite m 128 (wordBytes v)).size = N ∧
      loadWord (memoryReadBytes (memoryWrite m 128 (wordBytes v)) 64 32) 0 32 = (128 : U256) ∧
      loadWord (memoryReadBytes (memoryWrite m 128 (wordBytes v)) 128 32) 0 32 = v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [size_memoryWrite (by rw [size_wordBytes]; omega), hs]
  · rw [memoryReadBytes_memoryWrite_of_disjoint (by rw [size_wordBytes]; omega)
      (.inl (by omega))]
    exact hfp
  · exact loadWord_memoryWrite_wordBytes v (by omega)

/-- The first 32 bytes of an output of one word are that word. -/
theorem extract_word (v : U256) :
    (wordBytes v).extract 0 (min 32 (wordBytes v).size) = wordBytes v := by
  have e : (wordBytes v).extract 0 (wordBytes v).size = wordBytes v := by
    first
      | exact ByteArray.extract_zero_size
      | exact ByteArray.extract_zero_size _
  rw [size_wordBytes] at e
  rw [size_wordBytes, Nat.min_self]
  exact e

/-! ## The message layer -/

/-- From Paris: when the loop of the interpreter with the real runner goes from the start frame
of a message with no value and no precompile to a stopped frame `s`, `processMessage` gives `s`,
rolled back on an error. -/
theorem message_of_goes (hparis : .paris ≤ fork) {msg : Message fork}
    {S : State.TransactionState} {ss : Substate}
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) {s : Evm fork Nat}
    (hgo : Goes (processRunner fork msg.gas)
      (startFrame msg S ss (GasMeter.start msg.gas msg.reservoir)) s)
    (hs : s.running = false) :
    ∃ r, processMessage (Meter := Nat) fork msg S ss = .ok r ∧ r.1 = rollbackOnError S s := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hrf := hgo.result hs (start_within msg S ss)
  have hst := startState_of_paris hparis msg S
  rw [← hst] at hrf
  have hmap := processMessage_map_val ht noPre hrf
  cases hpm : processMessage (Meter := Nat) fork msg S ss with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok r =>
    rw [hpm] at hmap
    simp only [Except.map, Except.ok.injEq] at hmap
    exact ⟨r, rfl, hmap⟩

/-- A successful run of a message by `processMessage`: no error, no output, the state `st2`
(which reads as the state before in every storage word), the logs as before, and `tok` among the
accessed addresses. -/
def RunsOk (fork : Fork) (msg : Message fork) (S : State.TransactionState) (ss : Substate)
    (st2 : State.TransactionState) (tok : Address) : Prop :=
  ∃ r, processMessage (Meter := Nat) fork msg S ss = .ok r ∧ r.1.error = none ∧
    r.1.output = ByteArray.empty ∧ r.1.state = st2 ∧
    (∀ (A : Address) (n : U256), storageAt r.1.state A n = storageAt S A n) ∧
    r.1.substate.logs = ss.logs ∧ tok ∈ r.1.substate.accessedAddresses

/-- A run of a message by `processMessage` that reverts with the output `out`, the state put
back: every storage word reads as before the message. -/
def RunsRevert (fork : Fork) (msg : Message fork) (S : State.TransactionState) (ss : Substate)
    (out : ByteArray) : Prop :=
  ∃ r, processMessage (Meter := Nat) fork msg S ss = .ok r ∧ r.1.error = some .revert ∧
    r.1.output = out ∧ ∀ (A : Address) (n : U256), storageAt r.1.state A n = storageAt S A n

/-- A frame that reverts, at the message layer. -/
theorem revert_of_goes (hparis : .paris ≤ fork) {msg : Message fork}
    {S : State.TransactionState} {ss : Substate}
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) {s : Evm fork Nat}
    (hgo : Goes (processRunner fork msg.gas)
      (startFrame msg S ss (GasMeter.start msg.gas msg.reservoir)) s)
    (hs : s.running = false) (herr : s.error = some .revert)
    (hp : s.state.parent = S.parent) : RunsRevert fork msg S ss s.output := by
  obtain ⟨r, hpm, hr1⟩ := message_of_goes hparis noPre hv hgo hs
  refine ⟨r, hpm, ?_, ?_, ?_⟩
  · rw [hr1, error_rollbackOnError]
    exact herr
  · rw [hr1, output_rollbackOnError]
  · intro A n
    rw [hr1, state_rollbackOnError_of_error herr]
    exact getStorage_restoreTxState hp A _

/-- A frame that stops with no error, at the message layer. -/
theorem ok_of_goes (hparis : .paris ≤ fork) {msg : Message fork}
    {S : State.TransactionState} {ss : Substate}
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) {s : Evm fork Nat}
    (hgo : Goes (processRunner fork msg.gas)
      (startFrame msg S ss (GasMeter.start msg.gas msg.reservoir)) s)
    (hs : s.running = false) (herr : s.error = none) (hout : s.output = ByteArray.empty)
    {st2 : State.TransactionState} (hst : s.state = st2)
    (hsto : ∀ (A : Address) (n : U256), storageAt st2 A n = storageAt S A n)
    (hlogs : s.substate.logs = ss.logs) {tok : Address}
    (hacc : tok ∈ s.substate.accessedAddresses) : RunsOk fork msg S ss st2 tok := by
  obtain ⟨r, hpm, hr1⟩ := message_of_goes hparis noPre hv hgo hs
  rw [rollbackOnError_of_error_eq_none herr] at hr1
  refine ⟨r, hpm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr1]; exact herr
  · rw [hr1]; exact hout
  · rw [hr1]; exact hst
  · intro A n
    rw [hr1, hst]
    exact hsto A n
  · rw [hr1]; exact hlogs
  · rw [hr1]; exact hacc

/-! ## The call data of reclaimToken -/

/-- The selector of reclaimToken(address). -/
def SEL_RECLAIM : ByteArray := ⟨#[0x17, 0xff, 0xc3, 0x20]⟩

theorem size_SEL_RECLAIM : SEL_RECLAIM.size = 4 := by decide

theorem rc_size {data : ByteArray} {tok : U256} (hdata : data = data1 SEL_RECLAIM tok) :
    data.size = 36 := by
  rw [hdata]
  exact size_data1 size_SEL_RECLAIM tok

theorem rc_sel {data : ByteArray} {tok : U256} (hdata : data = data1 SEL_RECLAIM tok) :
    selector data = 0x17ffc320 := by
  rw [hdata, selector_data1 size_SEL_RECLAIM]
  decide

theorem rc_tokW {data : ByteArray} {tok : U256} (hdata : data = data1 SEL_RECLAIM tok)
    (hm : bitwiseAnd tok MASK = tok) : tokW data = tok := by
  show bitwiseAnd (loadWord data 4 32) MASK = tok
  rw [hdata, Witness.arg1_data1 size_SEL_RECLAIM, hm]

theorem rc_tokA {data : ByteArray} {tok : U256} (hdata : data = data1 SEL_RECLAIM tok)
    (hm : bitwiseAnd tok MASK = tok) : tokA data = toAddressMasked tok := by
  show toAddressMasked (bitwiseAnd (tokW data) MASK) = _
  rw [rc_tokW hdata hm, hm]

theorem rc_tokB {tok : U256} (hm2 : bitwiseAnd MASK tok = tok) :
    tokB tok = toAddressMasked tok := by
  show toAddressMasked (bitwiseAnd MASK (bitwiseAnd MASK tok)) = _
  rw [hm2, hm2]

/-! ## The two calls under the real runner -/

/-- reclaimToken(tok) sent by the owner, with the code `c` (not empty) at the token: the first
CALL sends, through the real runner, a message with the code `c` to the token, with the 36 bytes
of balanceOf(this) as data and no value; and after any child that the runner gives, the frame is
at 1537 with the flag of the child, its output written at 128 and kept as return data, and the
state of the child. -/
theorem first_call (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
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
    seg1 hberlin hglam (by omega) (by rw [hsz]; decide) (rc_sel hdata) hval hown
      (by rw [hA]; exact hcode) hcs hdel hdepth hg hg64 (processRunner fork bound) hb start
  obtain ⟨s_caller, s_ct, s_target, s_ca, s_code, s_data, s_val, s_depth, s_static⟩ := hsent
  refine ⟨caller, msg, hlt, hmg, by rw [hcst, hA], by rw [hcss, hA], s_code,
    by rw [s_target, hA], s_caller, by rw [s_ct, hA],
    noPre_of s_ca (by rw [hA]; exact hnp), s_val, s_data, s_depth, s_static, ?_⟩
  intro lt child hrun
  obtain ⟨a, hga, hgo, hat⟩ := hk lt child hrun
  have hw : GasMeter.gasHeld evm.gas ≤ bound := by
    rw [start.2.2.2.2.2.2.1]
    exact hb
  obtain ⟨w, -⟩ := hgo hw
  rw [inc_state, hW] at hat
  exact ⟨a, hga, w, hgo, hat⟩

/-- The second CALL of reclaimToken, from the frame at 1537 after a first call with no error
that returned at least 32 bytes: the message that it sends through the real runner (the code `c`
of the token, the 68 bytes of transfer(owner, balance) as data, no value), and after any child
the frame at 3212. -/
theorem second_call (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
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
    seg2 hberlin hglam hms hmfp hw hn (by rw [hB]; exact hcode) hcs hdel hdepth hg hg64
      (processRunner fork bound) hb ha
  obtain ⟨s_caller, s_ct, s_target, s_ca, s_code, s_data, s_val, s_depth, s_static⟩ := hsent
  refine ⟨caller, msg, hlt, hmg, by rw [hcst, hB], by rw [hcss, hB], s_code,
    by rw [s_target, hB], s_caller, by rw [s_ct, hB],
    noPre_of s_ca (by rw [hB]; exact hnp), s_val, s_data, s_depth, s_static, ?_⟩
  intro lt child hrun
  obtain ⟨a2, hga, hgo, hat⟩ := hk lt child hrun
  rw [inc_state] at hat
  exact ⟨a2, _, _, _, _, hga, hgo, hat⟩

end WbtcVerify.Sanity

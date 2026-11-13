import LinkVerify.Link.Seq
import TokenKit.Evm.Payee
import TokenKit.Evm.WitnessOpt

/-!
# Tools for the witnesses of transferAndCall

Written by hand (not generated). Nothing here is a witness; `Sanity/Tac.lean` uses these.

- `mcg_keep`: the 63/64 rule of a CALL with no value and no growth of memory, as two bounds: the
  message gets at most the gas left after the price, and the frame keeps one 64th of it.
- `stop_message_runs`, `invalid_message_runs`: EthLib's real runner `processRunner` does run a
  message with no value whose code is the one byte STOP (no error, the state of the caller) or
  the one byte INVALID 0xfe (an error).
- `tac_call_run`: from pc 0 of `transferAndCall`, for a recipient with code, the loop of the
  interpreter goes to the CALL, sends exactly one message, and for every frame that the runner
  gives for it the loop goes on from pc 3089 with the flag of that frame on the stack. For every
  runner and every bound from the gas of the frame.
- `codeState`: a state like `sState` where one more account holds a given code, under the keccak
  hash of that code.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace LinkVerify.Sanity

open UsdtVerify
open TokenKit
open LinkVerify LinkVerify.Tac LinkVerify.Paths

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The gas of the CALL -/

/-- The 63/64 rule for a CALL with no value and no growth of memory, when the gas left covers the
price `E`: the message gets at most the gas left after the price, and what the frame pays leaves
it at least one 64th of that. -/
theorem mcg_keep (htw : Fork.tangerineWhistle ≤ fork) {asked gas E : Nat} (h : E ≤ gas) :
    (messageCallGas fork 0 asked gas 0 E).subCall ≤ gas - E ∧
      (messageCallGas fork 0 asked gas 0 E).cost + (gas - E) / 64 ≤ gas := by
  have hc : fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas := ⟨htw, h⟩
  have hs : (messageCallGas fork 0 asked gas 0 E).subCall =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) +
      (if (0 : U256) = 0 then 0 else CALL_STIPEND) := rfl
  have hk : (messageCallGas fork 0 asked gas 0 E).cost =
      (if fork ≥ Fork.tangerineWhistle ∧ E + 0 ≤ gas then
        min asked (maxMessageCallGas (gas - 0 - E)) else asked) + E := rfl
  have hx : maxMessageCallGas (gas - 0 - E) = gas - 0 - E - (gas - 0 - E) / 64 := rfl
  have hm := Nat.min_le_right asked (maxMessageCallGas (gas - 0 - E))
  rw [hs, hk, if_pos hc, if_pos (rfl : (0 : U256) = 0)]
  omega

/-! ## Two real callees under the real runner -/

/-- The code of one byte, INVALID (0xfe): a contract whose every call fails. -/
def INVALID_CODE : ByteArray := ⟨#[0xfe]⟩

theorem delegatedAddress_invalid : delegatedAddress INVALID_CODE = none := by decide

/-- A message whose code address is no precompile runs no precompile. -/
theorem noPre_of {msg : Message fork} {a : Address} (h : msg.codeAddress = some a)
    (hnp : Precompiles.isPrecompile fork a.toU256.toNat = false) :
    precompileAddress fork msg = none := by
  simp [precompileAddress, h, hnp]

/-- A frame that the message layer rolls back keeps its error. -/
theorem error_rollbackOnError (snapshot : State.TransactionState) (evm : Evm fork Nat) :
    (rollbackOnError snapshot evm).error = evm.error := by
  unfold rollbackOnError
  split <;> rfl

/-- From Paris, `processRunner` does run a message with no value whose code is the one byte STOP,
to a target that is no precompile: it gives a frame with no error, in the state of the caller. -/
theorem stop_message_runs (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} (lt : msg.gas < bound)
    (hcode : msg.code = Payee.STOP_CODE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.state = caller.state := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hst : startState fork msg caller.state = caller.state := by
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hparis, ite_false]
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  obtain ⟨stopped, hrf, hq⟩ := Gas.SpecG.runFrame
    (Gas.stopG (fork := fork) (code := Payee.STOP_CODE) (message := msg) (pc := 0) (stack := [])
      (memory := .empty) (by decide) rfl)
    (bound := msg.gas) (runChild := processRunner fork msg.gas)
    (At.startFrame hcode (startState fork msg caller.state) caller.substate.child)
    (Nat.le_refl _)
  have hmap := processMessage_map_val ht noPre hrf
  obtain ⟨-, he, -, -, hs, -⟩ := hq
  have he' : stopped.error = none := by simpa using he
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    have hc : child.1 = stopped := by
      simp only [Except.map, Except.ok.injEq] at hmap
      rw [hmap, rollbackOnError_of_error_eq_none he']
    exact ⟨child, rfl, by rw [hc]; exact he', by rw [hc, hs, hst]⟩

/-- From Paris, `processRunner` does run a message with no value whose code is the one byte
INVALID, to a target that is no precompile: it gives a frame with the error of an invalid
opcode. -/
theorem invalid_message_runs (hparis : .paris ≤ fork) {bound : Nat} {caller : Evm fork Nat}
    {msg : Message fork} {to : Address} (lt : msg.gas < bound)
    (hcode : msg.code = INVALID_CODE) (htarget : msg.target = some to)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = some (.invalidOpcode 0xfe) := by
  have ht : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hv
  have hp : processRunner fork bound caller msg lt =
      processMessage fork msg caller.state caller.substate.child := by
    simp only [processRunner, htarget]
  obtain ⟨stopped, hrf, hq⟩ := Gas.SpecG.runFrame
    (Gas.invalid_feG (fork := fork) (code := INVALID_CODE) (message := msg) (pc := 0)
      (stack := []) (memory := .empty) (by decide) rfl)
    (bound := msg.gas) (runChild := processRunner fork msg.gas)
    (At.startFrame hcode (startState fork msg caller.state) caller.substate.child)
    (Nat.le_refl _)
  have hmap := processMessage_map_val ht noPre hrf
  obtain ⟨-, he, -⟩ := hq
  rw [hp]
  cases hpm : processMessage (Meter := Nat) fork msg caller.state caller.substate.child with
  | error e =>
    rw [hpm] at hmap
    simp [Except.map] at hmap
  | ok child =>
    rw [hpm] at hmap
    simp only [Except.map, Except.ok.injEq] at hmap
    exact ⟨child, rfl, by rw [hmap, error_rollbackOnError]; exact he⟩

/-! ## The run to the CALL and over it -/

/-- From pc 0 of `transferAndCall` with `tacCallGas + 13000` gas, for a recipient with code `c`
(no EIP-7702 delegation) and below the depth limit: the loop of the interpreter goes to the CALL
and sends one message `msg` from a frame `caller`. The message has less gas than the bound, goes
to the recipient with the code `c` and no value, and `caller` has the state of the token move
with two more reads recorded. For every frame `child` that the runner gives for it, the loop goes
on from pc 3089 with the flag of `child` on the stack, at least 147 gas, and the state of
`child` taken in. For every runner and every bound from the gas of the frame. -/
theorem tac_call_run (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
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
    (hb : tacCallGas fork message state substate + 13000 ≤ bound)
    {evm : Evm fork Nat}
    (start : At CODE message 0 [] .empty (tacCallGas fork message state substate + 13000) state
      substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      caller.state = ((tacCallSt message state).recordAccountRead
        (toAddressMasked (tacToW message))).recordAccountRead message.currentTarget ∧
      msg.target = some (toAddressMasked (tacToW message)) ∧
      msg.codeAddress = some (toAddressMasked (tacToW message)) ∧
      msg.code = c ∧ msg.value = 0 ∧
      ∀ (lt : msg.gas < bound)
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
            Evm.runFrame (step fork) (step_decreases fork) bound runChild after w := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  have hp1 := (transferAndCall_p1 (fork := fork) (message := message) (state := state)
    (substate := substate) hfork hsize hsize' hsel (by rw [hval]; decide)
    (gas := tacCallGas fork message state substate + 13000) (by omega)).toHoare
  have hcall := tac_at_call (fork := fork) (message := message)
    (sel := BitVec.ofNat 256 (selector message.data)) (state := state) (substate := substate)
    hfork hstatic hacc hN hcode h1 h2 h3 h4 h5
    (gas := tacCallGas fork message state substate + 13000 - 207) (by omega)
  obtain ⟨z, hr, hz⟩ := Triple.seq hp1 hcall evm start
  have hz' : At CODE message 3088
      (tacAsked fork message state substate
          (tacCallGas fork message state substate + 13000 - 207) :: tacToW message :: 0 ::
        tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132) ::
        tacFpw (tacLen message) :: 0 ::
        tacRest message (BitVec.ofNat 256 (selector message.data)))
      (tacMem message)
      (tacCallGas fork message state substate + 13000 - 207 -
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
        (tacCallGas fork message state substate + 13000 - 207) :: tacToW message ::
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
  have hk := mcg_keep (fork := fork) htw
    (asked := (tacAsked fork message state substate
      (tacCallGas fork message state substate + 13000 - 207)).toNat)
    (gas := z.gas) (E := E) (by rw [zg]; omega)
  have hlt : msg.gas < bound := by
    rw [m1]
    omega
  have hclg : 147 ≤ cl.gas := by
    rw [c7]
    omega
  refine ⟨cl, msg, hlt, by rw [s1, zs, zm] <;> rfl, mt.trans (by simp), mca, mc,
    m5.trans (by simp), ?_⟩
  intro lt child hch
  obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    resumeCall_eq (fork := fork) (caller := cl) (child := child.1)
      (o := tacFpw (tacLen message)) (osz := 0)
      (by rw [c5]; simp [tacRest, STACK_LIMIT])
  obtain ⟨w, hrun2⟩ : ∃ w : GasMeter.gasHeld after.gas ≤ bound,
      Evm.runFrame (step fork) (step_decreases fork) bound runChild z
        (Nat.le_trans (hr.gasHeld_le Step.gasHeld_le) within) =
      Evm.runFrame (step fork) (step_decreases fork) bound runChild after w :=
    ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) lt hch hres⟩
  have hme : memoryExtend (tacMem message) (ExtendMemory.expandBy ⟨0, 0⟩) = tacMem message :=
    memoryExtend_zero _
  have hw : memoryWrite (tacMem message) (tacFpw (tacLen message)).toNat
      (child.1.output.extract 0 (min (0 : U256).toNat child.1.output.size)) =
      tacMem message := by
    simp [memoryWrite]
  have hmem : after.memory = tacMem message := by
    rw [a6, c6, hext, zmem, hme]
    exact hw
  refine ⟨after, w, ⟨a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
    by rw [a4, c4, zp], by rw [a5, c5], hmem, rfl, a8.trans (c8.trans zrun),
    a9.trans (c9.trans zerr), a10.trans (c10.trans zout), a11, a12⟩, ?_, hrun1.trans hrun2⟩
  rw [a7]
  omega

/-! ## A state where one more account holds code -/

/-- The keccak hash under which the state keeps a code. -/
abbrev hashOf (code : ByteArray) : EthLib.Base.Hash32 :=
  EthLib.Cryptography.Hash.Keccak.keccak256 code

/-- `sState C kvs` with one more account, at `a`, that holds the code `code` (nonce 1, no ether),
kept under its keccak hash as EthLib's `setCode` keeps it. -/
def codeState (C : Address) (kvs : List (U256 × U256)) (a : Address) (code : ByteArray) :
    State.TransactionState :=
  { (sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩) with
    codeWrites := ((sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code }

/-- The storage of `codeState` is that of `sState`. -/
theorem storageAt_codeState (C : Address) (kvs : List (U256 × U256)) (a : Address)
    (code : ByteArray) (C' : Address) (n : U256) :
    storageAt (codeState C kvs a code) C' n = storageAt (sState C kvs) C' n := rfl

/-- `codeState` has the account of the contract, when the account with code is another one. -/
theorem hasAccount_codeState {C : Address} (kvs : List (U256 × U256)) {a : Address}
    (code : ByteArray) (h : C ≠ a) : hasAccount (codeState C kvs a code) C := by
  have e : (codeState C kvs a code).getAccountOptional C = (sState C kvs).getAccountOptional C :=
    getAccountOptional_setAccount_of_ne (sState C kvs) (some ⟨1, 0, hashOf code⟩) h
  have h0 := hasAccount_sState C kvs
  unfold hasAccount at h0 ⊢
  rw [e]
  exact h0

/-- `codeState` gives the code for its account, when the hash of the code is not the hash of the
empty code. -/
theorem getCode_codeState (C : Address) (kvs : List (U256 × U256)) (a : Address)
    {code : ByteArray} (hH : hashOf code ≠ EMPTY_CODE_HASH) :
    (codeState C kvs a code).getCode ((codeState C kvs a code).getAccount a).codeHash =
      .ok code := by
  have e : (codeState C kvs a code).getAccountOptional a = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self (sState C kvs) a (some ⟨1, 0, hashOf code⟩)
  have hacct : ((codeState C kvs a code).getAccount a).codeHash = hashOf code := by
    unfold State.TransactionState.getAccount
    rw [e] <;> rfl
  have e2 : (codeState C kvs a code).codeWrites[hashOf code]? = some code := by
    show (((sState C kvs).setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[hashOf code]? = some code
    simp
  rw [hacct]
  unfold State.TransactionState.getCode
  rw [if_neg hH, e2]

/-- A record of an account read keeps every storage word. -/
theorem storageAt_rar (S : State.TransactionState) (a C : Address) (n : U256) :
    storageAt (S.recordAccountRead a) C n = storageAt S C n := rfl

end LinkVerify.Sanity

import WbtcVerify.Wbtc.SeqLocal
import WbtcVerify.Wbtc.Reclaim.Good

/-!
# A real callee for `reclaimToken`: the tiny token, under EthLib's real runner

Written by hand (not generated). The results on `reclaimToken` rest on the local assumption
`ReclaimCalleeKeeps runChild message state` (Reclaim/Good.lean). Here it is machine-checked that
the assumption is TRUE for EthLib's real runner `Logic.processRunner fork bound` with a real
callee, so `supply_reclaimToken` is not empty.

The callee is the tiny token `TINY` = 0x600160005260206000f3 (PUSH1 1, PUSH1 0, MSTORE,
PUSH1 32, PUSH1 0, RETURN): it returns one 32-byte word for every call, reads and writes no
storage, sends no message.

What is proved:

- `tiny_spec`: the frame of `TINY` halts normally with the state unchanged, for every gas from
  `tinyCost` on.
- `not_sent_low`, `tiny_not_sent`: a frame of `TINY` sends no message, with ANY gas (also when
  it runs out of gas), under any runner.
- `tiny_process`: a message with no value that runs `TINY`, that `processMessage` ends with no
  error, ends in the state it started from (`startState`: only the touch before Paris).
- `tiny_runner`: the same for a message that a CALL of WBTC sends (`SentVia`) to an address that
  holds `TINY`, under the real runner.
- `reclaimCalleeKeeps_tiny`: `ReclaimCalleeKeeps (Logic.processRunner fork bound) message state`
  when the token of the call holds `TINY`.
- `supply_reclaimToken_tiny`: so a successful `reclaimToken` against the tiny token keeps `Inv`
  under the real runner.
- `cleanRunW_tiny`: the run that the real runner makes of such a message is clean for WBTC at
  any other address `L` (nothing enters `L`, nothing is deposited).

Assumed (all local, each listed at its theorem): Berlin ≤ fork < Glamsterdam and call data below
2^256 bytes (from `supply_reclaimToken`); `TinyAt state tok`: the state holds the code `TINY`
for the token; the token is no precompile address at the fork.
NO hypothesis on keccak (no `SepAll`, no `NoCollision`, no `Sep`), none on the code at the
address of WBTC.
Not covered: that such a run exists and ends with no error (the stream "witness" evaluates
concrete runs); the value of the word that `TINY` returns is not used.
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}

/-! ## The code -/

/-- The tiny token: PUSH1 1, PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, RETURN. -/
def TINY : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3]⟩

theorem size_TINY : TINY.size = 10 := rfl

/-- `TINY` is no EIP-7702 delegation indicator. -/
theorem tiny_not_delegated : delegatedAddress TINY = none := by
  have h : isValidDelegation TINY = false := by
    simp [isValidDelegation, size_TINY, DELEGATION_SIZE]
  simp [delegatedAddress, h]

/-- The word that PUSH1 0 pushes. -/
def tinyW0 : U256 := BitVec.ofNat 256 (0x00 : UInt8).toNat

/-- The word that PUSH1 1 pushes. -/
def tinyW1 : U256 := BitVec.ofNat 256 (0x01 : UInt8).toNat

/-- The word that PUSH1 32 pushes. -/
def tinyW32 : U256 := BitVec.ofNat 256 (0x20 : UInt8).toNat

/-- The gas that MSTORE pays to extend the empty memory. -/
def tinyC1 : Nat := (extendMemory ByteArray.empty.size [(tinyW0, 32)]).cost

/-- The memory after MSTORE. -/
def tinyM1 : ByteArray :=
  memoryWrite (memoryExtend ByteArray.empty
    (extendMemory ByteArray.empty.size [(tinyW0, 32)]).expandBy) tinyW0.toNat (wordBytes tinyW1)

/-- The gas that RETURN pays for its range. -/
def tinyC2 : Nat := (extendMemory tinyM1.size [(tinyW0, tinyW32)]).cost

/-- The output of `TINY`. -/
def tinyOut : ByteArray :=
  memoryReadBytes (memoryExtend tinyM1 (extendMemory tinyM1.size [(tinyW0, tinyW32)]).expandBy)
    tinyW0.toNat tinyW32.toNat

/-- The gas that a run of `TINY` pays. -/
def tinyCost : Nat := 3 + 3 + (3 + tinyC1) + 3 + 3 + tinyC2

/-- The frame of `TINY` halts normally, with the state and the substate unchanged, for every gas
from `tinyCost` on. Every fork. -/
theorem tiny_spec {gas : Nat} (hg : tinyCost ≤ gas) :
    Logic.SpecG fork (At TINY message 0 [] .empty gas state substate)
      (Halted false tinyOut (gas - tinyCost) state substate) := by
  have hg' : 3 + 3 + (3 + tinyC1) + 3 + 3 + tinyC2 ≤ gas := hg
  step Gas.push1G (byte := 0x01) (by decide) (by decide) (by decide) (by omega) (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide) (by omega) (by stk_ok)
  step Gas.mstoreG (by decide) (by decide) (show 3 + tinyC1 ≤ gas - 3 - 3 by omega)
  step Gas.push1G (byte := 0x20) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + tinyC1) by omega) (by stk_ok)
  step Gas.push1G (byte := 0x00) (by decide) (by decide) (by decide)
    (show 3 ≤ gas - 3 - 3 - (3 + tinyC1) - 3 by omega) (by stk_ok)
  exact haltGasL (specL (Gas.returnG (by decide) (by decide)
    (show tinyC2 ≤ gas - 3 - 3 - (3 + tinyC1) - 3 - 3 by omega)))
    (show gas - 3 - 3 - (3 + tinyC1) - 3 - 3 - tinyC2 =
      gas - (3 + 3 + (3 + tinyC1) + 3 + 3 + tinyC2) by omega)

/-! ## A frame that halts with more gas sends no message -/

/-- A frame that sends a message is running. -/
theorem sent_running {bound : Nat} {r : MessageRunner fork Nat bound} {evm c : Evm fork Nat}
    {m : Message fork} (hs : Trace.Sent r evm c m) : evm.running = true := by
  cases hs with
  | here h _ => exact h
  | next h _ _ => exact h
  | resumed h _ _ _ _ => exact h

/-- A chain of steps monotone in gas from `low` with `k` more gas to a stopped frame: `low`
sends no message, under any runner. With less gas the run follows the chain or fails; a failing
step sends nothing. Stronger than `Trace.not_sent_of_specG`, which needs the gas of the
specification. -/
theorem not_sent_low {bound : Nat} (r : MessageRunner fork Nat bound) {hi z : Evm fork Nat}
    (hr : Logic.Reaches (Logic.StepG fork) hi z) :
    ∀ (k : Nat) (low : Evm fork Nat), hi = addGas k low → z.running = false →
      ∀ (c : Evm fork Nat) (m : Message fork), ¬ Trace.Sent r low c m := by
  induction hr with
  | refl =>
    rintro k low rfl hz c m hs
    have hrun : low.running = false := by simpa using hz
    have h := sent_running hs
    rw [hrun] at h
    cases h
  | step hstep _ ih =>
    rintro k low rfl hz c m hs
    obtain ⟨hstep, mono⟩ := hstep
    rcases mono k low rfl with fails | ⟨b, hb, hh⟩
    · rcases fails with ⟨e, he⟩ | ⟨b, hb, hbr, -⟩
      · cases hs with
        | here _ h1 => rw [he] at h1; cases h1
        | next _ h1 _ => rw [he] at h1; cases h1
        | resumed _ h1 _ _ _ => rw [he] at h1; cases h1
      · have h := sent_running (hs.of_step_next hb)
        rw [hbr] at h
        cases h
    · cases hstep with
      | next _ hn =>
        rw [hh] at hn
        cases hn
        exact ih k b rfl hz c m (hs.of_step_next hb)
      | halt _ hn _ =>
        rw [hh] at hn
        cases hn

/-- A frame of `TINY` sends no message, with any gas, under any runner. -/
theorem tiny_not_sent {gas : Nat} {evm : Evm fork Nat}
    (start : At TINY message 0 [] .empty gas state substate evm)
    {bound : Nat} (r : MessageRunner fork Nat bound) (c : Evm fork Nat) (m : Message fork) :
    ¬ Trace.Sent r evm c m := by
  obtain ⟨z, hr, hz, -⟩ := tiny_spec (fork := fork) (message := message) (state := state)
    (substate := substate) (gas := gas + tinyCost) (Nat.le_add_left _ _) (addGas tinyCost evm)
    (At.ofLogic (start.toLogic.addGas tinyCost))
  exact not_sent_low r hr tinyCost evm rfl hz c m

/-! ## The state through the start of a message -/

/-- The start of a message changes no storage word. -/
theorem storage_startState (msg : Message fork) (S : State.TransactionState) (a : Address)
    (k : EthLib.Base.Bytes32) :
    (startState fork msg S).getStorage a k = S.getStorage a k := by
  unfold startState
  split
  · unfold State.TransactionState.touchAccount
    split
    · rfl
    · rfl
  · rfl

/-- The invariant of WBTC at `L` holds after the start of any message. -/
theorem inv_startState {L : Address} (msg : Message fork) {S : State.TransactionState}
    (h : Inv L S) : Inv L (startState fork msg S) :=
  storageOnly_inv L S _ (fun k => storage_startState msg S L k) h

/-- The state holds the code `TINY` for the address `tok`. -/
def TinyAt (S : State.TransactionState) (tok : Address) : Prop :=
  S.getCode (S.getAccount tok).codeHash = .ok TINY

theorem TinyAt.of_readsAs {tx S : State.TransactionState} {tok : Address} (r : ReadsAs tx S)
    (h : TinyAt S tok) : TinyAt tx tok := by
  unfold TinyAt at h ⊢
  rw [Reenter.getAccount_congr (r.1 tok (by simp)).1, r.2]
  exact h

theorem TinyAt.startState {S : State.TransactionState} {tok : Address} (msg : Message fork)
    (h : TinyAt S tok) : TinyAt (startState fork msg S) tok := by
  unfold TinyAt at h ⊢
  unfold EthLib.Execution.Evm.startState
  split
  · rw [State.TransactionState.getCode_touchAccount]
    by_cases hL : tok = msg.currentTarget
    · rw [hL, State.TransactionState.getAccount_touchAccount_self, ← hL]
      exact h
    · rw [State.TransactionState.getAccount_touchAccount hL]
      exact h
  · exact h

/-! ## A message that runs `TINY` -/

/-- A frame that `rollbackOnError` leaves with no error had none. -/
theorem error_none_of_rollback {snapshot : State.TransactionState} {evm : Evm fork Nat}
    (ok : (rollbackOnError snapshot evm).error = none) : evm.error = none := by
  unfold rollbackOnError at ok
  split at ok <;> exact ok

/-- A message with a code address that is no precompile at the fork calls no precompile. -/
theorem precompileAddress_none {m : Message fork} {a : Address} (hca : m.codeAddress = some a)
    (hpre : Precompiles.isPrecompile fork a.toU256.toNat = false) :
    precompileAddress fork m = none := by
  unfold precompileAddress
  rw [hca]
  simp [hpre]

/-- The frame that a message of code `TINY` starts. -/
theorem at_tiny_start {msg : Message fork} (hcode : msg.code = TINY)
    (S : State.TransactionState) (ss : Substate) (meter : Nat) :
    At TINY msg 0 [] .empty meter S ss (startFrame msg S ss meter) :=
  ⟨hcode, by rw [← hcode]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A message with no value that runs `TINY`, that `processMessage` ends with no error, ends in
the state it started from. -/
theorem tiny_process {msg : Message fork} {S : State.TransactionState} {ss : Substate}
    {meter : Nat} {held : GasMeter.gasHeld meter ≤ msg.gas}
    {ended : { evm : Evm fork Nat // GasMeter.gasHeld evm.gas ≤ msg.gas }}
    (hcode : msg.code = TINY) (hval : msg.value = 0)
    (hpre : precompileAddress fork msg = none)
    (h : processMessage fork msg S ss meter held = .ok ended)
    (hok : ended.val.error = none) :
    ended.val.state = startState fork msg S := by
  have nv : ¬(msg.shouldTransferValue = true ∧ msg.value ≠ 0) := fun h => h.2 hval
  have key : ∀ result, runFrame (step fork) (step_decreases fork) msg.gas
      (Logic.processRunner fork (Meter := Nat) msg.gas)
      (startFrame msg (startState fork msg S) ss meter) held = result →
      (processMessage fork msg S ss meter held).map Subtype.val =
        result.map (rollbackOnError S) :=
    fun _ ran => processMessage_map_val nv hpre ran
  cases hrun : runFrame (step fork) (step_decreases fork) msg.gas
      (Logic.processRunner fork (Meter := Nat) msg.gas)
      (startFrame msg (startState fork msg S) ss meter) held with
  | error e =>
    have hm := key _ hrun
    rw [h] at hm
    cases hm
  | ok after =>
    have hm := key _ hrun
    rw [h] at hm
    have hv : ended.val = rollbackOnError S after := Except.ok.inj hm
    have herr : after.error = none := by
      rw [hv] at hok
      exact error_none_of_rollback hok
    rw [hv, rollbackOnError_of_error_eq_none herr]
    exact (ok_exactL (B := tinyCost) (fun g hg => tiny_spec hg)
      (at_tiny_start hcode _ _ _) held hrun herr).2.2.2.2.1

/-- A message that a CALL sends (`SentVia`) to an address that holds `TINY` and is no
precompile, under the real runner: when its run ends with no error, the state at the end is the
state of the caller after the start of the message (the touch before Paris, nothing else). -/
theorem tiny_runner {bound : Nat} {tok : Address} {S : State.TransactionState}
    {caller : Evm fork Nat} {msg : Message fork} {child : Evm fork Nat}
    (hpre : Precompiles.isPrecompile fork tok.toU256.toNat = false)
    (htiny : TinyAt S tok) (hvia : SentVia message S tok caller msg)
    (hran : Ran (Logic.processRunner fork (Meter := Nat) bound) caller msg child)
    (herr : child.error = none) :
    child.state = startState fork msg caller.state := by
  obtain ⟨c, route, hcode, hroute, -, -, -, htar, hca, hmc, -, hval, -⟩ := hvia
  have hc : c = TINY := Except.ok.inj (hcode.symm.trans htiny)
  subst hc
  rcases route with _ | ⟨d, c'⟩
  · obtain ⟨lt, child', hrc, rfl⟩ := hran
    dsimp only [Logic.processRunner] at hrc
    split at hrc
    · exact tiny_process hmc hval (precompileAddress_none hca hpre) hrc herr
    · have htn : msg.target = none := by assumption
      rw [htar] at htn
      cases htn
  · exact absurd (tiny_not_delegated.symm.trans hroute.2.1) (by simp)

/-! ## The local assumption of `reclaimToken` holds for the tiny token -/

/-- THE LOCAL ASSUMPTION IS TRUE for EthLib's real runner and the tiny token: when the state
holds `TINY` for the token of the call, and the token is no precompile address, each of the two
messages of `reclaimToken` keeps the invariant. Every fork, every bound, NO hypothesis on
keccak, none on the code at the address of WBTC. -/
theorem reclaimCalleeKeeps_tiny {bound : Nat}
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message)) :
    ReclaimCalleeKeeps (Logic.processRunner fork (Meter := Nat) bound) message state := by
  intro caller1 msg1 child1 hran1 hvia1 _ herr1 hinv1
  have t0 : TinyAt (rcSt message state (rcToken message)) (rcToken message) :=
    htiny.of_readsAs (readsAs_rcSt _ _ _)
  have e1 := tiny_runner hpre t0 hvia1 hran1 herr1
  have rc1 : ReadsAs caller1.state (rcSt message state (rcToken message)) := by
    obtain ⟨_, _, -, -, hr, -⟩ := hvia1
    exact hr
  have t1 : TinyAt child1.state (rcToken message) := by
    rw [e1]
    exact (t0.of_readsAs rc1).startState msg1
  refine ⟨by rw [e1]; exact inv_startState msg1 hinv1, ?_⟩
  intro caller2 msg2 child2 hran2 hvia2 _ herr2 hinv2
  have e2 := tiny_runner hpre (t1.of_readsAs (readsAs_rcSt _ _ _)) hvia2 hran2 herr2
  rw [e2]
  exact inv_startState msg2 hinv2

/-- `reclaimToken` AGAINST THE TINY TOKEN KEEPS THE INVARIANT UNDER THE REAL RUNNER, with no
hypothesis on keccak: a frame of the code of WBTC, selector `reclaimToken`, run by EthLib's
interpreter loop with `processRunner`, that ends with no error, keeps "sum of balances =
totalSupply_", when the token of the call holds `TINY` and is no precompile address. -/
theorem supply_reclaimToken_tiny (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    (hpre : Precompiles.isPrecompile fork (rcToken message).toU256.toNat = false)
    (htiny : TinyAt state (rcToken message))
    (hinv : Inv message.currentTarget state)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL (Logic.processRunner fork (Meter := Nat) bound) evm s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state :=
  supply_reclaimToken hfork hglam hsize' hsel (reclaimCalleeKeeps_tiny hpre htiny) hinv start
    hrun hok

/-! ## The run of a tiny message is clean -/

/-- The run that the real runner makes of a message sent by a CALL (`SentVia`) to an address
`tok` that holds `TINY` is clean for WBTC at any other address `L`: the message does not enter
`L`, its frame sends no message (with any gas), and no code is deposited. No hypothesis on
keccak, none on precompiles. -/
theorem cleanRunW_tiny {L tok : Address} {S : State.TransactionState} {caller : Evm fork Nat}
    {msg : Message fork} (hne : tok ≠ L) (htiny : TinyAt S tok)
    (hvia : SentVia message S tok caller msg) : CleanRunW L caller msg := by
  obtain ⟨c, route, hcode, hroute, -, -, hcur, htar, -, hmc, -⟩ := hvia
  have hc : c = TINY := Except.ok.inj (hcode.symm.trans htiny)
  subst hc
  rcases route with _ | ⟨d, c'⟩
  · intro e he
    cases he with
    | call _ ho =>
      cases ho with
      | self => exact fun h => absurd (hcur.symm.trans h) hne
      | sub fo hs _ =>
        obtain ⟨-, state1, -, rfl⟩ := fo
        exact absurd hs (tiny_not_sent (at_tiny_start hmc _ _ _) _ _ _)
    | create htn _ =>
      rw [htar] at htn
      cases htn
  · exact absurd (tiny_not_delegated.symm.trans hroute.2.1) (by simp)

end WbtcVerify

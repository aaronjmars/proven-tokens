import WbtcVerify.Wbtc.ReclaimWit.Re
import WbtcVerify.Wbtc.ReclaimWit.SentSeg
import WbtcVerify.Wbtc.AnyLocal

/-!
# reclaimToken against a token that calls back into WBTC: the run

Written by hand (not generated). Fix of audit 4 (the gap of LINK-4, here for WBTC). The witnesses
of `reclaimToken` so far use a token that does nothing (`TINY`) or WBTC itself. Here the token is
another contract, chosen by the owner, whose code `RE` (ReclaimWit/Re.lean) CALLs back into WBTC
each time WBTC calls it: `transfer(0x2000, 1)`, then it returns the word 1.

The run: the owner sends reclaimToken(0x1000) to WBTC; the token at 0x1000 has 2 WBTC.

1. WBTC calls token.balanceOf(WBTC). The token calls back WBTC.transfer(0x2000, 1) (a real
   reentry: a frame of the code of WBTC runs inside the frame of reclaimToken), and returns 1.
2. WBTC calls token.transfer(owner, 1). The token calls back WBTC.transfer(0x2000, 1) again,
   and returns 1 ("true").
3. reclaimToken ends with STOP.

At the end the token has 0 WBTC and the address 0x2000 has 2.

What is proved:

- `re_inner_spec`, `re_inner_runs`: the inner call, as a frame and under EthLib's real runner.
- `re_call_runs`: a call of WBTC to the token under the real runner, with the inner call inside,
  and the run-local condition `Trace.CleanRun` of that call.
- `reclaim_re_core`: the whole run under the real runner, the end balances, and the run-local
  condition `Trace.CleanFrame` of the frame of reclaimToken: the messages that it sends are the
  two calls to the token (from `first_call_s`, `second_call_s`), nothing else.

Assumed: Paris ≤ fork < Glamsterdam; the address `C` has the word of the address of WBTC; the
start state as described (`ReSt`); a gas limit from 32,000,000 and below 2^64. No hypothesis on
keccak here: the slots of the two balances and slot 5 are compared in the kernel.

Not covered: other tokens, other amounts, a token that calls another function of WBTC, runs that
end with an error.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace WbtcVerify.Sanity

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete
  UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}


/-! ## Words and addresses -/

theorem mk2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (0x2000 : U256) = 0x2000 := by decide

theorem mk1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (1 : U256) = 1 := by decide

/-- The word of the address of the word 0x1000. -/
theorem token_toU256 : (toAddressMasked (0x1000 : U256)).toU256 = 0x1000 := by
  apply BitVec.eq_of_toNat_eq
  rw [EthLib.Base.toNat_toU256_toAddressMasked]
  decide

/-- An address with the word of WBTC is not the address of the word 0x1000. -/
theorem token_ne_wbtc {C : Address} (hC : C.toU256 = WBTCW) :
    toAddressMasked (0x1000 : U256) ≠ C := by
  intro h
  have h2 : (toAddressMasked (0x1000 : U256)).toU256 = C.toU256 := congrArg _ h
  rw [token_toU256, hC] at h2
  exact absurd h2 (by decide)

theorem re_size_ne : isZero (isZero (BitVec.ofNat 256 RE.size)) ≠ 0 := by
  rw [size_RE]
  decide

/-! ## The states of the run -/

/-- What the run needs of a state: `C` holds the code of WBTC, the token (the address of the
word 0x1000) holds `RE`, slot 5 says that `Witness.CALLER1` is the owner and the token is not
paused, the token has `X` WBTC and the address 0x2000 has `Y`. -/
structure ReSt (C : Address) (S : State.TransactionState) (X Y : U256) : Prop where
  hold : Reenter.HoldsCode C CODE S
  tok : Reenter.HoldsCode TOKEN RE S
  own : storageAt S C (5 : U256) = OWNER_SLOT
  b1 : storageAt S C (mapSlot (0x1000 : U256) (0 : U256)) = X
  b2 : storageAt S C (mapSlot (0x2000 : U256) (0 : U256)) = Y

/-- The state of the frame of reclaimToken at a CALL reads as the state before. -/
theorem ReSt.callSt {C : Address} {S : State.TransactionState} {X Y : U256} (A : Address)
    (h : ReSt C S X Y) : ReSt C (callSt S C A) X Y :=
  ⟨Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_recordAccountRead _
      (Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_readSlot _ _ h.hold))),
    Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_recordAccountRead _
      (Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_readSlot _ _ h.tok))),
    by rw [storageAt_callSt]; exact h.own, by rw [storageAt_callSt]; exact h.b1,
    by rw [storageAt_callSt]; exact h.b2⟩

/-- The state of the frame of `RE` at its CALL reads as the state before. -/
theorem ReSt.rar2 {C : Address} {S : State.TransactionState} {X Y : U256} (a b : Address)
    (h : ReSt C S X Y) : ReSt C ((S.recordAccountRead a).recordAccountRead b) X Y :=
  ⟨Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_recordAccountRead _ h.hold),
    Reenter.holdsCode_recordAccountRead _ (Reenter.holdsCode_recordAccountRead _ h.tok),
    by rw [storageAt_rar, storageAt_rar]; exact h.own,
    by rw [storageAt_rar, storageAt_rar]; exact h.b1,
    by rw [storageAt_rar, storageAt_rar]; exact h.b2⟩

/-! ## The inner call: transfer(0x2000, 1) sent by the token to WBTC -/

set_option maxHeartbeats 1000000 in
/-- The frame of the inner call. A message `transfer(0x2000, 1)` (the call data `reData` of
`RE`) from the token to the code of WBTC at `C`, in a state where the token has `X` and 0x2000
has `Y` (the two cases of the run: 2 and 0, or 1 and 1): the frame runs with no call to a normal
halt with the word 1; after it the token has `X - 1`, 0x2000 has `Y + 1`, and every other
storage word of `C` is as before. -/
theorem re_inner_spec (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {im : Message fork} {St : State.TransactionState} {ss : Substate} {C : Address} {X Y : U256}
    (hXY : (X = 2 ∧ Y = 0) ∨ (X = 1 ∧ Y = 1))
    (hct : im.currentTarget = C) (hdata : im.data = reData) (hv : im.value = 0)
    (hstatic : im.isStatic = false) (hcw : im.caller.toU256 = (0x1000 : U256))
    (hS : ReSt C St X Y) {gas : Nat} (hg : 60000 ≤ gas) :
    ∃ (cost : Nat) (st' : State.TransactionState) (ss' : Substate),
      Logic.SpecG fork (At CODE im 0 [] .empty gas St ss)
        (Halted false (wordBytes (1 : U256)) (gas - cost) st' ss') ∧
      ReSt C st' (X - 1) (Y + 1) ∧
      ∀ n : U256, n ≠ mapSlot (0x1000 : U256) (0 : U256) →
        n ≠ mapSlot (0x2000 : U256) (0 : U256) → storageAt st' C n = storageAt St C n := by
  obtain ⟨hold, hre, h5, hb1, hb2⟩ := hS
  have hsz : im.data.size = 68 := by rw [hdata]; exact reData_size
  have hsl : selector im.data = 0xa9059cbb := by rw [hdata]; exact reData_sel
  have hA1 : loadWord im.data 4 32 = (0x2000 : U256) := by rw [hdata]; exact reData_arg1
  have hA2 : loadWord im.data 36 32 = (1 : U256) := by rw [hdata]; exact reData_arg2
  have hacc : hasAccount St C := hold.hasAccount
  have hacc' : hasAccount St im.currentTarget := by rw [hct]; exact hacc
  have hmO : bitwiseAnd (bitwiseAnd (0x2000 : U256)
      (1461501637330902918203684832716283019655932542975 : U256))
      (1461501637330902918203684832716283019655932542975 : U256) = 0x2000 := by decide
  have hW : Gas.writeMax fork = 22100 := by
    show (if fork ≥ Fork.glamsterdam then 110020 else 22100) = 22100
    exact if_neg (Nat.not_le.mpr hglam)
  rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  ·
    refine ⟨_, _, _, Paths.transfer_p6 (fork := fork) (message := im) (state := St)
      (substate := ss) hfork (by rw [hsz]; decide) (by rw [hsz]; decide) hsl hstatic hacc'
      (by rw [hv]; decide)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (gas := gas)
      (Nat.lt_of_le_of_lt
        (Nat.add_le_add_right
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add (Nat.le_refl 3503) (slotCost_le2100 _)) (slotCost_le2100 _))
            (slotCost_le2100 _)) (Gas.writeCost_le hfork _ _ _ _)) (slotCost_le2100 _))
            (Gas.writeCost_le hfork _ _ _ _)) 2300)
        (by rw [hW]; omega)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · repeat (first
        | exact hold
        | apply Reenter.holdsCode_writeSlot
        | apply Reenter.holdsCode_readSlot)
    · repeat (first
        | exact hre
        | apply Reenter.holdsCode_writeSlot
        | apply Reenter.holdsCode_readSlot)
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · intro n h1 h2
      simp (disch := supply_side) only [hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h1, h2, ↓reduceIte]
  ·
    refine ⟨_, _, _, Paths.transfer_p6 (fork := fork) (message := im) (state := St)
      (substate := ss) hfork (by rw [hsz]; decide) (by rw [hsz]; decide) hsl hstatic hacc'
      (by rw [hv]; decide)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (by
        simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel)
      (gas := gas)
      (Nat.lt_of_le_of_lt
        (Nat.add_le_add_right
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add (Nat.le_refl 3503) (slotCost_le2100 _)) (slotCost_le2100 _))
            (slotCost_le2100 _)) (Gas.writeCost_le hfork _ _ _ _)) (slotCost_le2100 _))
            (Gas.writeCost_le hfork _ _ _ _)) 2300)
        (by rw [hW]; omega)), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · repeat (first
        | exact hold
        | apply Reenter.holdsCode_writeSlot
        | apply Reenter.holdsCode_readSlot)
    · repeat (first
        | exact hre
        | apply Reenter.holdsCode_writeSlot
        | apply Reenter.holdsCode_readSlot)
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · simp (disch := supply_side) only [hv, hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h5, hb1, hb2] <;> decide +kernel
    · intro n h1 h2
      simp (disch := supply_side) only [hA1, hA2, hcw, hct, hmO, storageAt_readSlot,
        Readable.storageAt_writeSlot_ite, h1, h2, ↓reduceIte]

/-- The inner call under the real runner: `processRunner` does run it, with no error. -/
theorem re_inner_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {caller : Evm fork Nat} {im : Message fork} (lt : im.gas < bound) {C : Address}
    {X Y : U256} (hXY : (X = 2 ∧ Y = 0) ∨ (X = 1 ∧ Y = 1)) (hC : C.toU256 = WBTCW)
    (hcode : im.code = CODE) (htarget : im.target = some C) (hca : im.codeAddress = some C)
    (hct : im.currentTarget = C) (hdata : im.data = reData) (hv : im.value = 0)
    (hstatic : im.isStatic = false) (hcw : im.caller.toU256 = (0x1000 : U256))
    (hgas : im.gas = 200000) (hS : ReSt C caller.state X Y) :
    ∃ ch, processRunner (Meter := Nat) fork bound caller im lt = .ok ch ∧ ch.1.error = none ∧
      ReSt C ch.1.state (X - 1) (Y + 1) ∧
      ∀ n : U256, n ≠ mapSlot (0x1000 : U256) (0 : U256) →
        n ≠ mapSlot (0x2000 : U256) (0 : U256) →
        storageAt ch.1.state C n = storageAt caller.state C n := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨cost, st', ss', spec, s0, s1⟩ :=
    re_inner_spec hfork hglam (ss := caller.substate.child) hXY hct hdata hv hstatic hcw hS
      (gas := im.gas) (by omega)
  obtain ⟨ch, hch, hce, hcs, -⟩ :=
    spec_message_runs hparis lt hcode htarget (noPre_of hca (notPrecompile_wbtc hC)) hv spec
  exact ⟨ch, hch, hce, by rw [hcs]; exact s0, by rw [hcs]; exact s1⟩

/-! ## A call of WBTC to the token `RE` -/

/-- A message with no value from WBTC (at `C`) to the token, whose code is `RE`, with at least
210000 gas, in a state where the token has `X` and 0x2000 has `Y`. Under the real runner it ends
with no error and the output `reOut` (the word 1); inside it the token called
`transfer(0x2000, 1)` on WBTC, so after it the token has `X - 1` and 0x2000 has `Y + 1`. And the
run of the message is clean (`Trace.CleanRun`) for every condition `Q` that holds for the
messages with the keys of the inner call: the message itself does not enter `C`, the only
message that it sends is the inner call, which sends nothing, and no code is deposited. -/
theorem re_call_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {caller : Evm fork Nat} {msg : Message fork} {C : Address} {X Y : U256}
    (hXY : (X = 2 ∧ Y = 0) ∨ (X = 1 ∧ Y = 1)) (hC : C.toU256 = WBTCW)
    (lt : msg.gas < bound) (hcode : msg.code = RE) (htarget : msg.target = some TOKEN)
    (noPre : precompileAddress fork msg = none) (hv : msg.value = 0)
    (hcaller : msg.caller = C) (hct : msg.currentTarget = TOKEN)
    (hstatic : msg.isStatic = false) (hdepth : msg.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hg : 210000 ≤ msg.gas) (hS : ReSt C caller.state X Y) :
    (∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = reOut ∧ ReSt C child.1.state (X - 1) (Y + 1) ∧
      ∀ n : U256, n ≠ mapSlot (0x1000 : U256) (0 : U256) →
        n ≠ mapSlot (0x2000 : U256) (0 : U256) →
        storageAt child.1.state C n = storageAt caller.state C n) ∧
    ∀ (Q : Message fork → Prop),
      (∀ m : Message fork, callKeys m = [(0x1000 : U256), (0x2000 : U256), (1 : U256)] → Q m) →
      Trace.CleanRun C CODE Q caller msg := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hclc : caller.state.getCode (caller.state.getAccount msg.caller).codeHash = .ok CODE := by
    rw [hcaller]
    exact hS.hold.1
  have facts : ∀ (cl1 : Evm fork Nat) (im : Message fork),
      ReSends msg caller.state caller.substate.child CODE cl1 im →
      im.code = CODE ∧ im.target = some C ∧ im.codeAddress = some C ∧ im.currentTarget = C ∧
      im.data = reData ∧ im.value = 0 ∧ im.isStatic = false ∧
      im.caller.toU256 = (0x1000 : U256) ∧ ReSt C cl1.state X Y ∧
      ∀ n : U256, storageAt cl1.state C n = storageAt caller.state C n := by
    intro cl1 im hs
    obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hs
    refine ⟨r8, by rw [r6, hcaller], by rw [r7, hcaller], r5.trans hcaller, r9, r10,
      r12.trans hstatic, by rw [r4, hct]; exact token_toU256, ?_, ?_⟩
    · rw [r1]
      exact hS.rar2 _ _
    · intro n
      rw [r1, storageAt_rar, storageAt_rar]
  obtain ⟨child, cl1, im, lt', ch, hchild, hchildE, hchildO, hs, himg, hch, hchE, hst⟩ :=
    re_message_runs hparis hglam lt hcode htarget noPre hv hclc
      (fun _ => delegatedAddress_CODE) hdepth hg
      (fun cl1 im lt' hs hg => by
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, -⟩ := facts cl1 im hs
        obtain ⟨ch, hch, hce, -⟩ :=
          re_inner_runs hparis hglam lt' hXY hC f1 f2 f3 f4 f5 f6 f7 f8 hg f9
        exact ⟨ch, hch, hce⟩)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := facts cl1 im hs
  obtain ⟨ch', hch', -, e0, e1⟩ :=
    re_inner_runs hparis hglam lt' hXY hC f1 f2 f3 f4 f5 f6 f7 f8 himg f9
  have hchEq : ch' = ch := Except.ok.inj (hch'.symm.trans hch)
  rw [hchEq] at e0 e1
  refine ⟨⟨child, hchild, hchildE, hchildO, by rw [hst]; exact e0, fun n h1 h2 => by
    rw [hst, e1 n h1 h2, f10 n]⟩, ?_⟩
  intro Q hQ
  refine cleanRun_call (by rw [htarget]; rfl)
    (re_clean hparis hglam hcode hv hclc (fun _ => delegatedAddress_CODE) hdepth
      (show 5000 ≤ msg.gas by omega) (Nat.le_refl _)
      (fun h => absurd (hct.symm.trans h) (token_ne_wbtc hC)) ?_)
  intro cl2 im2 hs2 hg2
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, -⟩ := facts cl2 im2 hs2
  have hg3 : im2.gas = 200000 := hg2 hg
  obtain ⟨cost, st', ss', spec2, -⟩ :=
    re_inner_spec hfork hglam (ss := cl2.substate.child) hXY k4 k5 k6 k7 k8 k9
      (gas := im2.gas) (by omega)
  refine cleanRun_call (by rw [k2]; rfl)
    (clean_of_spec hparis k6 k1 spec2 (fun _ => hQ im2 ?_))
  have hA1 : loadWord im2.data 4 32 = (0x2000 : U256) := by rw [k5]; exact reData_arg1
  have hA2 : loadWord im2.data 36 32 = (1 : U256) := by rw [k5]; exact reData_arg2
  simp only [callKeys, k8, hA1, hA2, mk1, mk2]

/-! ## The whole run of reclaimToken -/

set_option maxHeartbeats 1000000 in
/-- THE RUN. reclaimToken(0x1000) sent to WBTC (at `C`) by its owner, when the token at 0x1000
holds the code `RE`, has 2 WBTC, and 0x2000 has none. The loop of the interpreter with the real
runner goes from the start frame to a stopped frame with no error and no output. Both calls of
reclaimToken (balanceOf, then transfer) ran `RE`, and each time `RE` called back
`transfer(0x2000, 1)` on WBTC: at the end the token has 0 and 0x2000 has 2, every other storage
word of `C` is as before, and `C` holds the code of WBTC. And the frame meets `Trace.CleanFrame`
for every condition `Q` that holds for the messages with the keys of the inner call. -/
theorem reclaim_re_core (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = WBTCW) {S : State.TransactionState}
    (hS : ReSt C S 2 0) {G : Nat} (hG : 32000000 ≤ G) (hG64 : G < 2 ^ 64) :
    ∃ s : Evm fork Nat,
      Goes (processRunner fork (rcMsg b t C Witness.CALLER1 0x1000 G).gas)
        (startFrame (rcMsg b t C Witness.CALLER1 0x1000 G) S ss
          (GasMeter.start (rcMsg b t C Witness.CALLER1 0x1000 G).gas
            (rcMsg b t C Witness.CALLER1 0x1000 G).reservoir)) s ∧
      s.running = false ∧ s.error = none ∧ s.output = ByteArray.empty ∧
      storageAt s.state C (mapSlot (0x1000 : U256) (0 : U256)) = 0 ∧
      storageAt s.state C (mapSlot (0x2000 : U256) (0 : U256)) = 2 ∧
      (∀ n : U256, n ≠ mapSlot (0x1000 : U256) (0 : U256) →
        n ≠ mapSlot (0x2000 : U256) (0 : U256) → storageAt s.state C n = storageAt S C n) ∧
      Reenter.HoldsCode C CODE s.state ∧
      ∀ (Q : Message fork → Prop),
        (∀ m : Message fork, callKeys m = [(0x1000 : U256), (0x2000 : U256), (1 : U256)] →
          Q m) →
        Trace.CleanFrame C CODE Q (rcMsg b t C Witness.CALLER1 0x1000 G).gas
          (startFrame (rcMsg b t C Witness.CALLER1 0x1000 G) S ss
            (GasMeter.start (rcMsg b t C Witness.CALLER1 0x1000 G).gas
              (rcMsg b t C Witness.CALLER1 0x1000 G).reservoir)) := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hGe : (rcMsg b t C Witness.CALLER1 0x1000 G).gas = G := rfl
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  -- the first call: balanceOf(WBTC) to the token
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, m_code, m_target, m_caller, m_ct, m_np, m_val,
      m_data, m_depth, m_static, hk⟩ :=
    first_call_s (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (tok := 0x1000) rfl tok_m rfl (owner_yes hS.own) hS.tok.1 re_size_ne
      (fun _ => re_not_delegated) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) hG64 (Nat.le_refl _) hstart
  have hS1 : ReSt C caller.state 2 0 := by
    rw [hcst]
    exact hS.callSt _
  have m_depth1 : msg.depth = 1 := m_depth
  obtain ⟨⟨child, hrun, cerr, cout, cS, coth⟩, cclean⟩ :=
    re_call_runs hparis hglam (Or.inl ⟨rfl, rfl⟩) hC hlt m_code m_target m_np m_val m_caller
      m_ct m_static (by rw [m_depth1]; decide) (by omega) hS1
  obtain ⟨a1, hga1, hba1, hgo1, hsn1, hat1⟩ := hk hlt child hrun
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr]
    rfl
  rw [hflag, cout, reOut_eq, extract_word] at hat1
  obtain ⟨hM1s, hM1fp, hM1w⟩ := mem_after (1 : U256) (mem1_size C) (by decide) (mem1_fp C)
  have hrd : isZero (lessThan (BitVec.ofNat 256 (wordBytes 1).size) (32 : U256)) ≠ 0 := by
    rw [size_wordBytes]
    decide
  -- the second call: transfer(owner, 1) to the token
  obtain ⟨caller2, msg2, hlt2, hmg2, hcst2, hcss2, n_code, n_target, n_caller, n_ct, n_np,
      n_val, n_data, n_depth, n_static, hk2⟩ :=
    second_call_s (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (st := child.1.state) tok_m2 hM1s hM1fp hM1w hrd (c := RE) cS.tok.1 re_size_ne
      (fun _ => re_not_delegated) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) (by omega) hba1 hat1
  have hS2 : ReSt C caller2.state (2 - 1) (0 + 1) := by
    rw [hcst2]
    exact cS.callSt _
  have n_depth1 : msg2.depth = 1 := n_depth
  obtain ⟨⟨child2, hrun2, cerr2, cout2, cS2, coth2⟩, cclean2⟩ :=
    re_call_runs hparis hglam (Or.inr ⟨by decide, by decide⟩) hC hlt2 n_code n_target n_np
      n_val n_caller n_ct n_static (by rw [n_depth1]; decide) (by omega) hS2
  obtain ⟨a2, y1, y2, y3, t2, hga2, hgo2, hsn2, hat2⟩ := hk2 hlt2 child2 hrun2
  have hflag2 : (if child2.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr2]
    rfl
  rw [hflag2, cout2, reOut_eq, extract_word] at hat2
  obtain ⟨hM2s, hM2fp⟩ := mem2_facts (ownW child.1.state C) 1 hM1s hM1fp
  obtain ⟨hM3s, hM3fp, hM3w⟩ := mem_after (1 : U256) hM2s (by decide) hM2fp
  obtain ⟨s, hr, hrun3, herr, hout, hst, hsub⟩ :=
    seg3_ok hberlin hM3s hM3fp hM3w hrd (by decide) (by omega) hat2
  refine ⟨s, (hgo1.trans hgo2).trans (Goes.of_reaches _ hr), hrun3, herr, hout, ?_, ?_, ?_,
    by rw [hst]; exact cS2.hold, ?_⟩
  · rw [hst, cS2.b1]
    decide
  · rw [hst, cS2.b2]
    decide
  · intro n h1 h2
    rw [hst, coth2 n h1 h2, hcst2, storageAt_callSt, coth n h1 h2, hcst, storageAt_callSt]
  · intro Q hQ c m hsent
    rcases hsn1 c m hsent with ⟨hc0, hm0⟩ | hs1
    · rw [hc0, hm0]
      exact cclean Q hQ
    · rcases hsn2 c m hs1 with ⟨hc0, hm0⟩ | hs2
      · rw [hc0, hm0]
        exact cclean2 Q hQ
      · exact absurd hs2 (Trace.not_sent_of_reaches hr hrun3 _ c m)

end WbtcVerify.Sanity

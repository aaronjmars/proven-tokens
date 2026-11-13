import WbtcVerify.Wbtc.ReclaimWit.ReRun
import WbtcVerify.Wbtc.SeqLocal
import WbtcVerify.Wbtc.Sanity.Base

/-!
# reclaimToken against a token that calls back into WBTC: the reentrancy theorems applied

Written by hand (not generated). Fix of audit 4 (the gap of LINK-4, here for WBTC). The run of
ReclaimWit/ReRun.lean (the owner reclaims a token whose code `RE` calls back
`WBTC.transfer(0x2000, 1)` from inside both calls of reclaimToken) meets the hypotheses of the
run-local reentrancy theorems, and they are applied to it.

- `supply_reclaim_re_frame`: the frame of reclaimToken run by the loop of the interpreter with
  EthLib's real runner ends with no error; it meets `CleanFrameW`; so `supply_all_real_local`
  (AnyLocal.lean) gives the invariant at the end.
- `process_reclaim_re`: `processMessage` ends the message with no error; the run meets `CleanW`
  (the messages that enter WBTC are the top-level one and the two inner calls; no code is
  deposited); so `process_good_local` (SeqLocal.lean) gives a good end state.
- `msgL_reclaim_re`: the run is one step `MsgL` of the sequences of SeqLocal.lean.
- `reState`, `holdsCode_reState`, `tokenCode_reState`, `inv_reState`, `reSt_reState`: a closed
  start state. WBTC at `WBTC_ADDRESS`, owner `Witness.CALLER1`, not paused; the token at the
  address of the word 0x1000 holds `RE` and has 2 WBTC; `totalSupply_` is 2.
- `reclaim_reenter_closed`: THE CLOSED WITNESS on `reState`, with a gas limit of 32,000,000:
  no error, the token ends with 0 and 0x2000 with 2, `CleanW`, `GoodWbtc`, `RunL`, and the
  invariant at the end by `inv_runL`.

Hypotheses that stay (keccak, NOT proved), each named in the statements:

- `hA : Sep RE_KEYS`: the separation of slots for the five words of the run (the owner, 0x1000,
  0x2000, 1, 0). The words 1 and 0 are there because `callKeys` reads the two argument words of
  every call as possible address keys. It also gives the invariant of the start state.
- `hH : hashOf CODE ≠ EMPTY_CODE_HASH` and `hRE : hashOf RE ≠ hashOf CODE`: the hash of the code
  of WBTC is not the hash of the empty code, nor the hash of `RE` (the kernel cannot compute the
  keccak of the 4,582 bytes of the code within the memory of the build box).

Not covered: other tokens, other amounts, a token that calls another function of WBTC;
`Sep RE_KEYS` is not proved.
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


/-! ## The message and its keys -/

/-- The message of the witness: reclaimToken(0x1000) from `Witness.CALLER1` to `C`, gas `G`. -/
abbrev reMsg (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (G : Nat) : Message fork :=
  rcMsg b t C Witness.CALLER1 0x1000 G

/-- The start frame of the message. -/
abbrev reFrame (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (G : Nat) (S : State.TransactionState) (ss : Substate) : Evm fork Nat :=
  startFrame (reMsg b t C G) S ss (GasMeter.start (reMsg b t C G).gas (reMsg b t C G).reservoir)

/-- The address words of the run: the owner, the token, the address that the token pays, and
the two argument words 1 and 0 that `callKeys` reads as possible address keys. -/
def RE_KEYS : List U256 := [Witness.CALLER1W, 0x1000, 0x2000, 1, 0]

/-- The keys of the top-level message. -/
theorem callKeys_reMsg (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) (G : Nat) : callKeys (reMsg b t C G) = [Witness.CALLER1W, 0x1000, 0] := by
  show [Witness.CALLER1.toU256,
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord (data1 SEL_RECLAIM (0x1000 : U256)) 4 32),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord (data1 SEL_RECLAIM (0x1000 : U256)) 36 32)] = _
  decide +kernel

theorem reMsg_size (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C : Address) (G : Nat) : (reMsg b t C G).data.size < 2 ^ 256 := by
  show (data1 SEL_RECLAIM (0x1000 : U256)).size < 2 ^ 256
  rw [rc_size rfl]
  decide

/-- The keys of the top-level message are among the five words. -/
theorem sep_outer (hA : Sep RE_KEYS) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C : Address) (G : Nat) : Sep (callKeys (reMsg b t C G)) := by
  rw [callKeys_reMsg]
  refine hA.restrict (fun x hx => ?_)
  simp only [RE_KEYS, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- The keys of an inner call are among the five words. -/
theorem sep_inner (hA : Sep RE_KEYS) {m : Message fork}
    (hk : callKeys m = [(0x1000 : U256), (0x2000 : U256), (1 : U256)]) : SepMsg m := by
  unfold SepMsg
  rw [hk]
  refine hA.restrict (fun x hx => ?_)
  simp only [RE_KEYS, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
  rcases hx with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-! ## The frame level -/

/-- `supply_all_real_local` APPLIED TO A RUN WITH A TOKEN THAT CALLS BACK. In any state `S`
where `C` holds the code of WBTC, the token at 0x1000 holds `RE` and has 2 WBTC, 0x2000 has
none, `Witness.CALLER1` is the owner (`ReSt C S 2 0`), and the invariant holds: the frame of
reclaimToken(0x1000) run by the loop of the interpreter with `processRunner` ends with no
error; the end balances show the two inner calls; the frame meets `CleanFrameW` (the run-local
condition of AnyLocal.lean); and so, by `supply_all_real_local`, the invariant holds at the
end. The only hypothesis on keccak is `Sep` of the five words of the run. -/
theorem supply_reclaim_re_frame (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = WBTCW) {S : State.TransactionState}
    (hS : ReSt C S 2 0) (hinv : Inv C S) (hA : Sep RE_KEYS)
    {G : Nat} (hG : 32000000 ≤ G) (hG64 : G < 2 ^ 64) :
    ∃ (within : GasMeter.gasHeld (reFrame b t C G S ss).gas ≤ (reMsg b t C G).gas) (s : Evm fork Nat),
      Evm.runFrame (step fork) (step_decreases fork) (reMsg b t C G).gas (processRunner fork (reMsg b t C G).gas)
        (reFrame b t C G S ss) within = .ok s ∧
      s.error = none ∧ s.output = ByteArray.empty ∧
      storageAt s.state C (mapSlot (0x1000 : U256) (0 : U256)) = 0 ∧
      storageAt s.state C (mapSlot (0x2000 : U256) (0 : U256)) = 2 ∧
      CleanFrameW C (reMsg b t C G).gas (reFrame b t C G S ss) ∧ Inv C s.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨s, hgo, hstop, herr, hout, b1, b2, -, -, hclean⟩ :=
    reclaim_re_core hparis hglam b t ss hC hS hG hG64
  have within := start_within (reMsg b t C G) S ss
  have hrun := hgo.result hstop within
  have clean : CleanFrameW C (reMsg b t C G).gas (reFrame b t C G S ss) :=
    hclean (fun m => SepMsg m) (fun m hk => sep_inner hA hk)
  refine ⟨within, s, hrun, herr, hout, b1, b2, clean, ?_⟩
  exact supply_all_real_local (message := (reMsg b t C G)) hfork hglam (reMsg_size b t C G)
    (sep_outer hA b t C G) hS.hold hinv clean (At.startFrame (code := CODE) rfl S ss) within
    hrun herr

/-! ## The message level -/

/-- `process_good_local` APPLIED TO A RUN WITH A TOKEN THAT CALLS BACK. In a state `S` as above:
EthLib's `processMessage` ends the message reclaimToken(0x1000) with no error and no output; at
the end the token has 0 WBTC and 0x2000 has 2 (the two inner calls), every other storage word of
`C` is as before; the run of the message meets `CleanW` (the run-local condition of
SeqLocal.lean: the top-level call and the two inner calls are the only messages that enter `C`,
and no code is deposited); and so, by `process_good_local`, the end state is good: `C` holds
the code of WBTC and the sum of the balances is `totalSupply_`. -/
theorem process_reclaim_re (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = WBTCW) {S : State.TransactionState}
    (hS : ReSt C S 2 0) (hinv : Inv C S) (hA : Sep RE_KEYS)
    {G : Nat} (hG : 32000000 ≤ G) (hG64 : G < 2 ^ 64) :
    ∃ ended, processMessage (Meter := Nat) fork (reMsg b t C G) S ss = .ok ended ∧
      ended.1.error = none ∧ ended.1.output = ByteArray.empty ∧
      storageAt ended.1.state C (mapSlot (0x1000 : U256) (0 : U256)) = 0 ∧
      storageAt ended.1.state C (mapSlot (0x2000 : U256) (0 : U256)) = 2 ∧
      (∀ n : U256, n ≠ mapSlot (0x1000 : U256) (0 : U256) →
        n ≠ mapSlot (0x2000 : U256) (0 : U256) →
        storageAt ended.1.state C n = storageAt S C n) ∧
      CleanW C (reMsg b t C G) S ss (GasMeter.start (reMsg b t C G).gas (reMsg b t C G).reservoir) ∧
      GoodWbtc C ended.1.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨s, hgo, hstop, herr, hout, b1, b2, both, -, hclean⟩ :=
    reclaim_re_core hparis hglam b t ss hC hS hG hG64
  have hv : (reMsg b t C G).value = 0 := rfl
  obtain ⟨r, hpm, hr1⟩ := message_of_goes hparis
    (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) hv hgo hstop
  rw [rollbackOnError_of_error_eq_none herr] at hr1
  have clean : CleanW C (reMsg b t C G) S ss (GasMeter.start (reMsg b t C G).gas (reMsg b t C G).reservoir) := by
    intro e he
    cases he with
    | self => exact fun _ => sep_outer hA b t C G
    | sub fo hs ho =>
      rw [frameOf_noValue hparis hv fo] at hs
      exact hclean (fun m => SepMsg m) (fun m hk => sep_inner hA hk) _ _ hs e ho
  refine ⟨r, hpm, by rw [hr1]; exact herr, by rw [hr1]; exact hout, by rw [hr1]; exact b1,
    by rw [hr1]; exact b2, fun n h1 h2 => by rw [hr1]; exact both n h1 h2, clean, ?_⟩
  exact process_good_local hfork hglam (L := C) (message := (reMsg b t C G))
    (fun _ => ⟨rfl, rfl, reMsg_size b t C G⟩) ⟨hS.hold, hinv⟩ clean hpm

/-- The run is one step `MsgL` of the sequences of SeqLocal.lean, to a state with the end
balances of the two inner calls. -/
theorem msgL_reclaim_re (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = WBTCW) {S : State.TransactionState}
    (hS : ReSt C S 2 0) (hinv : Inv C S) (hA : Sep RE_KEYS)
    {G : Nat} (hG : 32000000 ≤ G) (hG64 : G < 2 ^ 64) :
    ∃ S' : State.TransactionState, MsgL C S S' ∧
      storageAt S' C (mapSlot (0x1000 : U256) (0 : U256)) = 0 ∧
      storageAt S' C (mapSlot (0x2000 : U256) (0 : U256)) = 2 := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨ended, hpm, -, -, b1, b2, -, clean, -⟩ :=
    process_reclaim_re hparis hglam b t ss hC hS hinv hA hG hG64
  exact ⟨ended.1.state,
    ⟨fork, (reMsg b t C G), ss, _, _, ended, hfork, hglam,
      fun _ => ⟨rfl, rfl, reMsg_size b t C G⟩, clean, hpm, rfl⟩, b1, b2⟩

/-! ## A closed start state -/

/-- A state with one more account, at `a`, that holds `code` (nonce 1, no ether), kept under its
keccak hash as EthLib's `setCode` keeps it. -/
def addCode (S : State.TransactionState) (a : Address) (code : ByteArray) :
    State.TransactionState :=
  { S.setAccount a (some ⟨1, 0, hashOf code⟩) with
    codeWrites := (S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code }

/-- `addCode` keeps every storage word. -/
theorem storageAt_addCode (S : State.TransactionState) (a : Address) (code : ByteArray)
    (C : Address) (n : U256) : storageAt (addCode S a code) C n = storageAt S C n := rfl

/-- `addCode` keeps what `getStorage` reads. -/
theorem getStorage_addCode (S : State.TransactionState) (a : Address) (code : ByteArray)
    (C : Address) (k : EthLib.Base.Bytes32) :
    (addCode S a code).getStorage C k = S.getStorage C k := rfl

/-- The code hash of the new account. -/
theorem codeHash_addCode_self (S : State.TransactionState) (a : Address) (code : ByteArray) :
    ((addCode S a code).getAccount a).codeHash = hashOf code := by
  have e : (addCode S a code).getAccountOptional a = some ⟨1, 0, hashOf code⟩ :=
    getAccountOptional_setAccount_self S a (some ⟨1, 0, hashOf code⟩)
  unfold State.TransactionState.getAccount
  rw [e] <;> rfl

/-- The code hash of another account is kept. -/
theorem codeHash_addCode_other (S : State.TransactionState) {a o : Address}
    (code : ByteArray) (h : o ≠ a) :
    ((addCode S a code).getAccount o).codeHash = (S.getAccount o).codeHash := by
  have e : (addCode S a code).getAccountOptional o = S.getAccountOptional o :=
    getAccountOptional_setAccount_of_ne S (some ⟨1, 0, hashOf code⟩) h
  unfold State.TransactionState.getAccount
  rw [e]

/-- `addCode` gives the new code under its hash, when it is not the hash of the empty code. -/
theorem getCode_addCode_self (S : State.TransactionState) (a : Address) {code : ByteArray}
    (hH : hashOf code ≠ EMPTY_CODE_HASH) :
    (addCode S a code).getCode (hashOf code) = .ok code := by
  have e2 : (addCode S a code).codeWrites[hashOf code]? = some code := by
    show ((S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[hashOf code]? = some code
    simp
  unfold State.TransactionState.getCode
  rw [if_neg hH, e2]

/-- `addCode` keeps the code under every other hash. -/
theorem getCode_addCode_other (S : State.TransactionState) (a : Address) {code : ByteArray}
    {h : EthLib.Base.Hash32} (hne : hashOf code ≠ h) :
    (addCode S a code).getCode h = S.getCode h := by
  have e2 : (addCode S a code).codeWrites[h]? = S.codeWrites[h]? := by
    show ((S.setAccount a (some ⟨1, 0, hashOf code⟩)).codeWrites.insert
      (hashOf code) code)[h]? = S.codeWrites[h]?
    simp [Std.ExtTreeMap.getElem?_insert, hne]
    rfl
  unfold State.TransactionState.getCode
  rw [e2]
  rfl

/-- The hash of `RE` is not the hash of the empty code (computed in the kernel). -/
theorem re_hash_ne : hashOf RE ≠ EMPTY_CODE_HASH := by decide +kernel

/-- The state before the token is added: the code of WBTC at `WBTC_ADDRESS`; slot 5 says that
`Witness.CALLER1` is the owner and the token is not paused; `totalSupply_` (slot 1) is 2; the
address of the word 0x1000 has 2 WBTC; every other storage word is 0. -/
abbrev reBase : State.TransactionState :=
  codeState WBTC_ADDRESS
    [((5 : U256), OWNER_SLOT), ((1 : U256), (2 : U256)),
      (mapSlot (0x1000 : U256) (0 : U256), (2 : U256))] WBTC_ADDRESS CODE

/-- THE START STATE: `reBase` with one more account, at the address of the word 0x1000, that
holds the code `RE`. -/
abbrev reState : State.TransactionState := addCode reBase TOKEN RE

/-- `WBTC_ADDRESS` holds the code of WBTC in `reState`. -/
theorem holdsCode_reState (hH : hashOf CODE ≠ EMPTY_CODE_HASH)
    (hRE : hashOf RE ≠ hashOf CODE) : Reenter.HoldsCode WBTC_ADDRESS CODE reState := by
  have e : (reState.getAccount WBTC_ADDRESS).codeHash =
      (reBase.getAccount WBTC_ADDRESS).codeHash :=
    codeHash_addCode_other reBase RE (token_ne_wbtc wbtc_address_word).symm
  have e0 : (reBase.getAccount WBTC_ADDRESS).codeHash = hashOf CODE :=
    codeHash_codeState_self _ _ _
  refine ⟨?_, by rw [e, e0]; exact hH, by rw [e]; exact e0⟩
  rw [e, e0, getCode_addCode_other reBase _ hRE, ← e0]
  exact getCode_codeState _ _ _ hH

/-- The address of the word 0x1000 holds the code `RE` in `reState`. No hypothesis: the hash of
`RE` is computed in the kernel. -/
theorem tokenCode_reState : Reenter.HoldsCode TOKEN RE reState :=
  ⟨by rw [codeHash_addCode_self]; exact getCode_addCode_self _ _ re_hash_ne,
    by rw [codeHash_addCode_self]; exact re_hash_ne, codeHash_addCode_self _ _ _⟩

theorem own_reState : storageAt reState WBTC_ADDRESS (5 : U256) = OWNER_SLOT := by
  rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_pos rfl]

theorem total_reState : storageAt reState WBTC_ADDRESS (1 : U256) = 2 := by
  rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_neg (by decide),
    storageAt_sState_cons, if_pos rfl]

theorem b1_reState :
    storageAt reState WBTC_ADDRESS (mapSlot (0x1000 : U256) (0 : U256)) = 2 := by
  rw [storageAt_addCode]
  simp only [storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil] <;>
    decide +kernel

theorem b2_reState :
    storageAt reState WBTC_ADDRESS (mapSlot (0x2000 : U256) (0 : U256)) = 0 := by
  rw [storageAt_addCode]
  simp only [storageAt_codeState, storageAt_sState_cons, storageAt_sState_nil] <;>
    decide +kernel

/-- `reState` is a start state of the run. `hH`, `hRE`: on the hash of the code of WBTC. -/
theorem reSt_reState (hH : hashOf CODE ≠ EMPTY_CODE_HASH) (hRE : hashOf RE ≠ hashOf CODE) :
    ReSt WBTC_ADDRESS reState 2 0 :=
  ⟨holdsCode_reState hH hRE, tokenCode_reState, own_reState, b1_reState, b2_reState⟩

/-- The sum of the balances of `reState` is 2, the word of slot 1. `hA`: the separation of
slots (keccak, not proved) says that no other address has the balance slot of 0x1000 and that
slot 1 and slot 5 are balance slots of no address. -/
theorem inv_reState (hA : Sep RE_KEYS) : Inv WBTC_ADDRESS reState := by
  have hu : Supply.UniqBal 0 (0x1000 : U256) := hA.uniq _ (by simp [RE_KEYS])
  have ha : (0x1000 : U256).toNat < 2 ^ 160 := by decide
  have hfg : ∀ i : Nat, i < 2 ^ 160 → i ≠ (0x1000 : U256).toNat →
      Supply.bal 0 WBTC_ADDRESS reState i = (fun _ => (0 : Int)) i := by
    intro i hi hne
    have hi' : i < 2 ^ 256 := Nat.lt_trans hi (by decide)
    have ht : (BitVec.ofNat 256 i).toNat = i := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hi'
    have hk : ¬ mapSlot (0x1000 : U256) 0 = mapSlot (BitVec.ofNat 256 i) 0 := by
      intro e
      have h1 := hu (BitVec.ofNat 256 i) (by rw [ht]; exact hi) e.symm
      exact hne (by rw [← ht, h1])
    have h5 : ¬ (5 : U256) = mapSlot (BitVec.ofNat 256 i) 0 :=
      hA.fixed.1 _ (by rw [ht]; exact hi)
    have h1 : ¬ (1 : U256) = mapSlot (BitVec.ofNat 256 i) 0 :=
      hA.total _ (by rw [ht]; exact hi)
    show ((storageAt reState WBTC_ADDRESS (mapSlot (BitVec.ofNat 256 i) 0)).toNat : Int) = 0
    rw [storageAt_addCode, storageAt_codeState, storageAt_sState_cons, if_neg h5,
      storageAt_sState_cons, if_neg h1, storageAt_sState_cons, if_neg hk, storageAt_sState_nil]
    rfl
  show Supply.sumBal 0 WBTC_ADDRESS reState -
    ((storageAt reState WBTC_ADDRESS 1).toNat : Int) = 0
  unfold Supply.sumBal
  rw [Supply.sumTo_update (f := fun _ => (0 : Int)) (a := (0x1000 : U256).toNat) (2 ^ 160) ha
    hfg, sumTo_zero]
  show (0 : Int) - 0 +
    ((storageAt reState WBTC_ADDRESS
      (mapSlot (BitVec.ofNat 256 (0x1000 : U256).toNat) 0)).toNat : Int) -
    ((storageAt reState WBTC_ADDRESS 1).toNat : Int) = 0
  rw [Supply.ofNat_toNat, b1_reState, total_reState]
  decide

/-! ## The closed witness -/

/-- THE CLOSED WITNESS OF A TOKEN THAT CALLS BACK. From the state `reState`, at every fork from
Paris and before Glamsterdam, in every block and transaction environment: EthLib's
`processMessage` ends the message reclaimToken(0x1000) from the owner `CALLER1` to WBTC (gas
limit 32,000,000) with no error. The token, whose code is `RE`, called `transfer(0x2000, 1)` on
WBTC from inside its `balanceOf` and again from inside its `transfer`: at the end the token has
0 WBTC and the address 0x2000 has 2. The run meets the run-local condition `CleanW`, the end
state is good by `process_good_local`, the run is a sequence `RunL` from `reState`, and the sum
of the balances at the end is `totalSupply_` by `inv_runL`.

Hypotheses (keccak, not proved): `hA` on the five words of the run, `hH` and `hRE` on the hash
of the code of WBTC. -/
theorem reclaim_reenter_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    (hH : hashOf CODE ≠ EMPTY_CODE_HASH) (hRE : hashOf RE ≠ hashOf CODE)
    (hA : Sep RE_KEYS) :
    ∃ ended, processMessage (Meter := Nat) fork (reMsg b t WBTC_ADDRESS 32000000) reState ss =
        .ok ended ∧
      ended.1.error = none ∧ ended.1.output = ByteArray.empty ∧
      storageAt ended.1.state WBTC_ADDRESS (mapSlot (0x1000 : U256) (0 : U256)) = 0 ∧
      storageAt ended.1.state WBTC_ADDRESS (mapSlot (0x2000 : U256) (0 : U256)) = 2 ∧
      CleanW WBTC_ADDRESS (reMsg b t WBTC_ADDRESS 32000000) reState ss
        (GasMeter.start (reMsg b t WBTC_ADDRESS 32000000).gas
          (reMsg b t WBTC_ADDRESS 32000000).reservoir) ∧
      GoodWbtc WBTC_ADDRESS ended.1.state ∧
      RunL WBTC_ADDRESS reState ended.1.state ∧
      Inv WBTC_ADDRESS ended.1.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hS := reSt_reState hH hRE
  have hinv := inv_reState hA
  obtain ⟨ended, hpm, hok, hout, b1, b2, -, clean, good⟩ :=
    process_reclaim_re hparis hglam b t ss wbtc_address_word hS hinv hA (Nat.le_refl _)
      (by decide)
  have hmsg : MsgL WBTC_ADDRESS reState ended.1.state :=
    ⟨fork, reMsg b t WBTC_ADDRESS 32000000, ss, _, _, ended, hfork, hglam,
      fun _ => ⟨rfl, rfl, reMsg_size b t WBTC_ADDRESS 32000000⟩, clean, hpm, rfl⟩
  have hrunL : RunL WBTC_ADDRESS reState ended.1.state := RunL.msg hmsg (RunL.nil _)
  exact ⟨ended, hpm, hok, hout, b1, b2, clean, good, hrunL, inv_runL hrunL hS.hold hinv⟩

end WbtcVerify.Sanity

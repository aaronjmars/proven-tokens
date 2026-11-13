import WbtcVerify.Wbtc.Sanity.ReclaimRun

/-!
# Sanity witnesses for reclaimToken(address) under EthLib's real interpreter

Written by hand (not generated), independent of the Hoare proofs of `supply_reclaimToken`. Each
theorem is a complete concrete run of `processMessage` (the real message layer, whose runner of
child messages is the real `processRunner`), from Paris and before Glamsterdam.

The message is `rcMsg`: reclaimToken(0x1000) sent to the contract by `Witness.CALLER1` with `G`
gas and no value. The token is the address of the word 0x1000 (`TOKEN`).

Proved (each with a `_closed` form at `WBTC_ADDRESS` on a concrete state, with no hypothesis left
but the two fork bounds):
- `reclaimToken_runs`: the caller is the owner in slot 5 and the token holds `ONE_CODE` (ten
  bytes that answer every call with the word 1): the run ends with no error and no output, every
  storage word of every address reads as before, no log is added, the token is among the
  accessed addresses, and the final state is the state before with the reads of the two calls
  recorded (slot 5 twice, the account of the token four times, the account of the contract
  twice).
- `reclaimToken_notOwner_reverts`: another owner in slot 5: revert, no output.
- `reclaimToken_noCode_reverts`: no code at the token: revert, no output.
- `reclaimToken_calleeReverts`: the token holds `REVERT_CODE` (reverts every call with the word
  42 as data): reclaimToken reverts and its output is exactly these 32 bytes.
- `reclaimToken_shortReturn_reverts`: the token holds the one byte STOP (returns no data):
  revert, no output.
- `reclaimToken_falseReturn_reverts`: the token holds `ZERO_CODE` (answers every call with the
  word 0, so transfer "returns false"): both calls happen, then revert, no output.
  In every failing case every storage word of every address reads as before the message.
- `tiny_token_keeps`, `one_token_call_runs`: the satisfiability witness for the assumption on the
  callee of the supply theorem: for every frame `caller` (so also from a state where WBTC holds
  its code), a message with no value to the token that holds `ONE_CODE`, with any data (the 36
  bytes of balanceOf(this), the 68 bytes of transfer(owner, 1)) and at least 18 gas, is run by
  the real runner to a frame with no error whose state is the state of the caller, so every
  storage word of WBTC is as it was; and every frame with no error that the real runner gives
  for such a message has the state of the caller.

Assumed: the fork bounds, and in the general forms the word of the contract address, slot 5, the
code at the token, and the gas (at least 2,000,000 for the runs with two calls, under 2^64).
Not covered: the exact gas left, a callee that fails with return data of another size than 32
bytes, a second call that fails, the token WBTC itself (see `Sanity/ReclaimSelf.lean`).
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

/-! ## The message, the token, the owner -/

/-- reclaimToken(tok) sent to `C` by `caller` with `G` gas and no value. -/
abbrev rcMsg (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C caller : Address)
    (tok : U256) (G : Nat) : Message fork :=
  { sMsg b t C caller CODE (data1 SEL_RECLAIM tok) with gas := G }

/-- The token of the witnesses: the address of the word 0x1000. -/
abbrev TOKEN : Address := toAddressMasked (0x1000 : U256)

/-- Slot 5 when `Witness.CALLER1` is the owner (the owner is in the bits 8..167). -/
abbrev OWNER_SLOT : U256 := 0x010101010101010101010101010101010101010100

/-- Slot 5 when another address is the owner. -/
abbrev OTHER_SLOT : U256 := 0x020202020202020202020202020202020202020200

theorem tok_m : bitwiseAnd (0x1000 : U256) MASK = 0x1000 := by decide

theorem tok_m2 : bitwiseAnd MASK (0x1000 : U256) = 0x1000 := by decide

theorem notPrecompile_token :
    Precompiles.isPrecompile fork (toAddressMasked (0x1000 : U256)).toU256.toNat = false := by
  rw [EthLib.Base.toNat_toU256_toAddressMasked]
  have h : (0x1000 : U256).toNat % 2 ^ 160 = 4096 := by decide
  rw [h]
  rfl

theorem notPrecompile_wbtc {C : Address}
    (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256)) :
    Precompiles.isPrecompile fork C.toU256.toNat = false := by
  rw [hC]
  rfl

theorem wbtc_ne_token : WBTC_ADDRESS ≠ TOKEN := by
  intro h
  have h2 : WBTC_ADDRESS.toU256.toNat = (toAddressMasked (0x1000 : U256)).toU256.toNat :=
    congrArg (fun a : Address => a.toU256.toNat) h
  rw [EthLib.Base.toNat_toU256_toAddressMasked, wbtc_address_word] at h2
  exact absurd h2 (by decide)

/-- The caller is the owner of `OWNER_SLOT`. -/
theorem owner_yes {S : State.TransactionState} {C : Address}
    (h5 : storageAt S C (5 : U256) = OWNER_SLOT) :
    equal Witness.CALLER1.toU256
      (bitwiseAnd MASK (div (storageAt S C (5 : U256)) (256 : U256))) ≠ 0 := by
  rw [Witness.caller1_toU256, h5]
  decide

/-- The caller is not the owner of `OTHER_SLOT`. -/
theorem owner_no {S : State.TransactionState} {C : Address}
    (h5 : storageAt S C (5 : U256) = OTHER_SLOT) :
    equal Witness.CALLER1.toU256
      (bitwiseAnd MASK (div (storageAt S C (5 : U256)) (256 : U256))) = 0 := by
  rw [Witness.caller1_toU256, h5]
  decide

theorem tiny_size_ne (b last : UInt8) :
    isZero (isZero (BitVec.ofNat 256 (tinyCode b last).size)) ≠ 0 := by
  rw [size_tinyCode]
  decide

/-- The reads that a frame records up to a CALL keep the block of the state. -/
theorem parent_callSt (S : State.TransactionState) (C A : Address) :
    (callSt S C A).parent = S.parent := rfl

/-! ## Two calls to a token that answers with a word -/

/-- reclaimToken(tok) sent by the owner when the token holds a `tinyCode b` that returns the word
`v`: the loop of the interpreter, with the real runner, goes through both calls to a frame at
3212, with the flag 1 and the word `v` in the memory at 128. -/
theorem tiny_two_calls (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {S : State.TransactionState} {ss : Substate} {tok : U256}
    (hdata : message.data = data1 SEL_RECLAIM tok) (hm : bitwiseAnd tok MASK = tok)
    (hm2 : bitwiseAnd MASK tok = tok) (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt S message.currentTarget (5 : U256)) (256 : U256))) ≠ 0)
    (b : UInt8) {v : U256} (hv : tinyOut b = wordBytes v)
    (hcode : S.getCode (S.getAccount (toAddressMasked tok)).codeHash = .ok (tinyCode b 0xf3))
    (hdel : .pectra ≤ fork → delegatedAddress (tinyCode b 0xf3) = none)
    (hnp : Precompiles.isPrecompile fork (toAddressMasked tok).toU256.toNat = false)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas : Nat} (hg : 2000000 ≤ gas) (hb : gas ≤ bound) (hb64 : bound < 2 ^ 64)
    {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas S ss evm) :
    ∃ (after : Evm fork Nat) (ss2 : Substate) (x1 x2 x3 bal owner t2 t sel : U256)
      (mem : ByteArray),
      Goes (processRunner fork bound) evm after ∧ 200 ≤ after.gas ∧ mem.size = 224 ∧
      loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256) ∧
      loadWord (memoryReadBytes mem 128 32) 0 32 = v ∧
      ss2.logs = ss.logs ∧ toAddressMasked tok ∈ ss2.accessedAddresses ∧
      Logic.At CODE message 3212
        (1 :: x1 :: x2 :: x3 :: [bal, owner, t2, (1617 : U256), bal, t, (570 : U256), sel]) mem
        after.gas
        (callSt (callSt S message.currentTarget (toAddressMasked tok)) message.currentTarget
          (toAddressMasked tok)) ss2 (wordBytes v) after := by
  have hcs := tiny_size_ne b 0xf3
  have hrd : isZero (lessThan (BitVec.ofNat 256 (wordBytes v).size) (32 : U256)) ≠ 0 := by
    rw [size_wordBytes]
    decide
  -- the first call
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, m_code, m_target, -, -, m_np, m_val, -, -, -, hk⟩ :=
    first_call (bound := bound) hparis hglam hdata hm hval hown hcode hcs hdel hnp hdepth
      (by omega) (by omega) hb start
  obtain ⟨child, hrun, cerr, cout, cst, css⟩ :=
    tiny_message_runs hparis b (caller := caller) hlt m_code m_target m_np m_val (by omega)
  obtain ⟨a1, hga1, hba1, hgo1, hat1⟩ := hk hlt child hrun
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr]
    rfl
  have hl1 := logs_after cerr css hcss
  rw [hflag, cout, hv, extract_word, cst, hcst] at hat1
  obtain ⟨hM1s, hM1fp, hM1w⟩ := mem_after v (mem1_size message.currentTarget) (by decide)
    (mem1_fp message.currentTarget)
  have hcode2 : (callSt S message.currentTarget (toAddressMasked tok)).getCode
      ((callSt S message.currentTarget (toAddressMasked tok)).getAccount
        (toAddressMasked tok)).codeHash = .ok (tinyCode b 0xf3) := hcode
  -- the second call
  obtain ⟨caller2, msg2, hlt2, hmg2, hcst2, hcss2, n_code, n_target, -, -, n_np, n_val, -, -, -,
      hk2⟩ :=
    second_call (bound := bound) hparis hglam hm2 hM1s hM1fp hM1w hrd
      (c := tinyCode b 0xf3) hcode2 hcs hdel hnp hdepth (by omega) (by omega) hba1 hat1
  obtain ⟨child2, hrun2, cerr2, cout2, cst2, css2⟩ :=
    tiny_message_runs hparis b (caller := caller2) hlt2 n_code n_target n_np n_val (by omega)
  obtain ⟨a2, y1, y2, y3, t2, hga2, hgo2, hat2⟩ := hk2 hlt2 child2 hrun2
  have hflag2 : (if child2.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr2]
    rfl
  have hl2 := logs_after cerr2 css2 hcss2
  have hacc2 := accessed_after cerr2 css2 hcss2
  rw [hflag2, cout2, hv, extract_word, cst2, hcst2] at hat2
  obtain ⟨hM2s, hM2fp⟩ := mem2_facts
    (ownW (callSt S message.currentTarget (toAddressMasked tok)) message.currentTarget) v
    hM1s hM1fp
  obtain ⟨hM3s, hM3fp, hM3w⟩ := mem_after v hM2s (by decide) hM2fp
  exact ⟨a2, _, _, _, _, _, _, _, _, _, _, hgo1.trans hgo2, by omega, hM3s, hM3fp, hM3w,
    hl2.trans hl1, hacc2, hat2⟩

/-! ## W1: a full successful run -/

/-- W1. reclaimToken(TOKEN) sent by the owner, the token answering every call with the word 1:
`processMessage` gives a frame with no error and no output; every storage word of every address
reads as before, no log is added, the token is among the accessed addresses, and the state is
the state before with the reads of the two calls recorded. -/
theorem reclaimToken_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hcode : S.getCode (S.getAccount TOKEN).codeHash = .ok ONE_CODE)
    {G : Nat} (hG : 2000000 ≤ G) (hG64 : G < 2 ^ 64) :
    RunsOk fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss
      (callSt (callSt S C TOKEN) C TOKEN) TOKEN := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  obtain ⟨a2, ss2, x1, x2, x3, bal, owner, t2, tk, sel, mem, hgo, hg2, hms, hfp, hw, hlogs,
      hacc, hat⟩ :=
    tiny_two_calls (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (tok := (0x1000 : U256)) rfl tok_m tok_m2 rfl (owner_yes h5) 0x01 tinyOut_one hcode
      (fun _ => delegatedAddress_one) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) hG (Nat.le_refl _) hG64 hstart
  obtain ⟨s, hr, hrun, herr, hout, hst, hsub⟩ :=
    seg3_ok (Nat.le_trans (by decide) hparis) hms hfp hw
      (by rw [size_wordBytes]; decide) (by decide) hg2 hat
  refine ok_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (hgo.trans (Goes.of_reaches _ hr)) hrun herr hout hst ?_ (by rw [hsub]; exact hlogs)
    (by rw [hsub]; exact hacc)
  intro A n
  rw [storageAt_callSt, storageAt_callSt]

theorem one_hash_ne : hashOf ONE_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

theorem zero_hash_ne : hashOf ZERO_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

theorem revert_hash_ne : hashOf REVERT_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

theorem stop_hash_ne : hashOf Payee.STOP_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

/-- Slot 5 of a `codeState` whose only word is slot 5. -/
theorem slot5_codeState (C : Address) (w : U256) (a : Address) (code : ByteArray) :
    storageAt (codeState C [((5 : U256), w)] a code) C (5 : U256) = w := by
  rw [storageAt_codeState, storageAt_sState_cons, if_pos rfl]

/-- The state of W1: the contract at `WBTC_ADDRESS` with `Witness.CALLER1` as owner, and the
token with the code that answers 1. -/
abbrev oneState : State.TransactionState :=
  codeState WBTC_ADDRESS [((5 : U256), OWNER_SLOT)] TOKEN ONE_CODE

/-- W1, closed: no hypothesis left but the fork bounds. -/
theorem reclaimToken_runs_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    RunsOk fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000) oneState ss
      (callSt (callSt oneState WBTC_ADDRESS TOKEN) WBTC_ADDRESS TOKEN) TOKEN :=
  reclaimToken_runs hparis hglam b t ss wbtc_address_word (slot5_codeState _ _ _ _)
    (getCode_codeState _ _ _ one_hash_ne) (Nat.le_refl _) (by decide)

/-! ## W2: the caller is not the owner -/

/-- W2. Another address is the owner: the call reverts with no output, the state put back. -/
theorem reclaimToken_notOwner_reverts (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OTHER_SLOT)
    {G : Nat} (hG : 8000 ≤ G) :
    RunsRevert fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss ByteArray.empty := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  have hsz := rc_size (data := (rcMsg b t C Witness.CALLER1 0x1000 G).data) rfl
  obtain ⟨s, hr, hrun, herr, hout, hst⟩ :=
    seg_notowner (Nat.le_trans (by decide) hparis) (by rw [hsz]; decide) (by rw [hsz]; decide)
      (rc_sel (data := (rcMsg b t C Witness.CALLER1 0x1000 G).data) rfl) rfl (owner_no h5) hG
      hstart
  have h := revert_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (Goes.of_reaches _ hr) hrun herr (by rw [hst]; rfl)
  rw [hout] at h
  exact h

/-- W2, closed. -/
theorem reclaimToken_notOwner_reverts_closed (hparis : .paris ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    RunsRevert fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000)
      (codeState WBTC_ADDRESS [((5 : U256), OTHER_SLOT)] TOKEN ONE_CODE) ss ByteArray.empty :=
  reclaimToken_notOwner_reverts hparis b t ss wbtc_address_word (slot5_codeState _ _ _ _)
    (by decide)

/-! ## W3: the token has no code -/

/-- W3. No code at the token: the call reverts with no output, before any call. -/
theorem reclaimToken_noCode_reverts (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hcode : S.getCode (S.getAccount TOKEN).codeHash = .ok ByteArray.empty)
    {G : Nat} (hG : 8000 ≤ G) :
    RunsRevert fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss ByteArray.empty := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  have hsz := rc_size (data := (rcMsg b t C Witness.CALLER1 0x1000 G).data) rfl
  have hA := rc_tokA (data := (rcMsg b t C Witness.CALLER1 0x1000 G).data) rfl tok_m
  obtain ⟨s, hr, hrun, herr, hout, hst⟩ :=
    seg_nocode (Nat.le_trans (by decide) hparis) hglam (by rw [hsz]; decide)
      (by rw [hsz]; decide) (rc_sel (data := (rcMsg b t C Witness.CALLER1 0x1000 G).data) rfl)
      rfl (owner_yes h5) (by rw [hA]; exact hcode) (by decide) hG hstart
  have h := revert_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (Goes.of_reaches _ hr) hrun herr (by rw [hst]; rfl)
  rw [hout] at h
  exact h

/-- In `sState C kvs` an address other than `C` has no code. -/
theorem getCode_sState_other {C a : Address} (kvs : List (U256 × U256)) (hne : C ≠ a) :
    (sState C kvs).getCode ((sState C kvs).getAccount a).codeHash = .ok ByteArray.empty := by
  have hO : (sState C kvs).getAccount a = State.EMPTY_ACCOUNT := by
    unfold State.TransactionState.getAccount
    have hnone : (sState C kvs).getAccountOptional a = none := by
      simp [sState, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
        State.State.getAccountOptional, Std.ExtTreeMap.getElem?_insert, hne]
    rw [hnone] <;> rfl
  rw [hO]
  simp [State.TransactionState.getCode, State.EMPTY_ACCOUNT]

/-- W3, closed: the state has no account at the token. -/
theorem reclaimToken_noCode_reverts_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    RunsRevert fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000)
      (sState WBTC_ADDRESS [((5 : U256), OWNER_SLOT)]) ss ByteArray.empty :=
  reclaimToken_noCode_reverts hparis hglam b t ss wbtc_address_word
    (by rw [storageAt_sState_cons, if_pos rfl]) (getCode_sState_other _ wbtc_ne_token)
    (by decide)

/-! ## W4: the token reverts on balanceOf -/

/-- W4. The token reverts every call with the word 42 as data: reclaimToken reverts, and its
output is exactly the 32 bytes of the revert data of the token. -/
theorem reclaimToken_calleeReverts (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hcode : S.getCode (S.getAccount TOKEN).codeHash = .ok REVERT_CODE)
    {G : Nat} (hG : 2000000 ≤ G) (hG64 : G < 2 ^ 64) :
    RunsRevert fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss (wordBytes 42) := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, m_code, m_target, -, -, m_np, m_val, -, -, -, hk⟩ :=
    first_call (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (tok := (0x1000 : U256)) rfl tok_m rfl (owner_yes h5) hcode (tiny_size_ne 0x2a 0xfd)
      (fun _ => delegatedAddress_revert) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) hG64 (Nat.le_refl _) hstart
  obtain ⟨child, hrun, cerr, cout, cst⟩ :=
    tiny_message_reverts hparis 0x2a (caller := caller) hlt m_code m_target m_np m_val
      (by omega)
  obtain ⟨a1, hga1, hba1, hgo1, hat1⟩ := hk hlt child hrun
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 0 := by
    rw [cerr]
    rfl
  rw [hflag, cout, tinyOut_revert, extract_word] at hat1
  have hM1s : (memoryWrite (mem1 (rcMsg b t C Witness.CALLER1 0x1000 G).currentTarget) 128
      (wordBytes 42)).size = 192 :=
    (mem_after (42 : U256) (mem1_size _) (by decide) (mem1_fp _)).1
  obtain ⟨s, hr, hrun2, herr, hout, hst, -⟩ :=
    bubble1 (Nat.le_trans (by decide) hparis) (size_wordBytes 42)
      (by rw [hM1s]; decide) (by simp) (by omega) a1 hat1
  have hread : memoryReadBytes (wordBytes 42) 0 32 = wordBytes 42 := by decide +kernel
  have h := revert_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (hgo1.trans (Goes.of_reaches _ hr)) hrun2 herr (by rw [hst, cst, parent_restoreTxState, hcst, parent_callSt])
  rw [hout, hread] at h
  exact h

/-- W4, closed. -/
theorem reclaimToken_calleeReverts_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    RunsRevert fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000)
      (codeState WBTC_ADDRESS [((5 : U256), OWNER_SLOT)] TOKEN REVERT_CODE) ss (wordBytes 42) :=
  reclaimToken_calleeReverts hparis hglam b t ss wbtc_address_word (slot5_codeState _ _ _ _)
    (getCode_codeState _ _ _ revert_hash_ne) (Nat.le_refl _) (by decide)

/-! ## W5: the token returns fewer than 32 bytes -/

/-- W5. The token holds the one byte STOP: the first call succeeds with no return data, and
reclaimToken reverts with no output. -/
theorem reclaimToken_shortReturn_reverts (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hcode : S.getCode (S.getAccount TOKEN).codeHash = .ok Payee.STOP_CODE)
    {G : Nat} (hG : 2000000 ≤ G) (hG64 : G < 2 ^ 64) :
    RunsRevert fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss ByteArray.empty := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  obtain ⟨caller, msg, hlt, hmg, hcst, hcss, m_code, m_target, -, -, m_np, m_val, -, -, -, hk⟩ :=
    first_call (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (tok := (0x1000 : U256)) rfl tok_m rfl (owner_yes h5) hcode (by decide)
      (fun _ => Payee.delegatedAddress_stop) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) (by omega) hG64 (Nat.le_refl _) hstart
  obtain ⟨child, hrun, cerr, cout, cst, css⟩ :=
    stop_message_runs hparis (caller := caller) hlt m_code m_target m_np m_val
  obtain ⟨a1, hga1, hba1, hgo1, hat1⟩ := hk hlt child hrun
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [cerr]
    rfl
  rw [hflag, cout, memoryWrite_empty_extract] at hat1
  obtain ⟨s, hr, hrun2, herr, hout, hst, -⟩ :=
    seg2_short (Nat.le_trans (by decide) hparis) (mem1_size C) (mem1_fp C) (by decide)
      (by omega) hat1
  have h := revert_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (hgo1.trans (Goes.of_reaches _ hr)) hrun2 herr (by rw [hst, cst, hcst, parent_callSt])
  rw [hout] at h
  exact h

/-- W5, closed. -/
theorem reclaimToken_shortReturn_reverts_closed (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam) (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (ss : Substate) :
    RunsRevert fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000)
      (codeState WBTC_ADDRESS [((5 : U256), OWNER_SLOT)] TOKEN Payee.STOP_CODE) ss
      ByteArray.empty :=
  reclaimToken_shortReturn_reverts hparis hglam b t ss wbtc_address_word
    (slot5_codeState _ _ _ _) (getCode_codeState _ _ _ stop_hash_ne) (Nat.le_refl _) (by decide)

/-! ## W6: the token returns the word 0 -/

/-- W6. The token answers every call with the word 0: balanceOf gives 0, transfer(owner, 0)
"returns false", and reclaimToken reverts with no output after both calls. -/
theorem reclaimToken_falseReturn_reverts (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate)
    {C : Address} (hC : C.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256))
    {S : State.TransactionState} (h5 : storageAt S C (5 : U256) = OWNER_SLOT)
    (hcode : S.getCode (S.getAccount TOKEN).codeHash = .ok ZERO_CODE)
    {G : Nat} (hG : 2000000 ≤ G) (hG64 : G < 2 ^ 64) :
    RunsRevert fork (rcMsg b t C Witness.CALLER1 0x1000 G) S ss ByteArray.empty := by
  have hstart := At.startFrame (message := rcMsg b t C Witness.CALLER1 0x1000 G) (code := CODE)
    rfl S ss
  obtain ⟨a2, ss2, x1, x2, x3, bal, owner, t2, tk, sel, mem, hgo, hg2, hms, hfp, hw, hlogs,
      hacc, hat⟩ :=
    tiny_two_calls (bound := (rcMsg b t C Witness.CALLER1 0x1000 G).gas) hparis hglam
      (tok := (0x1000 : U256)) rfl tok_m tok_m2 rfl (owner_yes h5) 0x00 tinyOut_zero hcode
      (fun _ => delegatedAddress_zero) notPrecompile_token
      (by show 0 + 1 ≤ STACK_DEPTH_LIMIT; decide) hG (Nat.le_refl _) hG64 hstart
  obtain ⟨s, hr, hrun, herr, hout, hst, hsub⟩ :=
    seg3_zero (Nat.le_trans (by decide) hparis) hms hfp hw
      (by rw [size_wordBytes]; decide) (by decide) hg2 hat
  have h := revert_of_goes hparis (noPre_of (a := C) rfl (notPrecompile_wbtc hC)) rfl
    (hgo.trans (Goes.of_reaches _ hr)) hrun herr
    (by rw [hst, parent_callSt, parent_callSt])
  rw [hout] at h
  exact h

/-- W6, closed. -/
theorem reclaimToken_falseReturn_reverts_closed (hparis : .paris ≤ fork)
    (hglam : fork < .glamsterdam) (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (ss : Substate) :
    RunsRevert fork (rcMsg b t WBTC_ADDRESS Witness.CALLER1 0x1000 2000000)
      (codeState WBTC_ADDRESS [((5 : U256), OWNER_SLOT)] TOKEN ZERO_CODE) ss ByteArray.empty :=
  reclaimToken_falseReturn_reverts hparis hglam b t ss wbtc_address_word
    (slot5_codeState _ _ _ _) (getCode_codeState _ _ _ zero_hash_ne) (Nat.le_refl _) (by decide)

/-! ## The assumption on the callee is satisfiable -/

/-- Every frame with no error that the real runner gives, from Paris, for a message with no value
to a token (no precompile) whose code is a `tinyCode b` that returns: it has the state of the
caller, so every storage word of every address (of WBTC too) is as it was. For any gas, any call
data and any frame `caller`. -/
theorem tiny_token_keeps (hparis : .paris ≤ fork) (b : UInt8) {caller child : Evm fork Nat}
    {msg : Message fork} {tok : Address}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = tinyCode b 0xf3) (htarget : msg.target = some tok)
    (hca : msg.codeAddress = some tok)
    (hnp : Precompiles.isPrecompile fork tok.toU256.toNat = false) (hv : msg.value = 0)
    (herr : child.error = none) :
    child.state = caller.state ∧
      ∀ (C : Address) (n : U256), storageAt child.state C n = storageAt caller.state C n := by
  have h := (tiny_child_keeps hparis b hran hcode htarget (noPre_of hca hnp) hv herr).1
  exact ⟨h, fun C n => by rw [h]⟩

/-- The message that a CALL of reclaimToken sends to the token of W1 does run under the real
runner: for every frame `caller` (so also from a state where WBTC holds its code), a message with
no value to `TOKEN` with the code `ONE_CODE`, any data (the 36 bytes of balanceOf(this), the 68
bytes of transfer(owner, 1)) and at least 18 gas gives a frame with no error, the word 1 as
output, and the state of the caller: every storage word of WBTC is as it was. -/
theorem one_token_call_runs (hparis : .paris ≤ fork) {caller : Evm fork Nat}
    {msg : Message fork} (lt : msg.gas < bound) (hcode : msg.code = ONE_CODE)
    (htarget : msg.target = some TOKEN) (hca : msg.codeAddress = some TOKEN)
    (hv : msg.value = 0) (hg : 18 ≤ msg.gas) :
    ∃ child, processRunner (Meter := Nat) fork bound caller msg lt = .ok child ∧
      child.1.error = none ∧ child.1.output = wordBytes 1 ∧ child.1.state = caller.state ∧
      ∀ (C : Address) (n : U256), storageAt child.1.state C n = storageAt caller.state C n := by
  obtain ⟨child, hrun, cerr, cout, cst, -⟩ :=
    tiny_message_runs hparis 0x01 (caller := caller) lt hcode htarget
      (noPre_of hca notPrecompile_token) hv hg
  exact ⟨child, hrun, cerr, by rw [cout, tinyOut_one], cst, fun C n => by rw [cst]⟩

end WbtcVerify.Sanity

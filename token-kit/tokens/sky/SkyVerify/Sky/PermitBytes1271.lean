import SkyVerify.Sky.Permit1271

/-!
# SKY: the ERC-1271 path of `permit(owner, spender, value, deadline, bytes signature)`

Hand-written, after Sky/Permit1271.lean. The function with a signature as bytes (selector
`0x9fd5a6cf`) reaches the code of `permit(v, r, s)` with another end of the stack (it returns to
558, not to 3182) and, for a signature of 65 bytes, with a free memory pointer 31 bytes higher:
the layouts C (the chain id is 1, free memory pointer 610 at the call of ECRECOVER) and D (else,
930). The theorems here are those of Sky/Permit1271.lean for that stack and these layouts, over
the generated segments `permitCodeC/D`, `permitCopyC/D`, `permitAnswerC/D`, `permitEmptyC/D`.

No assumption is made on the code of the owner (`staticcall_kept`).
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}

/-- From 3725, after the copy of the return data, when the size of the return data (as a word)
is not 32: the size check fails (or the flag is 0), so no run ends with no error. -/
theorem permitBytes_wrong_size (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B : Nat}
    {N Xw flag dg owner nonce deadline value spender sel : U256}
    {m rd : ByteArray} {st : State.TransactionState} {ss : Substate}
    (h : RunsTo runChild s CODE message B 3725
      [N, Xw, flag, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] m st ss rd)
    (hwX : loadWord (memoryReadBytes m Xw.toNat 32) 0 32 = N) (hfit : Xw.toNat + 32 ≤ m.size)
    (hN : N ≠ 32) (hflag : flag = 0 ∨ flag = 1) (hok : s.error = none) : False := by
  ls 3728 (lpush 2 3734)
  ls 3734 ljump
  ls 3735 ljumpdest
  ls 3736 lpop
  ls 3737 (lswap 1)
  ls 3738 lpop
  ls 3739 (lswap 1)
  ls 3740 lpop
  ls 3741 (ldup 1)
  ls 3742 (ldup 0)
  ls 3743 (lun 0x15 instruction_iszero)
  ls 3746 (lpush 2 3753)
  rcases hflag with rfl | rfl
  · ls 3753 (ljumpi (by decide))
    exact permit_fail_tail hfork (by simp) h hok
  · ls 3747 (ljumpi0 (by decide))
    ls 3748 lpop
    ls 3749 (ldup 0)
    ls 3750 (mloadInG rfl hfit (by code_fact) (by code_fact) hG)
    rw [hwX] at h
    ls 3752 (lpush 1 32)
    ls 3753 (lbin 0x14 instruction_eq)
    have hc : equal (32 : U256) N = 0 := if_neg (fun e => hN e.symm)
    rw [hc] at h
    exact permit_fail_tail hfork (by simp) h hok

/-- From 3683, after the STATICCALL to the owner, to the checks of the answer: a run that ends
with no error had no return data (then it is at 3729), or return data of size 32 as a word
(then it is at 3725, the return data copied to the memory at the free memory pointer). -/
theorem permitBytes_after_call (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B sz : Nat}
    {Xw flag c ow dg owner nonce deadline value spender sel : U256}
    {M out : ByteArray} {st : State.TransactionState} {ss : Substate}
    (hs : M.size = sz) (hmod : sz % 32 = 0) (h128 : 128 ≤ Xw.toNat) (hXf : Xw.toNat + 64 ≤ sz)
    (hX32 : (add Xw (32 : U256)).toNat = Xw.toNat + 32)
    (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = Xw)
    (hflag : flag = 0 ∨ flag = 1)
    (h : RunsTo runChild s CODE message B 3683
      [flag, c, ow, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] M st ss out)
    (hok : s.error = none) :
    (BitVec.ofNat 256 out.size = 0 ∧ ∃ (g : Nat) (l : Evm fork Nat), g ≤ B ∧
      At CODE message 3729
        [(0 : U256), (0 : U256), flag, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg,
          owner, (2739 : U256), dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel]
        M g st ss l ∧ EndsL runChild l s) ∨
    (BitVec.ofNat 256 out.size = 32 ∧ ∃ (M' : ByteArray) (g : Nat) (l : Evm fork Nat), g ≤ B ∧
      M'.size = sz ∧
      loadWord (memoryReadBytes M' 64 32) 0 32 =
        add Xw (bitwiseAnd (add (32 : U256) (63 : U256)) (bitwiseNot (31 : U256))) ∧
      loadWord (memoryReadBytes M' 96 32) 0 32 = loadWord (memoryReadBytes M 96 32) 0 32 ∧
      loadWord (memoryReadBytes M' Xw.toNat 32) 0 32 = (32 : U256) ∧
      loadWord (memoryReadBytes M' (Xw.toNat + 32) 32) 0 32 =
        loadWord (memoryReadBytes out 0 32) 0 32 ∧
      At CODE message 3725
        [(32 : U256), Xw, flag, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg,
          owner, (2739 : U256), dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel]
        M' g st ss l ∧ EndsL runChild l s) := by
  obtain ⟨N, hN⟩ : ∃ N : U256, BitVec.ofNat 256 out.size = N := ⟨_, rfl⟩
  have hNle : N.toNat ≤ out.size := by
    rw [← hN, BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  rw [hN]
  ls 3684 (lswap 1)
  ls 3685 lpop
  ls 3686 lpop
  ls 3687 lrds
  rw [hN] at h
  ls 3688 (ldup 0)
  ls 3690 (lpush 1 0)
  ls 3691 (ldup 1)
  ls 3692 (lbin 0x14 instruction_eq)
  ls 3695 (lpush 2 3729)
  by_cases h0 : N = 0
  · subst h0
    ls 3729 (ljumpi (by decide))
    exact .inl ⟨rfl, h.to_at⟩
  · have hc : equal N (0 : U256) = 0 := if_neg h0
    ls 3696 (ljumpi0 hc)
    ls 3698 (lpush 1 64)
    ls 3699 (mloadInG hs (by show 64 + 32 ≤ sz; omega) (by code_fact) (by code_fact) hG)
    rw [show loadWord (memoryReadBytes M (64 : U256).toNat 32) 0 32 = Xw from hfp] at h
    ls 3700 (lswap 1)
    ls 3701 lpop
    ls 3703 (lpush 1 31)
    ls 3704 (lun 0x19 (instruction_of_stackOnlyStep rfl))
    ls 3706 (lpush 1 63)
    ls 3707 lrds
    rw [hN] at h
    ls 3708 (lbin 0x01 instruction_add)
    ls 3709 (lbin 0x16 (instruction_of_stackOnlyStep rfl))
    ls 3710 (ldup 2)
    ls 3711 (lbin 0x01 instruction_add)
    ls 3713 (lpush 1 64)
    ls 3714 (mstoreInG hs (by show 64 + 32 ≤ sz; omega) (by code_fact) (by code_fact) hG)
    ls 3715 lrds
    rw [hN] at h
    ls 3716 (ldup 2)
    ls 3717 (mstoreInG (size_rawW hs (by show 64 + 32 ≤ sz + 0; omega)) (by omega)
      (by code_fact) (by code_fact) hG)
    ls 3718 lrds
    rw [hN] at h
    ls 3720 (lpush 1 0)
    ls 3722 (lpush 1 32)
    ls 3723 (ldup 4)
    ls 3724 (lbin 0x01 instruction_add)
    ls 3725 (returndatacopyG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact)
      (by show 0 + N.toNat ≤ out.size; omega) hG)
    have f64 : (64 : U256).toNat + 32 ≤ sz + 0 := by show 64 + 32 ≤ sz + 0; omega
    have fX : Xw.toNat + 32 ≤ sz + 0 + 0 := by omega
    by_cases h32 : N = 32
    · subst h32
      have hNle' : 32 ≤ out.size := hNle
      obtain ⟨g, l, hB, hat, e⟩ := h.to_at
      refine .inr ⟨rfl, _, g, l, hB, ?_, ?_, ?_, ?_, ?_, hat, e⟩
      · exact size_copied (size_rawW (size_rawW hs f64) fX)
          (by rw [hX32]; show Xw.toNat + 32 + 32 ≤ sz + 0 + 0; omega) hNle
      · exact load_copied (load_rawW (load_rawW_self hs f64) (size_rawW hs f64) fX
          (by show 64 + 32 ≤ sz + 0; omega) (.inl (by show 64 + 32 ≤ Xw.toNat; omega)))
          (size_rawW (size_rawW hs f64) fX) hmod (by omega) (by rw [hX32]; omega)
          (by decide) hNle
      · exact load_copied (load_rawW (load_rawW rfl hs f64 (by omega)
          (.inr (by show 64 + 32 ≤ 96; omega))) (size_rawW hs f64) fX (by omega)
          (.inl (by omega))) (size_rawW (size_rawW hs f64) fX) hmod (by omega)
          (by rw [hX32]; omega) (by decide) hNle
      · exact load_copied (load_rawW_self (size_rawW hs f64) fX)
          (size_rawW (size_rawW hs f64) fX) hmod (by omega) (by rw [hX32]; omega)
          (by decide) hNle
      · rw [← hX32]
        exact load_copied_word (size_rawW (size_rawW hs f64) fX) (by rw [hX32]; omega) hNle'
    · exfalso
      exact permitBytes_wrong_size hfork h
        (load_copied (load_rawW_self (size_rawW hs f64) fX)
          (size_rawW (size_rawW hs f64) fX) hmod (by omega) (by rw [hX32]; omega) h0 hNle)
        (Nat.le_trans (by omega) (size_copied_ge (size_rawW (size_rawW hs f64) fX) hmod h0
          hNle))
        h32 hflag hok

/-- `PermitWrites` with `k` more gas at the start and `k` more gas used: the same end. The last
part of `permit` costs 23 gas less from the entry with a signature as bytes (fewer words to
pop), so its facts are restated with the gas constants of `PermitEnd` and `PermitByContract`. -/
theorem permitWrites_shift {st : State.TransactionState} {ss : Substate} {g c c' k : Nat}
    {s : Evm fork Nat} {owner spender value : U256} (hc : c' = c + k)
    (h : PermitWrites fork message st ss g c s owner spender value) :
    PermitWrites fork message st ss (g + k) c' s owner spender value := by
  subst hc
  unfold PermitWrites at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, by omega, h4, by rw [h5]; omega, h6, h7⟩

/-- Layout C (free memory pointer 610 at the call of ECRECOVER): from the GAS before the
STATICCALL to the owner to the end. -/
theorem permit_call_C (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {st0 : State.TransactionState} {ss0 : Substate} {g3 : Nat} {z3 s : Evm fork Nat}
    {ow dg owner nonce deadline value spender sel : U256} {Mc D : ByteArray}
    (n0 : Mc.size = 1088) (n64 : loadWord (memoryReadBytes Mc 64 32) 0 32 = (838 : U256))
    (n96 : loadWord (memoryReadBytes Mc 96 32) 0 32 = (0 : U256))
    (nd : memoryReadBytes Mc 838 196 = D)
    (hz3 : At CODE message 3681
      [ow, (838 : U256), (196 : U256), (838 : U256), (0 : U256), (1034 : U256), ow, (0 : U256),
        (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] Mc g3 st0 ss0 z3)
    (hend3 : EndsL (processRunner fork bound) z3 s) (hok : s.error = none) :
    ∃ (out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
      OwnerCall fork bound message st0 ss0 (g3 - 2) ow D out ∧
      BitVec.ofNat 256 out.size = 32 ∧
      loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
      State.TransactionState.SameOutside [] st0 st ∧ st.parent = st0.parent ∧
      ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
      ss.refundCounter = ss0.refundCounter ∧ g ≤ g3 - 2 ∧
      PermitWrites fork message st ss g 2324 s owner spender value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨w3, hrun3⟩ := hend3
  rcases gas_outcome (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz3 w3 hrun3 with
    herr | ⟨z4, hz4, w4, hrun4⟩
  · exact absurd hok herr
  rcases staticcall_sent hparis hglam (by code_fact) (by code_fact) hz4.toLogic w4 hrun4 with
    herr | ⟨flag, out, g5, st, ss, z5, hflag, hat, hle, hso, hpar, hlogs, ⟨w5, hrun5⟩, hdel,
      href, hsent⟩
  · exact absurd hok herr
  rw [staticcall_mem_same out (by rw [n0]; decide)] at hat
  have h := RunsTo.of_logic hat ⟨w5, hrun5⟩
  rcases permitBytes_after_call hberlin n0 (by decide) (by decide) (by decide) (by decide) n64 hflag
      h hok with
    ⟨-, g, l, hB, hat0, e0⟩ | ⟨hN, M', g, l, hB, s0, s64, s96, sX, sX32, hat1, e1⟩
  · exact False.elim (Paths.ok_permitEmptyC_ends hberlin n0 n64 n96 hat0 e0 hok)
  · obtain ⟨hfl, hrw1, hrw2, r⟩ := Paths.ok_permitAnswerC_ends hberlin s0
      (s64.trans (by decide)) (s96.trans n96) sX sX32 hat1 e1 hok
    have e1' := word_eq_of_equal hrw1
    have e2' := word_eq_of_equal hrw2
    obtain ⟨cc, route, caller, msg, child, hcc, hroute, hsend, hran, hcerr, hcout⟩ :=
      hsent (isZero_eq_zero_iff.mp hfl)
    exact ⟨out, st, ss, g,
      ownerCall_of_sends (i := (838 : U256)) (isz := (196 : U256))
        (by rw [n0]; decide) nd hcc hroute hsend hran hcerr hcout, hN,
      e1'.trans ((BitVec.and_comm _ _).trans e2'), hso, hpar, hlogs, hdel, href, by omega, r⟩

/-- Layout C: from the EXTCODESIZE of the owner to the end. `PermitByContract` is stated from
`gas + 23`: it counts 2347 gas for the last part, and this entry uses 2324 there, so the end
gas is exact from a gas that is 23 higher (`permitWrites_shift`). Its `k` is so 1315 (1292 and
23): the gas left at the STATICCALL is `gas - (the access cost + 1292)`. -/
theorem permit_contract_C (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {z s : Evm fork Nat}
    {dg owner nonce deadline value spender sS sR sel vw : U256} {M : ByteArray}
    (pm : PermitMem M 768 (610 : U256) sR sS vw)
    (hz : At CODE message 3580
      [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] M gas state substate z)
    (hend : EndsL (processRunner fork bound) z s) (hok : s.error = none) :
    PermitByContract fork bound message state substate (gas + 23) s 1315 dg sR sS vw owner
      spender value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨within, hrun⟩ := hend
  rcases extcodesize_outcome hberlin (by code_fact) (by code_fact) hz within hrun with
    herr | ⟨c, z1, hcode, hg1, hz1, w1, hrun1⟩
  · exact absurd hok herr
  obtain ⟨hcs, hg2, z2, hz2, hend2⟩ := Paths.ok_permitCodeC_ends hberlin pm.size pm.fp pm.w96
    pm.w128 pm.w160 pm.w192 pm.top hz1 ⟨w1, hrun1⟩ hok
  obtain ⟨m0, m64, m96, -, -, -, m579, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCodeC_p0_mem (cs := BitVec.ofNat 256 c.size) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sel := sel) (vw := vw) pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 pm.top
  obtain ⟨hg3, z3, hz3, hend3⟩ :=
    Paths.ok_permitCopyC_ends hberlin m0 m64 m96 m579 hz2 hend2 hok
  obtain ⟨n0, n64, n96, -, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCopyC_p0_mem (ow := bitwiseAnd ADDR_MASK owner) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sel := sel) m0 m64 m96 m579
  have cd := code_data (F := 610) (dg := dg) (sR := sR) (sS := sS) (vw := vw)
    (fpn := (838 : U256)) pm.size pm.top (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl
  have cp := copy_data (S := 642) (G := 838) cd.1 rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
  rw [show bitwiseAnd ADDR_MASK owner = bitwiseAnd owner ADDR_MASK from BitVec.and_comm _ _]
    at hz3
  obtain ⟨out, st, ss, g, hcall, hN, hmagic, hso, hpar, hlogs, hdel, href, hg, r⟩ :=
    permit_call_C hparis hglam n0 n64 n96 (cp.2.trans cd.2) hz3 hend3 hok
  have eg : gas - externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
      substate.accessedAddresses)) - 626 - 664 - 2 =
      gas + 23 - (externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
        substate.accessedAddresses)) + 1315) := by omega
  rw [eg] at hcall
  exact ⟨c, out, st, ss, g + 23, hcode, isZero_eq_zero_iff.mp hcs, hcall, hN, hmagic, hso, hpar,
    hlogs, hdel, href, by omega, permitWrites_shift (c := 2324) (by omega) r⟩

/-- Layout D (free memory pointer 930 at the call of ECRECOVER): from the GAS before the
STATICCALL to the owner to the end. -/
theorem permit_call_D (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {st0 : State.TransactionState} {ss0 : Substate} {g3 : Nat} {z3 s : Evm fork Nat}
    {ow dg owner nonce deadline value spender sel : U256} {Mc D : ByteArray}
    (n0 : Mc.size = 1408) (n64 : loadWord (memoryReadBytes Mc 64 32) 0 32 = (1158 : U256))
    (n96 : loadWord (memoryReadBytes Mc 96 32) 0 32 = (0 : U256))
    (nd : memoryReadBytes Mc 1158 196 = D)
    (hz3 : At CODE message 3681
      [ow, (1158 : U256), (196 : U256), (1158 : U256), (0 : U256), (1354 : U256), ow, (0 : U256),
        (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] Mc g3 st0 ss0 z3)
    (hend3 : EndsL (processRunner fork bound) z3 s) (hok : s.error = none) :
    ∃ (out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
      OwnerCall fork bound message st0 ss0 (g3 - 2) ow D out ∧
      BitVec.ofNat 256 out.size = 32 ∧
      loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
      State.TransactionState.SameOutside [] st0 st ∧ st.parent = st0.parent ∧
      ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
      ss.refundCounter = ss0.refundCounter ∧ g ≤ g3 - 2 ∧
      PermitWrites fork message st ss g 2324 s owner spender value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨w3, hrun3⟩ := hend3
  rcases gas_outcome (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz3 w3 hrun3 with
    herr | ⟨z4, hz4, w4, hrun4⟩
  · exact absurd hok herr
  rcases staticcall_sent hparis hglam (by code_fact) (by code_fact) hz4.toLogic w4 hrun4 with
    herr | ⟨flag, out, g5, st, ss, z5, hflag, hat, hle, hso, hpar, hlogs, ⟨w5, hrun5⟩, hdel,
      href, hsent⟩
  · exact absurd hok herr
  rw [staticcall_mem_same out (by rw [n0]; decide)] at hat
  have h := RunsTo.of_logic hat ⟨w5, hrun5⟩
  rcases permitBytes_after_call hberlin n0 (by decide) (by decide) (by decide) (by decide) n64 hflag
      h hok with
    ⟨-, g, l, hB, hat0, e0⟩ | ⟨hN, M', g, l, hB, s0, s64, s96, sX, sX32, hat1, e1⟩
  · exact False.elim (Paths.ok_permitEmptyD_ends hberlin n0 n64 n96 hat0 e0 hok)
  · obtain ⟨hfl, hrw1, hrw2, r⟩ := Paths.ok_permitAnswerD_ends hberlin s0
      (s64.trans (by decide)) (s96.trans n96) sX sX32 hat1 e1 hok
    have e1' := word_eq_of_equal hrw1
    have e2' := word_eq_of_equal hrw2
    obtain ⟨cc, route, caller, msg, child, hcc, hroute, hsend, hran, hcerr, hcout⟩ :=
      hsent (isZero_eq_zero_iff.mp hfl)
    exact ⟨out, st, ss, g,
      ownerCall_of_sends (i := (1158 : U256)) (isz := (196 : U256))
        (by rw [n0]; decide) nd hcc hroute hsend hran hcerr hcout, hN,
      e1'.trans ((BitVec.and_comm _ _).trans e2'), hso, hpar, hlogs, hdel, href, by omega, r⟩

/-- Layout D: from the EXTCODESIZE of the owner to the end. `PermitByContract` is stated from
`gas + 23`: it counts 2347 gas for the last part, and this entry uses 2324 there, so the end
gas is exact from a gas that is 23 higher (`permitWrites_shift`). Its `k` is so 1315 (1292 and
23): the gas left at the STATICCALL is `gas - (the access cost + 1292)`. -/
theorem permit_contract_D (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {z s : Evm fork Nat}
    {dg owner nonce deadline value spender sS sR sel vw : U256} {M : ByteArray}
    (pm : PermitMem M 1088 (930 : U256) sR sS vw)
    (hz : At CODE message 3580
      [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (558 : U256), sel] M gas state substate z)
    (hend : EndsL (processRunner fork bound) z s) (hok : s.error = none) :
    PermitByContract fork bound message state substate (gas + 23) s 1315 dg sR sS vw owner
      spender value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨within, hrun⟩ := hend
  rcases extcodesize_outcome hberlin (by code_fact) (by code_fact) hz within hrun with
    herr | ⟨c, z1, hcode, hg1, hz1, w1, hrun1⟩
  · exact absurd hok herr
  obtain ⟨hcs, hg2, z2, hz2, hend2⟩ := Paths.ok_permitCodeD_ends hberlin pm.size pm.fp pm.w96
    pm.w128 pm.w160 pm.w192 pm.top hz1 ⟨w1, hrun1⟩ hok
  obtain ⟨m0, m64, m96, -, -, -, m579, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCodeD_p0_mem (cs := BitVec.ofNat 256 c.size) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sel := sel) (vw := vw) pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 pm.top
  obtain ⟨hg3, z3, hz3, hend3⟩ :=
    Paths.ok_permitCopyD_ends hberlin m0 m64 m96 m579 hz2 hend2 hok
  obtain ⟨n0, n64, n96, -, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCopyD_p0_mem (ow := bitwiseAnd ADDR_MASK owner) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sel := sel) m0 m64 m96 m579
  have cd := code_data (F := 930) (dg := dg) (sR := sR) (sS := sS) (vw := vw)
    (fpn := (1158 : U256)) pm.size pm.top (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl
  have cp := copy_data (S := 962) (G := 1158) cd.1 rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
  rw [show bitwiseAnd ADDR_MASK owner = bitwiseAnd owner ADDR_MASK from BitVec.and_comm _ _]
    at hz3
  obtain ⟨out, st, ss, g, hcall, hN, hmagic, hso, hpar, hlogs, hdel, href, hg, r⟩ :=
    permit_call_D hparis hglam n0 n64 n96 (cp.2.trans cd.2) hz3 hend3 hok
  have eg : gas - externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
      substate.accessedAddresses)) - 626 - 664 - 2 =
      gas + 23 - (externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
        substate.accessedAddresses)) + 1315) := by omega
  rw [eg] at hcall
  exact ⟨c, out, st, ss, g + 23, hcode, isZero_eq_zero_iff.mp hcs, hcall, hN, hmagic, hso, hpar,
    hlogs, hdel, href, by omega, permitWrites_shift (c := 2324) (by omega) r⟩

end SkyVerify

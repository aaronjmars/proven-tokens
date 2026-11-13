import LinkVerify.Link.Tac
import LinkVerify.Link.CallIn
import LinkVerify.Link.Invariant
import LinkVerify.Link.Hold

/-!
# transferAndCall, the whole function with its CALL

Written by hand (not generated). The triples of `LinkVerify.Tac` stop at the CALL opcode (pc 3088)
and start again after it (pc 3089). Here they are joined through the CALL, for every message
runner, with `callIn_outcome` (the outcome of a CALL of 0 wei with its input inside the memory).

- `tac_to_ne`: at the CALL the recipient is not the token (the code tested it).
- `inv_tacDoneSt`, `inv_tacCallSt`: the two writes of the token move keep the sum of the balances.
- `holdsCode_tacCallSt`: they keep the code of every account.
- `tac_after_fail_any`: after the CALL, with flag 0, the function REVERTs, for every memory.
- `ok_tac_whole`: every run from 530 that ends with no error, with the message of the CALL
  stated exactly (`SentIn`): gas, caller, target, value 0, call data. `hdel`: the recipient is no
  EIP-7702 delegated account (the exact gas of the CALL is stated for that case only).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit TokenKit.Complete
open LinkVerify LinkVerify.Paths LinkVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork} {sel : U256} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The word of the recipient on the stack at the CALL. -/
abbrev tacToW (message : Message fork) : U256 :=
  bitwiseAnd (tacTo message) (1461501637330902918203684832716283019655932542975 : U256)

/-- Two words with the same address have the same low 160 bits. -/
theorem mask_eq_of_address {a b : U256} (h : toAddressMasked a = toAddressMasked b) :
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) a =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) b := by
  have hm : ∀ w : U256,
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat =
        w.toNat % 2 ^ 160 := by
    intro w
    simp only [bitwiseAnd, BitVec.toNat_and]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 160
  apply BitVec.eq_of_toNat_eq
  rw [hm, hm, ← EthLib.Base.toNat_toU256_toAddressMasked,
    ← EthLib.Base.toNat_toU256_toAddressMasked, h]

/-- At the CALL the recipient is not the token itself. -/
theorem tac_to_ne (h2 : TacToOther message) :
    toAddressMasked (tacToW message) ≠ message.currentTarget := by
  intro e
  have e' : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (tacTo message) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        message.currentTarget.toU256 := by
    apply mask_eq_of_address
    rw [EthLib.Base.toAddressMasked_toU256, ← e, tacToW, toAddressMasked_mask']
  unfold TacToOther at h2
  rw [e'] at h2
  have a := isZero_ne_zero_iff.mp h2
  have b := isZero_eq_zero_iff.mp a
  have c := isZero_ne_zero_iff.mp b
  exact (equal_ne_zero_iff.mpr rfl) c

/-- The state at the CALL is the state of the token move with one more recorded read. -/
theorem tacCallSt_rar (message : Message fork) (state : State.TransactionState) :
    tacCallSt message state =
      (tacDoneSt message state).recordAccountRead (toAddressMasked (tacToW message)) := rfl

/-- At the CALL the state gives the code that the test of the recipient saw. -/
theorem tac_code_at_call {c : ByteArray} (hcode : TacCode message state c) (h5 : TacHasCode c) :
    (tacCallSt message state).getCode ((tacCallSt message state).getAccount
      (toAddressMasked (tacToW message))).codeHash = .ok c := by
  rw [tacCallSt_rar, getCode_rar, getAccount_rar]
  exact (tac_second_check hcode h5).1

/-- The token move of `transferAndCall` keeps the sum of the balances (no code at the
recipient). -/
theorem inv_tacDoneSt (hsep : Sep (callKeys message))
    (hacc : hasAccount state message.currentTarget)
    (h3 : TacFunded message state) (h4 : TacFits message state)
    (hinv : Inv message.currentTarget state) :
    Inv message.currentTarget (tacDoneSt message state) := by
  unfold TacFunded at h3
  unfold TacFits at h4
  unfold tacDoneSt tac_noneSt
  simp only [tacTo, tacValue, and_mask_comm, mask_idem] at *
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have f4 := Supply.sub_fact_gt1 h3
  have f5 := Supply.add_fact_ltc h4
  unfold Inv at hinv ⊢
  simp (disch := supply_side) only
    [Supply.sumBal_recordAccountRead, Supply.sumBal_read, S_bal hsep, storageAt_readSlot]
  omega

/-- The token move of `transferAndCall` keeps the sum of the balances (the state at the CALL). -/
theorem inv_tacCallSt (hsep : Sep (callKeys message))
    (hacc : hasAccount state message.currentTarget)
    (h3 : TacFunded message state) (h4 : TacFits message state)
    (hinv : Inv message.currentTarget state) :
    Inv message.currentTarget (tacCallSt message state) := by
  unfold TacFunded at h3
  unfold TacFits at h4
  unfold tacCallSt tac_callSt
  simp only [tacTo, tacValue, and_mask_comm, mask_idem] at *
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have f4 := Supply.sub_fact_gt1 h3
  have f5 := Supply.add_fact_ltc h4
  unfold Inv at hinv ⊢
  simp (disch := supply_side) only
    [Supply.sumBal_recordAccountRead, Supply.sumBal_read, S_bal hsep, storageAt_readSlot]
  omega

/-- The token move keeps the code of every account. -/
theorem holdsCode_tacCallSt {L : Address} {code : ByteArray}
    (h : Reenter.HoldsCode L code state) : Reenter.HoldsCode L code (tacCallSt message state) := by
  unfold tacCallSt tac_callSt
  repeat (first
    | exact h
    | refine Reenter.holdsCode_recordAccountRead _ ?_
    | refine Reenter.holdsCode_writeSlot _ _ _ ?_
    | refine Reenter.holdsCode_readSlot _ _ ?_)

/-- After the CALL, the flag is zero: REVERT with no data, for every memory. -/
theorem tac_after_fail_any (hfork : .berlin ≤ fork) {mem : ByteArray}
    {st : State.TransactionState} {ss : Substate} {g : Nat} (hg : af_failCost ≤ g) :
    Logic.SpecG fork (At CODE message 3089 ((0 : U256) :: tacRest message sel) mem g st ss)
      (Halted true ByteArray.empty (g - af_failCost) st ss) :=
  af_fail (F := tacF message) (W := tacW message) hfork (by decide) hg

/-- No run from the frame after a CALL that gave the flag 0 ends with no error. -/
theorem no_ok_after_fail (hfork : .berlin ≤ fork) {mem : ByteArray}
    {st : State.TransactionState} {ss : Substate} {g : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 3089 ((0 : U256) :: tacRest message sel) mem g st ss evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) : False :=
  Complete.no_okLE (B := af_failCost) (fun _ hg => tac_after_fail_any hfork hg)
    (fun _ e h => reverted_error e h) start hrun hok

/-- The state of a frame that takes in a child with no error is the state of the child. -/
theorem state_incorporate_ok {caller child : Evm fork Nat} (herr : child.error = none) :
    (incorporateChild fork caller child).state = child.state := by
  simp [incorporateChild, herr]

/-- Every run of `transferAndCall` from 530 that ends with no error, with the CALL. The recipient
is set and is not the token, the amount is covered and the sum fits; the output is `true`. With
no code at the recipient: the state and the substate of the token move, exact gas. With code: the
CALL sent exactly one message, described by `SentIn` (to the recipient, from the token, value 0,
the call data `tacCallData`, the gas of the 63/64 rule on `tacAsked`), the message ended with no
error, and the end state is the state its run left. -/
theorem ok_tac_whole (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hN : tacN message < 2 ^ 64)
    (hdel : ∀ c, TacCode message state c → .pectra ≤ fork → delegatedAddress c = none)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    TacToSet message ∧ TacToOther message ∧ TacFunded message state ∧ TacFits message state ∧
    s.running = false ∧ s.output = wordBytes (1 : U256) ∧
    ∃ c : ByteArray, TacCode message state c ∧
      ((TacNoCode c ∧ tacDoneGas fork message state substate ≤ gas ∧
          s.gas = gas - tacDoneGas fork message state substate ∧
          s.state = tacDoneSt message state ∧
          s.substate = tacDoneSs fork message state substate) ∨
       (TacHasCode c ∧ tacCallGas fork message state substate + 5 ≤ gas ∧
          ∃ (caller : Evm fork Nat) (msg : Message fork) (child : Evm fork Nat),
            Ran runChild caller msg child ∧ child.error = none ∧ child.gas ≤ msg.gas ∧
            SentIn message (gas - (tacCallGas fork message state substate + 5))
              (tacCallSt message state) (tacCallSs fork message state substate)
              (tacAsked fork message state substate gas) (tacToW message)
              (tacCallData message) c caller msg ∧
            s.gas = gas - (tacCallGas fork message state substate + 5) -
              (callGas fork (tacCallSt message state) (tacCallSs fork message state substate)
                (tacAsked fork message state substate gas) (tacToW message) 0
                (gas - (tacCallGas fork message state substate + 5))).cost + child.gas -
              af_okCost ∧
            s.state = child.state ∧
            s.substate = (incorporateChild fork caller child).substate)) := by
  obtain ⟨hstat, hacc, h1, h2, h3, h4, c, hcode, hcase⟩ := ok_tac_pre hfork hN start hrun hok
  rcases hcase with ⟨h5, hg, hrn, hout, hgas, hst, hss⟩ | ⟨h5, hg, z, hz, within, hzr⟩
  · exact ⟨hstat, hacc, h1, h2, h3, h4, hrn, hout, c, hcode, .inl ⟨h5, hg, hgas, hst, hss⟩⟩
  · obtain ⟨hin, hdata, -⟩ := tac_call_range (message := message) hN
    have hcode2 := tac_code_at_call hcode h5
    have hz' : At CODE message 3088
        (tacAsked fork message state substate gas :: tacToW message :: 0 ::
          tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132) ::
          tacFpw (tacLen message) :: 0 :: tacRest message sel)
        (tacMem message) (gas - (tacCallGas fork message state substate + 5))
        (tacCallSt message state) (tacCallSs fork message state substate) z := hz
    have hd : ∀ c', (tacCallSt message state).getCode ((tacCallSt message state).getAccount
          (toAddressMasked (tacToW message))).codeHash = .ok c' →
        .pectra ≤ fork → delegatedAddress c' = none := by
      intro c' hc' hp
      have e : c' = c := by
        exact Except.ok.inj (hc'.symm.trans hcode2)
      rw [e]
      exact hdel c hcode hp
    rcases callIn_outcome hfork hglam (by code_fact) (by code_fact) hin hd hz' within hzr with
      herr | ⟨mem, g, st, ss, after, hat, w', hr'⟩ |
      ⟨c', caller, msg, child, after, hc', hran, hcg, hsent, hat, w', hr'⟩
    · exact absurd hok herr
    · exact (no_ok_after_fail hfork hat ⟨w', hr'⟩ hok).elim
    · have e : c' = c := by
        exact Except.ok.inj (hc'.symm.trans hcode2)
      subst e
      cases herr : child.error with
      | some e =>
        rw [herr] at hat
        exact (no_ok_after_fail hfork hat ⟨w', hr'⟩ hok).elim
      | none =>
        rw [herr] at hat
        obtain ⟨-, hgk, hrn, hout, hgas, hst, hss⟩ := ok_tac_post hfork hN hat ⟨w', hr'⟩ hok
        rw [hdata] at hsent
        exact ⟨hstat, hacc, h1, h2, h3, h4, hrn, hout, c', hcode, .inr ⟨h5, hg, caller, msg,
          child, hran, herr, hcg, hsent, hgas, by rw [hst, state_incorporate_ok herr], hss⟩⟩

end LinkVerify.Tac

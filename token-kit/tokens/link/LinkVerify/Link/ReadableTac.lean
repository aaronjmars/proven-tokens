import LinkVerify.Link.Readable
import LinkVerify.Link.Whole

/-!
# The readable corollary of transferAndCall

Written by hand (not generated). `Readable.lean` has the readable corollaries of the nine other
functions; this file has the one of `transferAndCall(address,uint256,bytes)`, proved from
`ok_transferAndCall` (pc 0 to 530), `ok_tac_len` (the length of the bytes) and `ok_tac_whole`
(the function with its CALL).

- `tacMid message state`: the state right after the token move (both balances written, the
  account of the recipient read once). It is `Tac.tacDoneSt message state`.
- `tacLogs message logs`: `logs` plus the two logs of the function, `Transfer(from, to, value)`
  and `Transfer(from, to, value, data)`.
- `tac_move_readable`: what the four conditions of the code say in numbers, and the storage of
  `tacMid` as a function of the start storage.
- `transferAndCall_readable`: the corollary.

Words of the call, as in `Readable.lean`: `sender` is the caller, `addrArg1` the first argument
masked to 160 bits (the recipient), `arg2` the second argument (the amount). `tacLen message` is
the length word of the `bytes` argument, `tacLog2Data message` the data of the second log and
`tacCallData message` the call data of the message to the recipient.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LinkVerify

open UsdtVerify
open TokenKit TokenKit.Complete TokenKit.Readable
open LinkVerify.Tac LinkVerify.Readable
open LinkVerify.Paths LinkVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The state right after the token move of `transferAndCall`: the two balances written and the
account of the recipient read once (the EXTCODESIZE test). -/
abbrev tacMid (message : Message fork) (state : State.TransactionState) :
    State.TransactionState :=
  tacDoneSt message state

/-- `logs` plus the two logs of `transferAndCall`, in the order the code emits them: the ERC-20
`Transfer(from, to, value)` with the amount as data, then the ERC-677
`Transfer(from, to, value, data)` with the data `tacLog2Data message`. -/
def tacLogs (message : Message fork) (logs : Array Blocks.Log) : Array Blocks.Log :=
  (logs.push (TokenKit.Readable.log3 message.currentTarget TRANSFER (sender message)
      (addrArg1 message) (wordBytes (arg2 message)))).push
    (TokenKit.Readable.log3 message.currentTarget TRANSFER_DATA (sender message)
      (addrArg1 message) (tacLog2Data message))

/-- A recorded read of an account changes no storage word. -/
theorem storageAt_rar (S : State.TransactionState) (a C : Address) (k : U256) :
    storageAt (S.recordAccountRead a) C k = storageAt S C k := rfl

/-- The logs at the end with no code at the recipient: the old logs and the two logs. -/
theorem tacDoneSs_logs :
    (tacDoneSs fork message state substate).logs = tacLogs message substate.logs := by
  have e1 : bitwiseAnd (tacTo message) (1461501637330902918203684832716283019655932542975 : U256) =
      addrArg1 message := by
    simp only [tacTo, addrArg1, and_mask_comm, mask_idem]
  have e2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (tacTo message) =
      addrArg1 message := by
    simp only [tacTo, addrArg1, mask_idem]
  rw [tacDoneSs_eq, e1, e2]
  rfl

/-- An access of an account adds no log. -/
theorem logs_accessAccount (ss : Substate) (a : Address) :
    (accessAccount ss a).logs = ss.logs := rfl

/-- The logs at the CALL: the old logs and the two logs. -/
theorem tacCallSs_logs :
    (tacCallSs fork message state substate).logs = tacLogs message substate.logs := by
  rw [tacCallSs_eq, logs_accessAccount]
  exact tacDoneSs_logs

/-- A code that fails the test `size > 0`: its size, as a word, is 0. -/
theorem size_word_of_noCode {c : ByteArray} (h : TacNoCode c) :
    (BitVec.ofNat 256 c.size : U256) = 0 := by
  have h' : ¬ 0 < (BitVec.ofNat 256 c.size).toNat := fun p => h ((tacHasCode_iff c).mpr p)
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 256 c.size).toNat = 0
  omega

/-- A code that passes the test `size > 0`: its size, as a word, is not 0. -/
theorem size_word_of_hasCode {c : ByteArray} (h : TacHasCode c) :
    (BitVec.ofNat 256 c.size : U256) ≠ 0 := by
  intro e
  have p := (tacHasCode_iff c).mp h
  rw [e] at p
  exact Nat.lt_irrefl 0 p

/-- The token move of `transferAndCall`, readable. From the four conditions of the code: the
recipient is not 0 and not the contract, the amount is covered, the balance of the recipient does
not overflow. And the storage of `tacMid`: the balances as after `transfer`, every other slot
kept. -/
theorem tac_move_readable (hsep : Sep (callKeys message))
    (hacc : hasAccount state message.currentTarget)
    (hc2 : TacToSet message) (hc3 : TacToOther message)
    (hc4 : TacFunded message state) (hc5 : TacFits message state) :
    (((addrArg1 message) ≠ 0) ∧
      ((addrArg1 message) ≠ message.currentTarget.toU256) ∧
      ((arg2 message).toNat ≤ (balance message state (sender message)).toNat) ∧
      ((addrArg1 message) ≠ (sender message) → (balance message state (addrArg1 message)).toNat + (arg2 message).toNat < 2 ^ 256)) ∧
    (((addrArg1 message) ≠ (sender message) → (balance message (tacMid message state) (sender message)).toNat = (balance message state (sender message)).toNat - (arg2 message).toNat ∧ (balance message (tacMid message state) (addrArg1 message)).toNat = (balance message state (addrArg1 message)).toNat + (arg2 message).toNat) ∧
      ((addrArg1 message) = (sender message) → balance message (tacMid message state) (sender message) = balance message state (sender message)) ∧
      (∀ k, k ≠ mapSlot (sender message) 1 → k ≠ mapSlot (addrArg1 message) 1 → storageAt (tacMid message state) message.currentTarget k = storageAt state message.currentTarget k)) := by
  unfold TacToSet at hc2
  unfold TacToOther at hc3
  unfold TacFunded at hc4
  unfold TacFits at hc5
  simp only [tacMid, tacDoneSt, tac_noneSt, storageAt_rar, balance, sender, addrArg1, arg2, tacTo, tacValue] at hc2 hc3 hc4 hc5 ⊢
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc2 hc3 hc4 hc5
  by_cases hd1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256
  · try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc2 hc3 hc4 hc5
    have v2 := Readable.ne_of_isZero0 hc2
    have e3 := Readable.ne_self_of_cond3 hc3
    have l4 := Readable.le_of_cond_gt1 hc4
    have f4 := Readable.sub_fact1 hc4
    have b5 := Readable.add_bound_ltc hc5
    have f5 := Readable.add_nat_ltc hc5
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close08)
  · have hd1' : ¬(bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)) := fun e => hd1 e.symm
    try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc2 hc3 hc4 hc5
    have v2 := Readable.ne_of_isZero0 hc2
    have e3 := Readable.ne_self_of_cond3 hc3
    have l4 := Readable.le_of_cond_gt1 hc4
    have f4 := Readable.sub_fact1 hc4
    have b5 := Readable.add_bound_ltc hc5
    have f5 := Readable.add_nat_ltc hc5
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, storageAt_rar, mask_idem, slot_bal_bal hsep, slot_allow_bal hsep, slot_bal_allow hsep, and_mask_comm, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close08)

/-- transferAndCall(to, value, data) with `from` the caller. A run of the code from pc 0 with the
selector `0x4000aea0` and less than `2 ^ 60` gas, that ends with no error, from Berlin and before
Glamsterdam. `hdel`: the recipient is no EIP-7702 delegated account.

Success needs: no value, a frame that may write, an account of the contract, `to` not 0 and not
the contract itself (validRecipient), `value <= balances[from]`, and (when `to` is not `from`)
no overflow of `balances[to]`.

Then: returns 1. In the state `tacMid message state` (right after the token move):
`balances[from]` is the old word minus `value` and `balances[to]` the old word plus `value`
(when `to = from` the balance is unchanged), every other slot keeps its word. The data of the
second log starts with the words `value`, 64 and the length of `data`.

Then one of two cases, on the code `c` that the start state gives for the recipient.
(a) The size of `c`, as a word of 256 bits, is 0: the end state is `tacMid message state` and the
logs are the old logs plus exactly two, `Transfer(from, to, value)` then
`Transfer(from, to, value, data)`.
(b) It is not 0: the code sent exactly one message `msg` to the recipient, from the frame
`caller`, and the runner ended it in the frame `child` with no error; the end state is the state
of `child`. The message goes to the recipient, from the contract, with value 0, the code `c` and
the call data `tacCallData message`: the selector `a4c0ed36` (`onTokenTransfer`), the sender,
`value`, 96 and the length of `data`. Its gas is what the 63/64 rule gives for the gas asked
(`tacAsked`: all the gas left but 710). The state of `caller` has the storage of
`tacMid message state` at every account and every slot (the callee starts with the new balances
in place), and its logs are the old logs plus the two logs. -/
theorem transferAndCall_readable (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x4000aea0)
    (hsep : Sep (callKeys message))
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked (addrArg1 message))).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas : Nat} (hgas : gas < 2 ^ 60) {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      ((addrArg1 message) ≠ 0) ∧
      ((addrArg1 message) ≠ message.currentTarget.toU256) ∧
      ((arg2 message).toNat ≤ (balance message state (sender message)).toNat) ∧
      ((addrArg1 message) ≠ (sender message) → (balance message state (addrArg1 message)).toNat + (arg2 message).toNat < 2 ^ 256)) ∧
    (s.output = wordBytes 1) ∧
    (((addrArg1 message) ≠ (sender message) → (balance message (tacMid message state) (sender message)).toNat = (balance message state (sender message)).toNat - (arg2 message).toNat ∧ (balance message (tacMid message state) (addrArg1 message)).toNat = (balance message state (addrArg1 message)).toNat + (arg2 message).toNat) ∧
      ((addrArg1 message) = (sender message) → balance message (tacMid message state) (sender message) = balance message state (sender message)) ∧
      (∀ k, k ≠ mapSlot (sender message) 1 → k ≠ mapSlot (addrArg1 message) 1 → storageAt (tacMid message state) message.currentTarget k = storageAt state message.currentTarget k)) ∧
    (loadWord (memoryReadBytes (tacLog2Data message) 0 32) 0 32 = arg2 message ∧
      loadWord (memoryReadBytes (tacLog2Data message) 32 32) 0 32 = (64 : U256) ∧
      loadWord (memoryReadBytes (tacLog2Data message) 64 32) 0 32 = tacLen message) ∧
    ∃ c : ByteArray,
      state.getCode (state.getAccount (toAddressMasked (addrArg1 message))).codeHash = .ok c ∧
      (((BitVec.ofNat 256 c.size : U256) = 0 ∧
          s.state = tacMid message state ∧
          s.substate.logs = tacLogs message substate.logs) ∨
       ((BitVec.ofNat 256 c.size : U256) ≠ 0 ∧
          ∃ (caller : Evm fork Nat) (msg : Message fork) (child : Evm fork Nat),
            Ran runChild caller msg child ∧ child.error = none ∧ s.state = child.state ∧
            msg.currentTarget = toAddressMasked (addrArg1 message) ∧
            msg.caller = message.currentTarget ∧
            msg.value = 0 ∧
            msg.code = c ∧
            msg.data = tacCallData message ∧
            (memoryReadBytes (tacCallData message) 0 4 = ⟨#[0xa4, 0xc0, 0xed, 0x36]⟩ ∧
              loadWord (memoryReadBytes (tacCallData message) 4 32) 0 32 = sender message ∧
              loadWord (memoryReadBytes (tacCallData message) 36 32) 0 32 = arg2 message ∧
              loadWord (memoryReadBytes (tacCallData message) 68 32) 0 32 = (96 : U256) ∧
              loadWord (memoryReadBytes (tacCallData message) 100 32) 0 32 = tacLen message) ∧
            msg.gas = (callGas fork (tacCallSt message state)
              (tacCallSs fork message state substate)
              (tacAsked fork message state substate (gas - 207)) (tacToW message) 0
              (gas - 207 - (tacCallGas fork message state substate + 5))).subCall ∧
            (∀ a k, storageAt caller.state a k = storageAt (tacMid message state) a k) ∧
            caller.substate.logs = tacLogs message substate.logs)) := by
  obtain ⟨hv, hcg, z, hz, hzr⟩ := ok_transferAndCall hfork hsize' hsel start hrun hok
  have hN := ok_tac_len hfork (show gas - 207 < 2 ^ 60 by omega) hz hzr hok
  obtain ⟨hstat, hacc, h1, h2, h3, h4, -, hout, c, hcode, hcase⟩ :=
    ok_tac_whole hfork hglam hN (fun c hc hp => hdel c hc hp) hz hzr hok
  obtain ⟨⟨r1, r2, r3, r4⟩, hmid⟩ := tac_move_readable hsep hacc h1 h2 h3 h4
  obtain ⟨l0, l1, l2⟩ := tac_log2_head (message := message) hN
  refine ⟨⟨Readable.value_of_cond hv, hstat, hacc, r1, r2, r3, r4⟩, hout, hmid, ⟨l0, l1, l2⟩,
    c, hcode, ?_⟩
  rcases hcase with ⟨h5, -, -, hst, hss⟩ |
    ⟨h5, -, caller, msg, child, hran, herr, -, hsent, -, hst, -⟩
  · refine .inl ⟨size_word_of_noCode h5, hst, ?_⟩
    rw [hss]
    exact tacDoneSs_logs
  · obtain ⟨hcst, hcss, hgasm, hcaller, htgt, -, -, hcodem, hdata, hval, -⟩ := hsent
    obtain ⟨c0, c1, c2, c3, c4⟩ := tac_call_head (message := message) hN
    refine .inr ⟨size_word_of_hasCode h5, caller, msg, child, hran, herr, hst, ?_, hcaller, hval,
      hcodem, hdata, ⟨c0, c1.trans (mask_idem _), c2, c3, c4⟩, hgasm, ?_, ?_⟩
    · rw [htgt]
      exact toAddressMasked_mask' _
    · intro a k
      simp only [hcst, tacCallSt_rar, storageAt_rar, tacMid]
    · exact (congrArg Substate.logs hcss).trans ((logs_accessAccount _ _).trans tacCallSs_logs)

end LinkVerify

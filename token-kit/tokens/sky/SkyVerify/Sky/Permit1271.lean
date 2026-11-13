import SkyVerify.Sky.Permit
import SkyVerify.Sky.OwnerCall
import TokenKit.Evm.Tail

/-!
# SKY: `permit(v, r, s)` when the recovered address is not the owner (ERC-1271)

Hand-written. The code after the comparison of the recovered address with the owner:
EXTCODESIZE of the owner, the call data of `isValidSignature(bytes32,bytes)` built in the
memory, a STATICCALL to the owner, the copy of the return data, the checks of the flag, of the
size and of the answer, and then the write of the allowance and the log.

No assumption is made on the code of the owner: the STATICCALL is the one of the real runner
(`staticcall_sent` of Sky/OwnerCall.lean, which is `staticcall_kept` of
TokenKit/Evm/StaticCall.lean with the message that was sent).

`PermitByContract` says which call was made: the return data `out` is the output of the run of
the message that the code sent to the owner (`OwnerCall`: target, call data `erc1271Input`, gas,
state). `PermitKept` is the weaker statement of before audit 4, where `out` was any string; it
follows (`PermitByContract.kept`) and is what the invariant and the readable forms use.
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

/-! ## Steps over `Logic.At` (the return data is kept)

`ls n r`: the run `h` goes on by the rule `r` to the program counter `n`. The rule macros close
the side goals about `CODE`; the gas premise is the `hG` of `RunsTo.step`. -/

set_option hygiene false in
macro "ls " n:num r:term : tactic =>
  `(tactic| replace h := RunsTo.step h hok (fun G hG => $r) (show _ = $n from rfl))

set_option hygiene false in
macro "lpush " n:term:max w:term:max : term =>
  `(Logic.pushG (n := $n) (word := $w) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by code_fact) hG (by stk_ok))
set_option hygiene false in
macro "lpushAny " n:term:max : term =>
  `(Logic.pushG (n := $n) (by decide) (by code_fact) (by code_fact)
    (decode_push $n (by decide)) (by rw [pushData_CODE]) hG (by stk_ok))
set_option hygiene false in
macro "ldup " n:term:max : term =>
  `(Logic.dupG $n (by code_fact) (by code_fact) rfl hG (by stk_ok))
set_option hygiene false in
macro "lswap " n:term:max : term => `(Logic.swapG $n (by code_fact) (by code_fact) rfl hG)
set_option hygiene false in
macro "lpop" : term => `(Logic.popG (by code_fact) (by code_fact) hG)
set_option hygiene false in
macro "ljumpdest" : term => `(Logic.jumpdestG (by code_fact) (by code_fact) hG)
set_option hygiene false in
macro "ljump" : term => `(Logic.jumpG (by code_fact) (by code_fact) hG (by valid_dest))
set_option hygiene false in
macro "ljumpi " c:term:max : term =>
  `(Logic.jumpi_takenG (by code_fact) (by code_fact) hG $c (by valid_dest))
set_option hygiene false in
macro "ljumpi0 " c:term:max : term =>
  `(Logic.jumpi_of_eq_zeroG (by code_fact) (by code_fact) hG $c)
set_option hygiene false in
macro "lbin " b:term:max i:term:max : term =>
  `(Logic.binaryG (byte := $b) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) $i hG)
set_option hygiene false in
macro "lun " b:term:max i:term:max : term =>
  `(Logic.unaryG (byte := $b) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) $i hG)
set_option hygiene false in
macro "lshl" : term =>
  `(Logic.binaryG (byte := 0x1b) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Nat.le_trans (by decide) hfork)) (instruction_of_stackOnlyStep rfl) hG)
set_option hygiene false in
macro "lmload" : term => `(Logic.mloadG (by code_fact) (by code_fact) hG)
set_option hygiene false in
macro "lmstore" : term => `(Logic.mstoreG (by code_fact) (by code_fact) hG)
set_option hygiene false in
macro "lrds" : term =>
  `(Logic.returndatasizeG (Nat.le_trans (by decide) hfork) (by code_fact) (by code_fact) hG
    (by stk_ok))

/-- From the JUMPDEST at 3753 with a zero on the stack (the checks of the answer of the owner
failed): the code reverts with "Sky/invalid-permit", so no run ends with no error. The memory
is any memory. -/
theorem permit_fail_tail (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B : Nat}
    {x fl a b c d : U256} {R : List U256} {m rd : ByteArray} {st : State.TransactionState}
    {ss : Substate} (hR : R.length ≤ 100)
    (h : RunsTo runChild s CODE message B 3753
      ((0 : U256) :: x :: fl :: a :: b :: c :: d :: (2739 : U256) :: R) m st ss rd)
    (hok : s.error = none) : False := by
  ls 3754 ljumpdest
  ls 3755 (ldup 0)
  ls 3756 (lun 0x15 instruction_iszero)
  ls 3759 (lpush 2 3802)
  ls 3802 (ljumpi (by decide))
  ls 3803 ljumpdest
  ls 3804 (lswap 6)
  ls 3805 (lswap 5)
  ls 3806 lpop
  ls 3807 lpop
  ls 3808 lpop
  ls 3809 lpop
  ls 3810 lpop
  ls 3811 lpop
  ls 2739 ljump
  ls 2740 ljumpdest
  ls 2743 (lpush 2 2804)
  ls 2744 (ljumpi0 rfl)
  ls 2746 (lpushAny 1)
  ls 2747 lmload
  ls 2751 (lpushAny 3)
  ls 2753 (lpushAny 1)
  ls 2754 lshl
  ls 2755 (ldup 1)
  ls 2756 lmstore
  ls 2758 (lpushAny 1)
  ls 2760 (lpushAny 1)
  ls 2761 (ldup 2)
  ls 2762 (lbin 0x01 instruction_add)
  ls 2763 lmstore
  ls 2765 (lpushAny 1)
  ls 2767 (lpushAny 1)
  ls 2768 (ldup 2)
  ls 2769 (lbin 0x01 instruction_add)
  ls 2770 lmstore
  ls 2789 (lpushAny 18)
  ls 2791 (lpushAny 1)
  ls 2792 lshl
  ls 2794 (lpushAny 1)
  ls 2795 (ldup 2)
  ls 2796 (lbin 0x01 instruction_add)
  ls 2797 lmstore
  ls 2799 (lpushAny 1)
  ls 2800 (lbin 0x01 instruction_add)
  ls 2803 (lpush 2 1090)
  ls 1090 ljump
  ls 1091 ljumpdest
  ls 1093 (lpushAny 1)
  ls 1094 lmload
  ls 1095 (ldup 0)
  ls 1096 (lswap 1)
  ls 1097 (lbin 0x03 instruction_sub)
  ls 1098 (lswap 0)
  exact h.reverts (fun G hG => Logic.revertG (Nat.le_trans (by decide) hfork) (by code_fact)
    (by code_fact) hG) hok
/-- From 3725, after the copy of the return data, when the size of the return data (as a word)
is not 32: the size check fails (or the flag is 0), so no run ends with no error. -/
theorem permit_wrong_size (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B : Nat}
    {N Xw flag dg owner nonce deadline value spender sS sR sv sel : U256}
    {m rd : ByteArray} {st : State.TransactionState} {ss : Substate}
    (h : RunsTo runChild s CODE message B 3725
      [N, Xw, flag, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] m st ss rd)
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
theorem permit_after_call (hfork : .berlin ≤ fork) {bound : Nat}
    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B sz : Nat}
    {Xw flag c ow dg owner nonce deadline value spender sS sR sv sel : U256}
    {M out : ByteArray} {st : State.TransactionState} {ss : Substate}
    (hs : M.size = sz) (hmod : sz % 32 = 0) (h128 : 128 ≤ Xw.toNat) (hXf : Xw.toNat + 64 ≤ sz)
    (hX32 : (add Xw (32 : U256)).toNat = Xw.toNat + 32)
    (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = Xw)
    (hflag : flag = 0 ∨ flag = 1)
    (h : RunsTo runChild s CODE message B 3683
      [flag, c, ow, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] M st ss out)
    (hok : s.error = none) :
    (BitVec.ofNat 256 out.size = 0 ∧ ∃ (g : Nat) (l : Evm fork Nat), g ≤ B ∧
      At CODE message 3729
        [(0 : U256), (0 : U256), flag, (0 : U256), (0 : U256), (0 : U256), (128 : U256), dg,
          owner, (2739 : U256), dg, nonce, (128 : U256), deadline, value, spender, owner,
          (3182 : U256), sS, sR, sv, deadline, value, spender, owner, (558 : U256), sel]
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
          owner, (2739 : U256), dg, nonce, (128 : U256), deadline, value, spender, owner,
          (3182 : U256), sS, sR, sv, deadline, value, spender, owner, (558 : U256), sel]
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
      exact permit_wrong_size hfork h
        (load_copied (load_rawW_self (size_rawW hs f64) fX)
          (size_rawW (size_rawW hs f64) fX) hmod (by omega) (by rw [hX32]; omega) h0 hNle)
        (Nat.le_trans (by omega) (size_copied_ge (size_rawW (size_rawW hs f64) fX) hmod h0
          hNle))
        h32 hflag hok

/-! ## The end of `permit` -/

/-- EQ gave a nonzero word: the two words are equal. -/
theorem word_eq_of_equal {a b : U256} (h : equal a b ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exact absurd (show equal a b = 0 from if_neg e) h

/-- The topic of `Approval(address,address,uint256)`. -/
abbrev APPROVAL_TOPIC : U256 :=
  (63486140976153616755203102783360879283472101686154884697241723088393386309925 : U256)

/-- The slot of `allowance[owner][spender]`, from the argument words. -/
abbrev permitAllowKey (owner spender : U256) : U256 :=
  mapSlot (bitwiseAnd spender ADDR_MASK) (mapSlot (bitwiseAnd ADDR_MASK owner) (3 : U256))

/-- The last part of `permit`, from the state `st`, the substate `ss` and the gas `g`: the call
is not static, the token account exists, the gas pays `c` and the write, nothing is returned,
the allowance slot holds `value` and every other slot is as in `st`, and the logs are those of
`ss` and then `Approval(owner, spender, value)`. The gas at the end is exact from `g`. -/
def PermitWrites (fork : Fork) (m : Message fork) (st : State.TransactionState) (ss : Substate)
    (g c : Nat) (s : Evm fork Nat) (owner spender value : U256) : Prop :=
  m.isStatic = false ∧
  hasAccount st m.currentTarget ∧
  (c + (Gas.writeCost fork (originalAt st m.currentTarget (permitAllowKey owner spender))
    (storageAt st m.currentTarget (permitAllowKey owner spender)) value
    (coldIn ss m.currentTarget (permitAllowKey owner spender)))) ≤ g ∧
  s.output = ByteArray.empty ∧
  s.gas = g - (c + (Gas.writeCost fork
    (originalAt st m.currentTarget (permitAllowKey owner spender))
    (storageAt st m.currentTarget (permitAllowKey owner spender)) value
    (coldIn ss m.currentTarget (permitAllowKey owner spender)))) ∧
  s.state = (writeSlot st m.currentTarget (permitAllowKey owner spender) value) ∧
  s.substate = (logSub (storeSub fork ss m.currentTarget (permitAllowKey owner spender)
    (originalAt st m.currentTarget (permitAllowKey owner spender))
    (storageAt st m.currentTarget (permitAllowKey owner spender)) value) m.currentTarget
    APPROVAL_TOPIC (bitwiseAnd ADDR_MASK owner) (bitwiseAnd spender ADDR_MASK) (wordBytes value))

/-- The ERC-1271 path of `permit` without the call (the statement of before audit 4): the
owner has code, some string `out` of 32 bytes starts with the magic value, and the state `st`
and the substate `ss` that the last part of `permit` starts from keep every account, every
storage word, every transient storage word, the logs, the accounts to delete and the refund
counter of the state at the EXTCODESIZE. Nothing here says where `out` comes from: the two facts
on `out` hold for a string picked freely. Use `PermitByContract` for the call; this form is kept
for the invariant and the readable forms, which only need what the call kept. -/
def PermitKept (fork : Fork) (m : Message fork) (st0 : State.TransactionState)
    (ss0 : Substate) (g0 : Nat) (s : Evm fork Nat) (owner spender value : U256) : Prop :=
  ∃ (c out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
    st0.getCode (st0.getAccount (toAddressMasked (bitwiseAnd owner ADDR_MASK))).codeHash =
      .ok c ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    BitVec.ofNat 256 out.size = 32 ∧
    loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
    State.TransactionState.SameOutside []
      (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))) st ∧
    st.parent = (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))).parent ∧
    ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
    ss.refundCounter = ss0.refundCounter ∧
    g + 1290 ≤ g0 ∧
    PermitWrites fork m st ss g 2347 s owner spender value

/-- The ERC-1271 path of `permit`, from the state `st0`, the substate `ss0` and the gas `g0` at
the EXTCODESIZE of the owner, under the real runner with the gas bound `bound`.

The state gives the code `c` of the owner and it is not empty (its size as a word is not 0).
Then the code made the STATICCALL that `OwnerCall` describes: to the owner address, with the
call data `erc1271Input dg sR sS vw` (`isValidSignature(digest, signature)` for the digest `dg`
and the 65 bytes `sR`, `sS` and the first byte of `vw`), in the state at the EXTCODESIZE with
the read of the owner recorded and the owner accessed, with
`g0 - (the access cost of the EXTCODESIZE + k)` gas left at the STATICCALL (`k` is the gas of
the opcodes between: 1292 for `permit(v, r, s)`). The return data `out` is the output of the
run of that message, which ended with no error; its size as a word is 32 and its first word is
the magic value.

The call kept every account, every storage word and every transient storage word
(`SameOutside []`), the logs, the accounts to delete and the refund counter. Then the code ended
as `PermitWrites` says from the state `st` and the substate `ss` after the call and a gas `g`
with `g + 1290 ≤ g0` (the gas is an inequality here: the gas that the code of the owner used is
not known). -/
def PermitByContract (fork : Fork) (bound : Nat) (m : Message fork)
    (st0 : State.TransactionState) (ss0 : Substate) (g0 : Nat) (s : Evm fork Nat) (k : Nat)
    (dg sR sS vw owner spender value : U256) : Prop :=
  ∃ (c out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
    st0.getCode (st0.getAccount (toAddressMasked (bitwiseAnd owner ADDR_MASK))).codeHash =
      .ok c ∧
    BitVec.ofNat 256 c.size ≠ 0 ∧
    OwnerCall fork bound m
      (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK)))
      { ss0 with accessedAddresses :=
        ss0.accessedAddresses.insert (toAddressMasked (bitwiseAnd owner ADDR_MASK)) }
      (g0 - (externalBaseCost fork
        (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉ ss0.accessedAddresses)) + k))
      (bitwiseAnd owner ADDR_MASK) (erc1271Input dg sR sS vw) out ∧
    BitVec.ofNat 256 out.size = 32 ∧
    loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
    State.TransactionState.SameOutside []
      (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))) st ∧
    st.parent = (st0.recordAccountRead (toAddressMasked (bitwiseAnd owner ADDR_MASK))).parent ∧
    ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
    ss.refundCounter = ss0.refundCounter ∧
    g + 1290 ≤ g0 ∧
    PermitWrites fork m st ss g 2347 s owner spender value

/-- `PermitByContract` gives the statement of before audit 4. -/
theorem PermitByContract.kept {bound : Nat} {st0 : State.TransactionState} {ss0 : Substate}
    {g0 k : Nat} {s : Evm fork Nat} {dg sR sS vw owner spender value : U256}
    (h : PermitByContract fork bound message st0 ss0 g0 s k dg sR sS vw owner spender value) :
    PermitKept fork message st0 ss0 g0 s owner spender value := by
  obtain ⟨c, out, st, ss, g, h1, h2, -, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨c, out, st, ss, g, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- Layout A (free memory pointer 579 at the call of ECRECOVER): from the GAS before the
STATICCALL to the owner to the end. -/
theorem permit_call_A (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {st0 : State.TransactionState} {ss0 : Substate} {g3 : Nat} {z3 s : Evm fork Nat}
    {ow dg owner nonce deadline value spender sS sR sv sel : U256} {Mc D : ByteArray}
    (n0 : Mc.size = 1056) (n64 : loadWord (memoryReadBytes Mc 64 32) 0 32 = (807 : U256))
    (n96 : loadWord (memoryReadBytes Mc 96 32) 0 32 = (0 : U256))
    (nd : memoryReadBytes Mc 807 196 = D)
    (hz3 : At CODE message 3681
      [ow, (807 : U256), (196 : U256), (807 : U256), (0 : U256), (1003 : U256), ow, (0 : U256),
        (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] Mc g3 st0 ss0 z3)
    (hend3 : EndsL (processRunner fork bound) z3 s) (hok : s.error = none) :
    ∃ (out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
      OwnerCall fork bound message st0 ss0 (g3 - 2) ow D out ∧
      BitVec.ofNat 256 out.size = 32 ∧
      loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
      State.TransactionState.SameOutside [] st0 st ∧ st.parent = st0.parent ∧
      ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
      ss.refundCounter = ss0.refundCounter ∧ g ≤ g3 - 2 ∧
      PermitWrites fork message st ss g 2347 s owner spender value := by
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
  rcases permit_after_call hberlin n0 (by decide) (by decide) (by decide) (by decide) n64 hflag
      h hok with
    ⟨-, g, l, hB, hat0, e0⟩ | ⟨hN, M', g, l, hB, s0, s64, s96, sX, sX32, hat1, e1⟩
  · exact False.elim (Paths.ok_permitEmptyA_ends hberlin n0 n64 n96 hat0 e0 hok)
  · obtain ⟨hfl, hrw1, hrw2, r⟩ := Paths.ok_permitAnswerA_ends hberlin s0
      (s64.trans (by decide)) (s96.trans n96) sX sX32 hat1 e1 hok
    have e1' := word_eq_of_equal hrw1
    have e2' := word_eq_of_equal hrw2
    obtain ⟨cc, route, caller, msg, child, hcc, hroute, hsend, hran, hcerr, hcout⟩ :=
      hsent (isZero_eq_zero_iff.mp hfl)
    exact ⟨out, st, ss, g,
      ownerCall_of_sends (i := (807 : U256)) (isz := (196 : U256))
        (by rw [n0]; decide) nd hcc hroute hsend hran hcerr hcout, hN,
      e1'.trans ((BitVec.and_comm _ _).trans e2'), hso, hpar, hlogs, hdel, href, by omega, r⟩

/-- Layout A: from the EXTCODESIZE of the owner to the end (`PermitByContract`). -/
theorem permit_contract_A (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {z s : Evm fork Nat}
    {dg owner nonce deadline value spender sS sR sv sel vw : U256} {M : ByteArray}
    (pm : PermitMem M 736 (579 : U256) sR sS vw)
    (hz : At CODE message 3580
      [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] M gas state substate z)
    (hend : EndsL (processRunner fork bound) z s) (hok : s.error = none) :
    PermitByContract fork bound message state substate gas s 1292 dg sR sS vw owner spender
      value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨within, hrun⟩ := hend
  rcases extcodesize_outcome hberlin (by code_fact) (by code_fact) hz within hrun with
    herr | ⟨c, z1, hcode, hg1, hz1, w1, hrun1⟩
  · exact absurd hok herr
  obtain ⟨hcs, hg2, z2, hz2, hend2⟩ := Paths.ok_permitCodeA_ends hberlin pm.size pm.fp pm.w96
    pm.w128 pm.w160 pm.w192 pm.top hz1 ⟨w1, hrun1⟩ hok
  obtain ⟨m0, m64, m96, -, -, -, m579, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCodeA_p0_mem (cs := BitVec.ofNat 256 c.size) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sv := sv) (sel := sel) (vw := vw) pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 pm.top
  obtain ⟨hg3, z3, hz3, hend3⟩ :=
    Paths.ok_permitCopyA_ends hberlin m0 m64 m96 m579 hz2 hend2 hok
  obtain ⟨n0, n64, n96, -, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCopyA_p0_mem (ow := bitwiseAnd ADDR_MASK owner) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sv := sv) (sel := sel) m0 m64 m96 m579
  have cd := code_data (F := 579) (dg := dg) (sR := sR) (sS := sS) (vw := vw)
    (fpn := (807 : U256)) pm.size pm.top (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl
  have cp := copy_data (S := 611) (G := 807) cd.1 rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
  rw [show bitwiseAnd ADDR_MASK owner = bitwiseAnd owner ADDR_MASK from BitVec.and_comm _ _]
    at hz3
  obtain ⟨out, st, ss, g, hcall, hN, hmagic, hso, hpar, hlogs, hdel, href, hg, r⟩ :=
    permit_call_A hparis hglam n0 n64 n96 (cp.2.trans cd.2) hz3 hend3 hok
  have eg : gas - externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
      substate.accessedAddresses)) - 626 - 664 - 2 =
      gas - (externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
        substate.accessedAddresses)) + 1292) := by omega
  rw [eg] at hcall
  exact ⟨c, out, st, ss, g, hcode, isZero_eq_zero_iff.mp hcs, hcall, hN, hmagic, hso, hpar,
    hlogs, hdel, href, by omega, r⟩

/-- Layout B (free memory pointer 899 at the call of ECRECOVER): from the GAS before the
STATICCALL to the owner to the end. -/
theorem permit_call_B (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {st0 : State.TransactionState} {ss0 : Substate} {g3 : Nat} {z3 s : Evm fork Nat}
    {ow dg owner nonce deadline value spender sS sR sv sel : U256} {Mc D : ByteArray}
    (n0 : Mc.size = 1376) (n64 : loadWord (memoryReadBytes Mc 64 32) 0 32 = (1127 : U256))
    (n96 : loadWord (memoryReadBytes Mc 96 32) 0 32 = (0 : U256))
    (nd : memoryReadBytes Mc 1127 196 = D)
    (hz3 : At CODE message 3681
      [ow, (1127 : U256), (196 : U256), (1127 : U256), (0 : U256), (1323 : U256), ow, (0 : U256),
        (0 : U256), (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] Mc g3 st0 ss0 z3)
    (hend3 : EndsL (processRunner fork bound) z3 s) (hok : s.error = none) :
    ∃ (out : ByteArray) (st : State.TransactionState) (ss : Substate) (g : Nat),
      OwnerCall fork bound message st0 ss0 (g3 - 2) ow D out ∧
      BitVec.ofNat 256 out.size = 32 ∧
      loadWord (memoryReadBytes out 0 32) 0 32 = MAGIC_1271 ∧
      State.TransactionState.SameOutside [] st0 st ∧ st.parent = st0.parent ∧
      ss.logs = ss0.logs ∧ ss.accountsToDelete = ss0.accountsToDelete ∧
      ss.refundCounter = ss0.refundCounter ∧ g ≤ g3 - 2 ∧
      PermitWrites fork message st ss g 2347 s owner spender value := by
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
  rcases permit_after_call hberlin n0 (by decide) (by decide) (by decide) (by decide) n64 hflag
      h hok with
    ⟨-, g, l, hB, hat0, e0⟩ | ⟨hN, M', g, l, hB, s0, s64, s96, sX, sX32, hat1, e1⟩
  · exact False.elim (Paths.ok_permitEmptyB_ends hberlin n0 n64 n96 hat0 e0 hok)
  · obtain ⟨hfl, hrw1, hrw2, r⟩ := Paths.ok_permitAnswerB_ends hberlin s0
      (s64.trans (by decide)) (s96.trans n96) sX sX32 hat1 e1 hok
    have e1' := word_eq_of_equal hrw1
    have e2' := word_eq_of_equal hrw2
    obtain ⟨cc, route, caller, msg, child, hcc, hroute, hsend, hran, hcerr, hcout⟩ :=
      hsent (isZero_eq_zero_iff.mp hfl)
    exact ⟨out, st, ss, g,
      ownerCall_of_sends (i := (1127 : U256)) (isz := (196 : U256))
        (by rw [n0]; decide) nd hcc hroute hsend hran hcerr hcout, hN,
      e1'.trans ((BitVec.and_comm _ _).trans e2'), hso, hpar, hlogs, hdel, href, by omega, r⟩

/-- Layout B: from the EXTCODESIZE of the owner to the end (`PermitByContract`). -/
theorem permit_contract_B (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam) {bound : Nat}
    {state : State.TransactionState} {substate : Substate} {gas : Nat} {z s : Evm fork Nat}
    {dg owner nonce deadline value spender sS sR sv sel vw : U256} {M : ByteArray}
    (pm : PermitMem M 1056 (899 : U256) sR sS vw)
    (hz : At CODE message 3580
      [bitwiseAnd owner ADDR_MASK, (0 : U256), (128 : U256), dg, owner, (2739 : U256),
        dg, nonce, (128 : U256), deadline, value, spender, owner, (3182 : U256), sS, sR, sv,
        deadline, value, spender, owner, (558 : U256), sel] M gas state substate z)
    (hend : EndsL (processRunner fork bound) z s) (hok : s.error = none) :
    PermitByContract fork bound message state substate gas s 1292 dg sR sS vw owner spender
      value := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨within, hrun⟩ := hend
  rcases extcodesize_outcome hberlin (by code_fact) (by code_fact) hz within hrun with
    herr | ⟨c, z1, hcode, hg1, hz1, w1, hrun1⟩
  · exact absurd hok herr
  obtain ⟨hcs, hg2, z2, hz2, hend2⟩ := Paths.ok_permitCodeB_ends hberlin pm.size pm.fp pm.w96
    pm.w128 pm.w160 pm.w192 pm.top hz1 ⟨w1, hrun1⟩ hok
  obtain ⟨m0, m64, m96, -, -, -, m579, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCodeB_p0_mem (cs := BitVec.ofNat 256 c.size) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sv := sv) (sel := sel) (vw := vw) pm.size pm.fp pm.w96 pm.w128 pm.w160
      pm.w192 pm.top
  obtain ⟨hg3, z3, hz3, hend3⟩ :=
    Paths.ok_permitCopyB_ends hberlin m0 m64 m96 m579 hz2 hend2 hok
  obtain ⟨n0, n64, n96, -, -, -, -, -, -, -, -, -⟩ :=
    Paths.permitCopyB_p0_mem (ow := bitwiseAnd ADDR_MASK owner) (dg := dg) (owner := owner)
      (nonce := nonce) (deadline := deadline) (value := value) (spender := spender) (sS := sS)
      (sR := sR) (sv := sv) (sel := sel) m0 m64 m96 m579
  have cd := code_data (F := 899) (dg := dg) (sR := sR) (sS := sS) (vw := vw)
    (fpn := (1127 : U256)) pm.size pm.top (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl
  have cp := copy_data (S := 931) (G := 1127) cd.1 rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
  rw [show bitwiseAnd ADDR_MASK owner = bitwiseAnd owner ADDR_MASK from BitVec.and_comm _ _]
    at hz3
  obtain ⟨out, st, ss, g, hcall, hN, hmagic, hso, hpar, hlogs, hdel, href, hg, r⟩ :=
    permit_call_B hparis hglam n0 n64 n96 (cp.2.trans cd.2) hz3 hend3 hok
  have eg : gas - externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
      substate.accessedAddresses)) - 626 - 664 - 2 =
      gas - (externalBaseCost fork (decide (toAddressMasked (bitwiseAnd owner ADDR_MASK) ∉
        substate.accessedAddresses)) + 1292) := by omega
  rw [eg] at hcall
  exact ⟨c, out, st, ss, g, hcode, isZero_eq_zero_iff.mp hcs, hcall, hN, hmagic, hso, hpar,
    hlogs, hdel, href, by omega, r⟩

/-- What follows the call of ECRECOVER in `permit`, for both layouts of the memory: with the
recovered word `rec`,

- the recovered address is the owner: the code ends as `PermitWrites` says from the state, the
  substate and the gas after the call, with exact gas (2190 and the price of the write);
- or it is not: 128 gas was there, and the code ends as `PermitByContract` says (ERC-1271): it
  called the owner with the digest `dg` and the signature `sR`, `sS`, first byte of `vw`, and
  the answer of that call was the magic value. -/
def PermitEnd (fork : Fork) (bound : Nat) (m : Message fork) (st : State.TransactionState)
    (ss : Substate) (g : Nat) (s : Evm fork Nat) (k : Nat)
    (dg sR sS vw owner spender value rec : U256) : Prop :=
  ((sub (bitwiseAnd ADDR_MASK owner) (bitwiseAnd ADDR_MASK rec)) = 0 ∧
    PermitWrites fork m st ss g 2190 s owner spender value) ∨
  ((sub (bitwiseAnd ADDR_MASK owner) (bitwiseAnd ADDR_MASK rec)) ≠ 0 ∧ 128 ≤ g ∧
    PermitByContract fork bound m st ss (g - 128) s k dg sR sS vw owner spender value)

/-- `PermitEnd` without the call (the statement of before audit 4, with `PermitKept`): what the
invariant and the readable forms use. -/
def PermitEndKept (fork : Fork) (m : Message fork) (st : State.TransactionState) (ss : Substate)
    (g : Nat) (s : Evm fork Nat) (owner spender value rec : U256) : Prop :=
  ((sub (bitwiseAnd ADDR_MASK owner) (bitwiseAnd ADDR_MASK rec)) = 0 ∧
    PermitWrites fork m st ss g 2190 s owner spender value) ∨
  ((sub (bitwiseAnd ADDR_MASK owner) (bitwiseAnd ADDR_MASK rec)) ≠ 0 ∧ 128 ≤ g ∧
    PermitKept fork m st ss (g - 128) s owner spender value)

/-- `PermitEnd` gives `PermitEndKept`. -/
theorem PermitEnd.kept {bound : Nat} {st : State.TransactionState} {ss : Substate} {g k : Nat}
    {s : Evm fork Nat} {dg sR sS vw owner spender value rec : U256}
    (h : PermitEnd fork bound message st ss g s k dg sR sS vw owner spender value rec) :
    PermitEndKept fork message st ss g s owner spender value rec := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, h2, h3.kept⟩

/-- `PermitEnd` cannot hold when the recovered address is not the owner and the state holds
no code at the owner: the ERC-1271 path needs code at the owner. -/
theorem permitEnd_no_code {bound : Nat} {st : State.TransactionState} {ss : Substate}
    {g k : Nat} {s : Evm fork Nat} {dg sR sS vw owner spender value rec : U256}
    (hne : sub (bitwiseAnd ADDR_MASK owner) (bitwiseAnd ADDR_MASK rec) ≠ 0)
    (hcode : ∀ c, st.getCode
      (st.getAccount (toAddressMasked (bitwiseAnd owner ADDR_MASK))).codeHash = .ok c →
      c.size = 0)
    (hend : PermitEnd fork bound message st ss g s k dg sR sS vw owner spender value rec) :
    False := by
  rcases hend with ⟨h0, -⟩ | ⟨-, -, c, out, st', ss', g', hc, hsz, -⟩
  · exact hne h0
  · exact hsz (by simp [hcode c hc])

/-- `PermitEnd` in the shape of the last argument of `PermitAfterEc`: the digest, the signature
words and the gas bound of the runner are the ones of the run. `k` is the gas of the opcodes
between the EXTCODESIZE of the owner and the STATICCALL (1292). -/
abbrev permitEndF (fork : Fork) (m : Message fork) (k : Nat) :
    (state : State.TransactionState) → (substate : Substate) → (gas : Nat) →
    (s : Evm fork Nat) → (vb sS sR dg owner nonce deadline value spender sv sel rec vw : U256) →
    (mem : ByteArray) → {bound : Nat} → (runChild : MessageRunner fork Nat bound) → Prop :=
  fun st ss g s _ sS sR dg owner _ _ value spender _ _ rec vw _ {bound} _ =>
    PermitEnd fork bound m st ss g s k dg sR sS vw owner spender value rec

/-- Completeness for `permit(owner, spender, value, deadline, v, r, s)` (selector `0xd505accf`)
over the real runner (`processRunner`), from Paris and before Glamsterdam, with no assumption on
ECRECOVER and none on the code of the owner. A run of a fresh frame of the code that ends with
no error passed the checks (`PermitChecks`), was not static, the token account exists, and it
ended as `PermitEnd` says after the call of ECRECOVER (`PermitAfterEc`): by the signature path
with exact gas, or by the ERC-1271 path with a gas inequality. On the ERC-1271 path the
statement names the call (`PermitByContract`, `OwnerCall`): the answer checked is the output of
the STATICCALL to the owner with `isValidSignature(digest, signature)` as call data. -/
theorem ok_permit_full {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    PermitChecks message ∧ message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    ((equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) = 0 ∧
        PermitAfterEc fork message state substate gas s bound 2207 1056 (899 : U256)
          (permitDomain message) (permitEndF fork message 1292)) ∨
      (equal (1 : U256) (BitVec.ofNat 256 message.blockEnv.chainId.toNat) ≠ 0 ∧
        PermitAfterEc fork message state substate gas s bound 1811 736 (579 : U256)
          DOMAIN_MAINNET (permitEndF fork message 1292))) := by
  obtain ⟨hchecks, hstatic, hacc, hlay⟩ :=
    ok_permit_ec hparis hglam hsize' hsel hdel start within hrun hok
  refine ⟨hchecks, hstatic, hacc, ?_⟩
  rcases hlay with ⟨hchain, hcg, h3000, M, pm, hends⟩ | ⟨hchain, hcg, h3000, M, pm, hends⟩
  · refine .inl ⟨hchain, hcg, h3000, M, pm, ?_⟩
    rcases hends with ⟨hsub, r⟩ | ⟨hsub, hg, z, hz, hend⟩
    · exact .inl ⟨hsub, r⟩
    · exact .inr ⟨hsub, hg, permit_contract_B hparis hglam pm hz hend hok⟩
  · refine .inr ⟨hchain, hcg, h3000, M, pm, ?_⟩
    rcases hends with ⟨hsub, r⟩ | ⟨hsub, hg, z, hz, hend⟩
    · exact .inl ⟨hsub, r⟩
    · exact .inr ⟨hsub, hg, permit_contract_A hparis hglam pm hz hend hok⟩

/-- A `permit` whose recovered address is not the owner (for the domain separator of either
layout), to an owner that holds no code in the state after the call of ECRECOVER, never ends
with no error: the ERC-1271 path needs code at the owner. -/
theorem permit_no_code_fails {state : State.TransactionState} {substate : Substate}
    (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xd505accf)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    (hrec : ∀ domain : U256,
      sub (bitwiseAnd ADDR_MASK (loadWord message.data 4 32))
        (bitwiseAnd ADDR_MASK (recoveredWord (permitInput
          (permitDigest domain (permitStruct message state)) (permitV message)
          (loadWord message.data 164 32) (loadWord message.data 196 32)))) ≠ 0)
    (hcode : ∀ c, (ecState message (permitState1 message state)).getCode
      ((ecState message (permitState1 message state)).getAccount
        (toAddressMasked (bitwiseAnd (loadWord message.data 4 32) ADDR_MASK))).codeHash = .ok c →
      c.size = 0)
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s) :
    s.error ≠ none := by
  intro hok
  obtain ⟨-, -, -, hlay⟩ := ok_permit_full hparis hglam hsize' hsel hdel start within hrun hok
  have key : ∀ {g k : Nat} {dg sR sS vw rec : U256},
      sub (bitwiseAnd ADDR_MASK (loadWord message.data 4 32)) (bitwiseAnd ADDR_MASK rec) ≠ 0 →
      PermitEnd fork bound message (ecState message (permitState1 message state))
        (ecSub (permitSub1 fork message state substate)) g s k dg sR sS vw
        (loadWord message.data 4 32) (loadWord message.data 36 32) (loadWord message.data 68 32)
        rec → False := by
    intro g k dg sR sS vw rec hne hend
    unfold PermitEnd PermitByContract at hend
    rcases hend with ⟨h0, -⟩ | ⟨-, -, c, out, st, ss, g', hc, hsz, -⟩
    · exact hne h0
    · exact hsz (by simp [hcode c hc])
  rcases hlay with ⟨-, hA⟩ | ⟨-, hA⟩
  · unfold PermitAfterEc at hA
    obtain ⟨-, -, M, -, hend⟩ := hA
    exact key (hrec _) hend
  · unfold PermitAfterEc at hA
    obtain ⟨-, -, M, -, hend⟩ := hA
    exact key (hrec _) hend

end SkyVerify

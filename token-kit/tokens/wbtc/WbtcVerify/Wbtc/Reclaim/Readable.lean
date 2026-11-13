import WbtcVerify.Wbtc.Reclaim.Good
import WbtcVerify.Wbtc.CallBubble

/-!
# `reclaimToken(address token)`: one readable statement

`reclaimToken_readable` says, for every run of `reclaimToken` that ends with no error, with any
runner of the outside calls:

- WHO MAY CALL: no value is sent and the caller is the owner (bits 8..167 of slot 5).
- WHAT IS SENT: exactly two messages, both from WBTC to the token (the address in the first
  argument; ANY address, WBTC itself included), both with value 0:
  1. 36 bytes with selector `0x70a08231` (`balanceOf(address)`) and the address of WBTC;
  2. 68 bytes with selector `0xa9059cbb` (`transfer(address,uint256)`), the owner and the first
     word that the first call returned.
- THE OWNER IS READ AGAIN: the owner in the second message is the owner in slot 5 of the state
  that the FIRST CHILD LEFT, not the owner that was checked at the start. A token that changes
  the owner of WBTC during `balanceOf` changes who is paid.
- WHAT MUST COME BACK: each child ended with no error and returned at least 32 bytes; the first
  word that the second child returned is not 0.
- WBTC'S OWN OPCODES TOUCH NOTHING: the frame handed to the runner at each call reads as the
  state before (the start state, then the state the first child left: `ReadsAs`, only records
  of reads differ) and has the logs of the frame before; the state at the end is the state the
  second child left, the substate at the end is the substate after the second child was taken
  in, and the output is empty.

Also here: `rc_data1`, `rc_data2` (size, selector and head words of the data of each message),
`rc_caller_owner`, `rcOwner_address`.

Assumed: Berlin ≤ fork < Glamsterdam, one counter of gas, call data below 2^256 bytes.
Not covered: what the children do (any runner); the runs that end with an error (`Fail.lean`);
the gas (exact in `ok_reclaim`).
-/

set_option autoImplicit false

namespace WbtcVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open WbtcVerify.Paths WbtcVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## Small facts -/

/-- EQ pushed a word that is not 0: the operands are equal. -/
theorem rc_eq_of_equal {a b : U256} (h : equal a b ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exact absurd (by unfold equal; rw [if_neg e]) h

/-- The owner test passed: the caller is the address in bits 8..167 of slot 5. -/
theorem rc_caller_owner {a : Address} {w : U256}
    (h : equal a.toU256 (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) ≠ 0) : a = toAddressMasked w := by
  have e := congrArg toAddressMasked (rc_eq_of_equal h)
  rw [EthLib.Base.toAddressMasked_toU256, toAddressMasked_mask] at e
  exact e

/-- The address in the owner word of the second message is the address in bits 8..167 of slot 5
of the state `S`. -/
theorem rcOwner_address (message : Message fork) (S : State.TransactionState) :
    toAddressMasked (rcOwner message S) =
      toAddressMasked (div (storageAt S message.currentTarget (5 : U256)) (256 : U256)) := by
  unfold rcOwner
  rw [toAddressMasked_mask, toAddressMasked_mask, and_mask_comm, toAddressMasked_mask]

/-! ## The data of the two messages -/

/-- The first four bytes at 128 of the memory at the first CALL. -/
theorem rc_byte1 (message : Message fork) {i : Nat} (hi : i < 4) :
    byteAt (rcMem1 message) (128 + i) = byteAt (wordBytes (50942633119752846454219349998365661925608737367104304655302372697894809501696 : U256)) i := by
  unfold rcMem1
  rw [byteAt_rawW_other (size_memW5 _ _ _ _ _) (by decide) (.inl (by omega)), byteAt_memW,
    show (128 + i) / 32 = 4 from by omega, show (128 + i) % 32 = i from by omega]
  rfl

/-- The data of the first message: 36 bytes, the selector of `balanceOf(address)`, then the
address of WBTC. -/
theorem rc_data1 (message : Message fork) :
    (memoryReadBytes (rcMem1 message) 128 36).size = 36 ∧
      selector (memoryReadBytes (rcMem1 message) 128 36) = 0x70a08231 ∧
      loadWord (memoryReadBytes (rcMem1 message) 128 36) 4 32 = message.currentTarget.toU256 := by
  have msz := reclaimToken_p2_mem (message := message)
  have hs : (rcMem1 message).size = 192 := msz.1
  have w : ∀ i, i < 4 → byteAt (rcMem1 message) (128 + i) = _ := fun i hi => rc_byte1 message hi
  refine ⟨size_memoryReadBytes (by rw [hs]; decide), ?_, ?_⟩
  · rw [selector_read (m := rcMem1 message) (a := 128) (k := 36) (by rw [hs]; decide)
      (by decide) (w 0 (by decide)) (w 1 (by decide)) (w 2 (by decide)) (w 3 (by decide))]
    decide +kernel
  · rw [loadWord_read_sub (m := rcMem1 message) (a := 128) (k := 36) (off := 4)
      (by rw [hs]; decide) (by decide)]
    exact msz.2.2.2.2.2

/-- The first four bytes at 128 of the memory at the second CALL. -/
theorem rc_byte2 (message : Message fork) (S : State.TransactionState) {mem : ByteArray}
    (bal : U256) (hs : mem.size = 192) {i : Nat} (hi : i < 4) :
    byteAt (rcMem2 message S mem bal) (128 + i) = byteAt (wordBytes (76450787359836037641860180984291677749980919077056822294353438043884394381312 : U256)) i := by
  unfold rcMem2
  rw [byteAt_rawW_other (size_rawW (size_rawW hs (by decide)) (by decide)) (by decide)
      (.inl (by omega)),
    byteAt_rawW_other (size_rawW hs (by decide)) (by decide) (.inl (by omega)),
    byteAt_rawW_self hs (by decide) (by omega)]

/-- The data of the second message: 68 bytes, the selector of `transfer(address,uint256)`, the
owner word read from the state `S`, and the word `bal` that was at memory 128. -/
theorem rc_data2 (message : Message fork) (S : State.TransactionState) {mem : ByteArray}
    {bal : U256} (hs : mem.size = 192)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = bal) :
    (memoryReadBytes (rcMem2 message S mem bal) 128 68).size = 68 ∧
      selector (memoryReadBytes (rcMem2 message S mem bal) 128 68) = 0xa9059cbb ∧
      loadWord (memoryReadBytes (rcMem2 message S mem bal) 128 68) 4 32 = rcOwner message S ∧
      loadWord (memoryReadBytes (rcMem2 message S mem bal) 128 68) 36 32 = bal := by
  have msz := reclaimMid_p1_mem (message := message) (state := S) (n := 0) (t := 0) (sel := 0)
    hs hfp hw
  have hs2 : (rcMem2 message S mem bal).size = 224 := msz.1
  have w : ∀ i, i < 4 → byteAt (rcMem2 message S mem bal) (128 + i) = _ :=
    fun i hi => rc_byte2 message S bal hs hi
  refine ⟨size_memoryReadBytes (by rw [hs2]; decide), ?_, ?_, ?_⟩
  · rw [selector_read (m := rcMem2 message S mem bal) (a := 128) (k := 68)
      (by rw [hs2]; decide) (by decide) (w 0 (by decide)) (w 1 (by decide)) (w 2 (by decide))
      (w 3 (by decide))]
    decide +kernel
  · rw [loadWord_read_sub (m := rcMem2 message S mem bal) (a := 128) (k := 68) (off := 4)
      (by rw [hs2]; decide) (by decide)]
    exact msz.2.2.1
  · rw [loadWord_read_sub (m := rcMem2 message S mem bal) (a := 128) (k := 68) (off := 36)
      (by rw [hs2]; decide) (by decide)]
    exact msz.2.2.2

/-! ## The readable statement -/

/-- `reclaimToken(address token)`, for EVERY run that ends with no error and every runner of the
outside calls.

Who may call: no value, and the caller is the owner of slot 5.

What is sent: two messages from WBTC to the token (`rcToken`: the address in the first
argument, any address), with value 0: `balanceOf(WBTC)` (36 bytes), then
`transfer(owner, balance)` (68 bytes), where `balance` is the first word that the first child
returned and `owner` is read from slot 5 of the state that the FIRST CHILD LEFT.

What must come back: both children ended with no error and returned at least 32 bytes; the
first word of the second is not 0.

WBTC's own opcodes: each frame handed to the runner reads as the state before it (`ReadsAs`)
and has the logs of the frame before it; the end state is the state the second child left, the
end substate is the substate after the second child was taken in; the output is empty. -/
theorem reclaimToken_readable (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    -- who may call
    message.value = 0 ∧
    message.caller =
      toAddressMasked (div (storageAt state message.currentTarget (5 : U256)) (256 : U256)) ∧
    ∃ (caller1 : Evm fork Nat) (msg1 : Message fork) (child1 : Evm fork Nat)
      (caller2 : Evm fork Nat) (msg2 : Message fork) (child2 : Evm fork Nat),
      -- the first message: balanceOf(WBTC), to the token
      msg1.currentTarget = rcToken message ∧ msg1.caller = message.currentTarget ∧
      msg1.value = 0 ∧ msg1.data.size = 36 ∧ selector msg1.data = 0x70a08231 ∧
      loadWord msg1.data 4 32 = message.currentTarget.toU256 ∧
      ReadsAs caller1.state state ∧ caller1.substate.logs = substate.logs ∧
      Ran runChild caller1 msg1 child1 ∧ child1.error = none ∧ 32 ≤ child1.output.size ∧
      -- the second message: transfer(owner read again, balance returned), to the token
      msg2.currentTarget = rcToken message ∧ msg2.caller = message.currentTarget ∧
      msg2.value = 0 ∧ msg2.data.size = 68 ∧ selector msg2.data = 0xa9059cbb ∧
      toAddressMasked (loadWord msg2.data 4 32) =
        toAddressMasked
          (div (storageAt child1.state message.currentTarget (5 : U256)) (256 : U256)) ∧
      loadWord msg2.data 36 32 = loadWord (memoryReadBytes child1.output 0 32) 0 32 ∧
      ReadsAs caller2.state child1.state ∧
      caller2.substate.logs = (incorporateChild fork caller1 child1).substate.logs ∧
      Ran runChild caller2 msg2 child2 ∧ child2.error = none ∧ 32 ≤ child2.output.size ∧
      loadWord (memoryReadBytes child2.output 0 32) 0 32 ≠ 0 ∧
      -- the end
      s.state = child2.state ∧ s.substate = (incorporateChild fork caller2 child2).substate ∧
      s.output = ByteArray.empty := by
  obtain ⟨hval, hown, c1, route1, caller1, msg1, child1, c2, route2, caller2, msg2, child2, -, -,
    hvia1, css1, md1, -, hran1, herr1, h321, -, -, hvia2, css2, md2, -, hran2, herr2, h322, hne,
    hst, hss, hout, -⟩ := ok_reclaim hfork hglam hsize' hsel start hrun hok
  obtain ⟨_, _, -, -, hr1, hca1, hcu1, -, -, -, -, hv1, -⟩ := hvia1
  obtain ⟨_, _, -, -, hr2, hca2, hcu2, -, -, -, -, hv2, -⟩ := hvia2
  have msz := reclaimToken_p2_mem (message := message)
  have hsW : (rcOut (rcMem1 message) child1.output).size = 192 :=
    size_rcOut child1.output msz.1 (by decide)
  have hfpW : loadWord (memoryReadBytes (rcOut (rcMem1 message) child1.output) 64 32) 0 32 =
      (128 : U256) := fp_rcOut child1.output msz.1 (by decide) msz.2.1
  have hwW : loadWord (memoryReadBytes (rcOut (rcMem1 message) child1.output) 128 32) 0 32 =
      loadWord (memoryReadBytes child1.output 0 32) 0 32 :=
    word_rcOut child1.output msz.1 (by decide) h321
  obtain ⟨d1s, d1sel, d1w⟩ := rc_data1 message
  obtain ⟨d2s, d2sel, d2o, d2b⟩ := rc_data2 message child1.state hsW hfpW hwW
  refine ⟨isZero_ne_zero_iff.mp hval, rc_caller_owner hown, caller1, msg1, child1, caller2, msg2,
    child2, hcu1, hca1, hv1, by rw [md1]; exact d1s, by rw [md1]; exact d1sel,
    by rw [md1]; exact d1w, hr1.trans (readsAs_rcSt _ _ _),
    by rw [css1]; exact (rcCallerSub_quiet _ _ _ _).1, hran1, herr1, h321,
    hcu2, hca2, hv2, by rw [md2]; exact d2s, by rw [md2]; exact d2sel,
    by rw [md2, d2o]; exact rcOwner_address _ _, by rw [md2]; exact d2b,
    hr2.trans (readsAs_rcSt _ _ _), by rw [css2]; exact (rcCallerSub_quiet _ _ _ _).1, hran2,
    herr2, h322, hne, hst, hss, hout⟩

end WbtcVerify

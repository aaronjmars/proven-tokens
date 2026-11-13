import WbtcVerify.Wbtc.CallOut
import WbtcVerify.Wbtc.Gen.PReclaimToken
import WbtcVerify.Wbtc.Gen.PReclaimCodeA
import WbtcVerify.Wbtc.Gen.PReclaimMid
import WbtcVerify.Wbtc.Gen.PReclaimCodeB
import WbtcVerify.Wbtc.Gen.PReclaimEnd
import TokenKit.Evm.Logic

/-!
# `reclaimToken(address token)`: every run that ends with no error, with its two outside calls

Selector 0x17ffc320, entry 537, body 1405..1620 and 3084..3260. The generated path files give
the code between the hand opcodes; this file joins them through EXTCODESIZE (1521, 3196), GAS
(1535, 3210), CALL (1536, 3211) and the code after each call (1537..1561, 3212..3236), with the
rules of `CallOut.lean` and of the kit.

What the bytes do, as proved here for every run that ends with no error (`ok_reclaim`):

1. The value is 0 and the caller is the owner (bits 8..167 of slot 5).
2. The token (the low 160 bits of the first argument, `rcToken`) has code (EXTCODESIZE not 0).
3. First CALL, to the token, value 0, gas = all gas left (the 63/64 rule decides what is sent),
   data = 36 bytes of memory from 128 (`balanceOf(address(this))`), output to memory 128..160.
   The child ended with no error and returned at least 32 bytes.
4. The owner is read AGAIN from slot 5 of the state that the first child left.
5. The token has code in that state.
6. Second CALL, to the token, value 0, gas = all gas left, data = 68 bytes of memory from 128
   (`transfer(owner read in 4, first word returned in 3)`), output to memory 128..160. The child
   ended with no error, returned at least 32 bytes, and its first word is not 0.
7. The frame stops with no output. Its state is the state that the second child left, its
   substate is the substate after that child was taken in. The gas is exact, as a formula in
   the gas that the two children left.

WBTC's own opcodes write no storage and emit no log in this function: between the calls the
state changes only by records of reads (`rcSt`).

Each message is described by EthLib's `SentVia`: the frame handed to the runner reads as the
state before the call, the message goes to the token with value 0 from WBTC, and it runs the
code that the state holds for the address the call resolves to (the token, or its EIP-7702
delegate). The token is ANY address: it may be WBTC itself.

Assumed: Berlin ≤ fork < Glamsterdam, one counter of gas, call data below 2^256 bytes.
Not covered here: the runs that end with an error (see `Fail.lean`); what the two children do
(any runner).
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
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-! ## Names for the parts of the run -/

/-- The word of the token on the stack: the first argument, masked to 160 bits. -/
def rcT (message : Message fork) : U256 :=
  bitwiseAnd (loadWord message.data 4 32) (1461501637330902918203684832716283019655932542975 : U256)

/-- The token: the address in the first argument of `reclaimToken`. -/
def rcToken (message : Message fork) : Address := toAddressMasked (rcT message)

/-- The token is the address of the low 160 bits of the first argument. -/
theorem rcToken_eq (message : Message fork) :
    rcToken message = toAddressMasked (loadWord message.data 4 32) := by
  unfold rcToken rcT
  rw [and_mask_comm, toAddressMasked_mask]

/-- The state of the frame at each CALL, from the state `S` before the owner check (first call)
or the state that the first child left (second call): one storage read (slot 5) and one account
read (the token) are recorded. Nothing else differs. -/
def rcSt (message : Message fork) (S : State.TransactionState) (tok : Address) :
    State.TransactionState :=
  (readSlot S message.currentTarget (5 : U256)).recordAccountRead tok

/-- The substate of the frame at each CALL: slot 5 and the token are accessed. -/
def rcSub (ss : Substate) (L tok : Address) : Substate :=
  { accessSlot ss L (5 : U256) with
    accessedAddresses := (accessSlot ss L (5 : U256)).accessedAddresses.insert tok }

/-- The substate of the frame handed to the runner at each CALL: the substate at the CALL, with
the token accessed and, for a token that is an EIP-7702 delegation, its delegate accessed. Logs,
accounts to delete and refund counter are those of `ss`. -/
def rcCallerSub (ss : Substate) (L tok : Address) (route : Route) : Substate :=
  routeSub { rcSub ss L tok with
    accessedAddresses := (rcSub ss L tok).accessedAddresses.insert tok } route

/-- The frame handed to the runner has the logs, the accounts to delete and the refund counter
of the frame before the part. -/
theorem rcCallerSub_quiet (ss : Substate) (L tok : Address) (route : Route) :
    (rcCallerSub ss L tok route).logs = ss.logs ∧
      (rcCallerSub ss L tok route).accountsToDelete = ss.accountsToDelete ∧
      (rcCallerSub ss L tok route).refundCounter = ss.refundCounter := by
  rcases route with _ | ⟨d, c⟩ <;> exact ⟨rfl, rfl, rfl⟩

/-- The gas of the frame at each CALL, from the gas `gas` at the start of the part: `pre` plus
the read of slot 5, then EXTCODESIZE, then 25 for the test of the size, then 2 for GAS. -/
def rcGas (fork : Fork) (ss : Substate) (L tok : Address) (pre gas : Nat) : Nat :=
  gas - (pre + slotCost (coldIn ss L (5 : U256))) -
    externalBaseCost fork (decide (tok ∉ (accessSlot ss L (5 : U256)).accessedAddresses)) - 25 - 2

/-- The gas of a CALL that asks for all the gas `g` of the frame (GAS then CALL), with value 0
and no growth of memory: `.cost` is what the frame pays, `.subCall` is what the message gets
(the 63/64 rule). `ss` is the substate at the CALL. -/
def rcCallGas (fork : Fork) (ss : Substate) (tok : Address) (route : Route) (g : Nat) :=
  messageCallGas fork 0 (BitVec.ofNat 256 g).toNat g 0
    (callBaseCost fork (decide (tok ∉ ss.accessedAddresses)) +
      routeCost fork (ss.accessedAddresses.insert tok) route)

/-- The memory at the first CALL: the selector of `balanceOf(address)` at 128, the address of
WBTC at 132. The free memory pointer (word 64) is 128. 192 bytes. -/
def rcMem1 (message : Message fork) : ByteArray :=
  memoryWrite (memoryExtend (memW [(0 : U256), (0 : U256), (128 : U256), (0 : U256),
    (50942633119752846454219349998365661925608737367104304655302372697894809501696 : U256)]) 32)
    132 (wordBytes message.currentTarget.toU256)

/-- The memory after a CALL with the output range 128..160: the first 32 bytes (or fewer) of the
output of the child are written at 128. -/
def rcOut (m out : ByteArray) : ByteArray :=
  memoryWrite m (128 : U256).toNat (out.extract 0 (min (32 : U256).toNat out.size))

/-- The owner word that the second message carries: bits 8..167 of slot 5 of the state `S`. -/
def rcOwner (message : Message fork) (S : State.TransactionState) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (bitwiseAnd (div (storageAt S message.currentTarget (5 : U256)) (256 : U256))
        (1461501637330902918203684832716283019655932542975 : U256)))

/-- The memory at the second CALL, from the memory `mem` after the first call: the selector of
`transfer(address,uint256)` at 128, the owner at 132, the balance `bal` at 164. 224 bytes. -/
def rcMem2 (message : Message fork) (S : State.TransactionState) (mem : ByteArray) (bal : U256) :
    ByteArray :=
  memoryWrite (memoryExtend (memoryWrite (memoryExtend (memoryWrite (memoryExtend mem 0) 128
    (wordBytes (76450787359836037641860180984291677749980919077056822294353438043884394381312 :
      U256))) 0) 132 (wordBytes (rcOwner message S))) 32) 164 (wordBytes bal)

/-! ## Small facts -/

/-- A bound on the size of a memory with a known size. -/
theorem le_size_of {m : ByteArray} {sz a : Nat} (h : m.size = sz) (ha : a ≤ sz) : a ≤ m.size :=
  h ▸ ha

/-- The state of a frame that takes in a child with no error is the state of the child. -/
theorem incorporate_state_none {caller child : Evm fork Nat} (herr : child.error = none) :
    (incorporateChild fork caller child).state = child.state := by
  simp [incorporateChild, herr]

/-- The test `RETURNDATASIZE < 32` failed: at least 32 bytes came back. -/
theorem size_ge_of_not_lt {k : Nat}
    (h : isZero (lessThan (BitVec.ofNat 256 k) (32 : U256)) ≠ 0) : 32 ≤ k := by
  rcases Nat.lt_or_ge k 32 with hk | hk
  · exfalso
    apply h
    have e : (BitVec.ofNat 256 k).toNat = k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans hk (by decide))
    have h32 : (32 : U256).toNat = 32 := rfl
    have l : lessThan (BitVec.ofNat 256 k) (32 : U256) = 1 := by
      unfold lessThan
      rw [e, h32, if_pos hk]
    rw [l]
    decide
  · exact hk

/-- The flag of a child, 1 on top: the child ended with no error. -/
theorem error_none_of_flag {child : Evm fork Nat}
    (h : (if child.error.isNone then (1 : U256) else 0) = 1) : child.error = none := by
  cases herr : child.error with
  | none => rfl
  | some e =>
    rw [herr] at h
    exact absurd h (by simp)

/-- The size of the memory after the write of the output. -/
theorem size_rcOut {m : ByteArray} (out : ByteArray) {sz : Nat} (hs : m.size = sz)
    (hsz : 160 ≤ sz) : (rcOut m out).size = sz :=
  (size_callWrite out (o := 128) (n := 32) (by omega)).trans hs

/-- The write of the output keeps the free memory pointer. -/
theorem fp_rcOut {m : ByteArray} (out : ByteArray) {sz : Nat} {fp : U256} (hs : m.size = sz)
    (hsz : 160 ≤ sz) (hfp : loadWord (memoryReadBytes m 64 32) 0 32 = fp) :
    loadWord (memoryReadBytes (rcOut m out) 64 32) 0 32 = fp := by
  show loadWord (memoryReadBytes (memoryWrite m 128 (out.extract 0 (min 32 out.size))) 64 32)
    0 32 = fp
  rw [read_callWrite_other out (o := 128) (n := 32) (a := 64) (k := 32) (by omega)
    (.inl (by omega))]
  exact hfp

/-- With at least 32 bytes of output, the word at 128 is the first word of the output. -/
theorem word_rcOut {m : ByteArray} (out : ByteArray) {sz : Nat} (hs : m.size = sz)
    (hsz : 160 ≤ sz) (hout : 32 ≤ out.size) :
    loadWord (memoryReadBytes (rcOut m out) 128 32) 0 32 =
      loadWord (memoryReadBytes out 0 32) 0 32 :=
  load_callWrite_word out (o := 128) (by omega) hout

/-! ## The code after each CALL -/

/-- The code after the first CALL (1537..1561), for a run that ends with no error. -/
theorem rc_tail1 (hfork : .byzantium ≤ fork) {flag a b c fp : U256} {rest : List U256}
    {rd mem : ByteArray} {sz gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hs : mem.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT) (hflag : flag = 0 ∨ flag = 1)
    {l s : Evm fork Nat}
    (start : Logic.At CODE message 1537 (flag :: a :: b :: c :: rest) mem gas st ss rd l)
    (e : EndsL runChild l s) (hok : s.error = none) :
    flag = 1 ∧ 39 ≤ gas ∧
    ∃ z, At CODE message 1562 (BitVec.ofNat 256 rd.size :: fp :: rest) mem (gas - 39) st ss z ∧
      z.returnData = rd ∧ EndsL runChild z s :=
  callTail_ok (pc := 1537) (D := (1553 : U256)) hfork (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by decide) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by valid_dest) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) hs hfit hfp hrest hflag start e hok

/-- The code after the second CALL (3212..3236), for a run that ends with no error. -/
theorem rc_tail2 (hfork : .byzantium ≤ fork) {flag a b c fp : U256} {rest : List U256}
    {rd mem : ByteArray} {sz gas : Nat} {st : State.TransactionState} {ss : Substate}
    (hs : mem.size = sz) (hfit : 96 ≤ sz)
    (hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = fp)
    (hrest : rest.length + 7 < STACK_LIMIT) (hflag : flag = 0 ∨ flag = 1)
    {l s : Evm fork Nat}
    (start : Logic.At CODE message 3212 (flag :: a :: b :: c :: rest) mem gas st ss rd l)
    (e : EndsL runChild l s) (hok : s.error = none) :
    flag = 1 ∧ 39 ≤ gas ∧
    ∃ z, At CODE message 3237 (BitVec.ofNat 256 rd.size :: fp :: rest) mem (gas - 39) st ss z ∧
      z.returnData = rd ∧ EndsL runChild z s :=
  callTail_ok (pc := 3212) (D := (3228 : U256)) hfork (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by decide) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by valid_dest) (by code_fact) (by code_fact)
    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)
    (by code_fact) hs hfit hfp hrest hflag start e hok

/-! ## From the start to the code after the first call -/

/-- A run of `reclaimToken` that ends with no error, up to the frame after the first call
(pc 1562): no value, the caller is the owner, the token has code, one message was sent
(`balanceOf(address(this))` to the token), its child ended with no error, and the run goes on
from 1562 with the size of the output on top, the output written at memory 128, the state of
the child and the exact gas. -/
theorem ok_reclaim_first (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
    equal message.caller.toU256
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) ≠ 0 ∧
    ∃ (c : ByteArray) (route : Route) (caller : Evm fork Nat) (msg : Message fork)
      (child : Evm fork Nat) (sel : U256) (z : Evm fork Nat),
      state.getCode (state.getAccount (rcToken message)).codeHash = .ok c ∧
      BitVec.ofNat 256 c.size ≠ 0 ∧
      SentVia message (rcSt message state (rcToken message)) (rcToken message) caller msg ∧
      caller.substate = rcCallerSub substate message.currentTarget (rcToken message) route ∧
      msg.data = memoryReadBytes (rcMem1 message) 128 36 ∧
      msg.gas = (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
        (rcToken message) route
        (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).subCall ∧
      Ran runChild caller msg child ∧ child.error = none ∧
      At CODE message 1562
        [BitVec.ofNat 256 child.output.size, (128 : U256), (0 : U256), rcT message, (570 : U256),
          sel]
        (rcOut (rcMem1 message) child.output)
        (rcGas fork substate message.currentTarget (rcToken message) 567 gas -
          (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
            (rcToken message) route
            (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).cost +
          child.gas - 39)
        child.state (incorporateChild fork caller child).substate z ∧
      EndsL runChild z s := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨hval, hown, -, z0, hz0, w0, hr0⟩ := ok_reclaimToken hfork hsize' hsel start hrun hok
  have msz := reclaimToken_p2_mem (message := message)
  refine ⟨hval, hown, ?_⟩
  have hT : toAddressMasked (bitwiseAnd (bitwiseAnd (loadWord message.data 4 32)
      (1461501637330902918203684832716283019655932542975 : U256))
      (1461501637330902918203684832716283019655932542975 : U256)) = rcToken message := by
    rw [and_mask_comm, toAddressMasked_mask]
    rfl
  -- EXTCODESIZE
  rcases extcodesize_outcome hfork (by code_fact) (by code_fact) hz0 w0 hr0 with
    herr | ⟨c, z1, hc, -, hz1, w1, hr1⟩
  · exact absurd hok herr
  simp only [hT] at hc hz1
  -- the test of the size
  obtain ⟨hcs, -, z2, hz2, w2, hr2⟩ := ok_reclaimCodeA hfork msz.1 msz.2.1 hz1 ⟨w1, hr1⟩ hok
  -- GAS
  rcases gas_outcome (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz2 w2 hr2 with
    herr | ⟨z3, hz3, w3, hr3⟩
  · exact absurd hok herr
  -- CALL
  rcases callOut_outcome hfork hglam (by code_fact) (by code_fact)
      (le_size_of msz.1 (by decide)) (le_size_of msz.1 (by decide)) hz3 w3 hr3 with
    herr | ⟨g, st, ss, z4, hz4, -, w4, hr4⟩ |
    ⟨c', route, caller, msg, child, z4, -, -, hvia, css, md, mg, hran, -, hz4, w4, hr4⟩
  · exact absurd hok herr
  · exact absurd (rc_tail1 hbyz msz.1 (by decide) msz.2.1 (by simp [STACK_LIMIT]) (.inl rfl) hz4 ⟨w4, hr4⟩
      hok).1 (by decide)
  simp only [hT] at hvia css mg hz4
  have hsW := size_rcOut child.output msz.1 (by decide)
  have hfpW := fp_rcOut child.output msz.1 (by decide) msz.2.1
  obtain ⟨hflag, -, z5, hz5, -, e5⟩ := rc_tail1 hbyz hsW (by decide) hfpW
    (by simp [STACK_LIMIT])
    (by by_cases h : child.error.isNone <;> simp [h]) hz4 ⟨w4, hr4⟩ hok
  have herr : child.error = none := error_none_of_flag hflag
  rw [incorporate_state_none herr] at hz5
  exact ⟨c, route, caller, msg, child, _, z5, hc,
    isZero_eq_zero_iff.mp (isZero_ne_zero_iff.mp hcs), hvia, css, md, mg, hran, herr, hz5, e5⟩

/-! ## From the code after the first call to the end -/

/-- A run from the frame after the first call (pc 1562) that ends with no error: at least 32
bytes came back, the owner is read from slot 5 of the state of the frame, the token has code,
one message was sent (`transfer(owner, bal)` to the token), its child ended with no error and
returned at least 32 bytes with a first word that is not 0, and the frame stopped with no
output, the state of the child and the exact gas. -/
theorem ok_reclaim_second {n t sel bal : U256} {mem : ByteArray} (hfork : .berlin ≤ fork)
    (hglam : fork < .glamsterdam)
    (hmem_size : mem.size = 192)
    (hmem_fp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hmem_w128 : loadWord (memoryReadBytes mem 128 32) 0 32 = bal)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 1562 [n, (128 : U256), (0 : U256), t, (570 : U256), sel] mem gas
      state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    isZero (lessThan n (32 : U256)) ≠ 0 ∧
    ∃ (c : ByteArray) (route : Route) (caller : Evm fork Nat) (msg : Message fork)
      (child : Evm fork Nat),
      state.getCode (state.getAccount (toAddressMasked t)).codeHash = .ok c ∧
      BitVec.ofNat 256 c.size ≠ 0 ∧
      SentVia message (rcSt message state (toAddressMasked t)) (toAddressMasked t) caller msg ∧
      caller.substate = rcCallerSub substate message.currentTarget (toAddressMasked t) route ∧
      msg.data = memoryReadBytes (rcMem2 message state mem bal) 128 68 ∧
      msg.gas = (rcCallGas fork (rcSub substate message.currentTarget (toAddressMasked t))
        (toAddressMasked t) route
        (rcGas fork substate message.currentTarget (toAddressMasked t) 514 gas)).subCall ∧
      Ran runChild caller msg child ∧ child.error = none ∧ 32 ≤ child.output.size ∧
      loadWord (memoryReadBytes child.output 0 32) 0 32 ≠ 0 ∧
      s.state = child.state ∧ s.substate = (incorporateChild fork caller child).substate ∧
      s.output = ByteArray.empty ∧
      s.gas = rcGas fork substate message.currentTarget (toAddressMasked t) 514 gas -
        (rcCallGas fork (rcSub substate message.currentTarget (toAddressMasked t))
          (toAddressMasked t) route
          (rcGas fork substate message.currentTarget (toAddressMasked t) 514 gas)).cost +
        child.gas - 39 - 79 := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨hn, -, z0, hz0, w0, hr0⟩ :=
    ok_reclaimMid hfork hmem_size hmem_fp hmem_w128 start hrun hok
  have msz := reclaimMid_p1_mem (message := message) (state := state) (n := n) (t := t)
    (sel := sel) hmem_size hmem_fp hmem_w128
  refine ⟨hn, ?_⟩
  -- EXTCODESIZE
  rcases extcodesize_outcome hfork (by code_fact) (by code_fact) hz0 w0 hr0 with
    herr | ⟨c, z1, hc, -, hz1, w1, hr1⟩
  · exact absurd hok herr
  simp only [toAddressMasked_mask] at hc hz1
  -- the test of the size
  obtain ⟨hcs, -, z2, hz2, w2, hr2⟩ := ok_reclaimCodeB hfork msz.1 msz.2.1 hz1 ⟨w1, hr1⟩ hok
  -- GAS
  rcases gas_outcome (by code_fact) (by code_fact) (by simp [STACK_LIMIT]) hz2 w2 hr2 with
    herr | ⟨z3, hz3, w3, hr3⟩
  · exact absurd hok herr
  -- CALL
  rcases callOut_outcome hfork hglam (by code_fact) (by code_fact)
      (le_size_of msz.1 (by decide)) (le_size_of msz.1 (by decide)) hz3 w3 hr3 with
    herr | ⟨g, st, ss, z4, hz4, -, w4, hr4⟩ |
    ⟨c', route, caller, msg, child, z4, -, -, hvia, css, md, mg, hran, -, hz4, w4, hr4⟩
  · exact absurd hok herr
  · exact absurd (rc_tail2 hbyz msz.1 (by decide) msz.2.1 (by simp [STACK_LIMIT]) (.inl rfl) hz4 ⟨w4, hr4⟩
      hok).1 (by decide)
  simp only [toAddressMasked_mask] at hvia css mg hz4
  have hsW := size_rcOut child.output msz.1 (by decide)
  have hfpW := fp_rcOut child.output msz.1 (by decide) msz.2.1
  obtain ⟨hflag, -, z5, hz5, -, e5⟩ := rc_tail2 hbyz hsW (by decide) hfpW
    (by simp [STACK_LIMIT])
    (by by_cases h : child.error.isNone <;> simp [h]) hz4 ⟨w4, hr4⟩ hok
  have herr : child.error = none := error_none_of_flag hflag
  obtain ⟨hn2, hret, -, hout, hsg, hsst, hsss⟩ := ok_reclaimEnd hfork hsW hfpW rfl hz5 e5 hok
  have h32 : 32 ≤ child.output.size := size_ge_of_not_lt hn2
  rw [word_rcOut child.output msz.1 (by decide) h32] at hret
  exact ⟨c, route, caller, msg, child, hc,
    isZero_eq_zero_iff.mp (isZero_ne_zero_iff.mp hcs), hvia, css, md, mg, hran, herr, h32,
    isZero_eq_zero_iff.mp (isZero_ne_zero_iff.mp hret), hsst.trans (incorporate_state_none herr),
    hsss, hout, hsg⟩

/-! ## The whole function -/

/-- EVERY run of `reclaimToken(address token)` that ends with no error, for every runner.

The value is 0 and the caller is the owner of slot 5. The frame sent exactly two messages, both
to the token (`rcToken`, any address, WBTC itself included), both with value 0:

1. `msg1` from the state before the call (plus records of reads, `rcSt`), with the 36 bytes
   `balanceOf(address(this))` (`rcMem1`); its child `child1` ended with no error and returned at
   least 32 bytes.
2. `msg2` from the state that `child1` left (plus records of reads), with the 68 bytes
   `transfer(owner, bal)` (`rcMem2`): the owner is bits 8..167 of slot 5 of the state that
   `child1` left (`rcOwner`: read again after the first call), and `bal` is the first word that
   `child1` returned; its child `child2` ended with no error and returned at least 32 bytes,
   and the first word is not 0.

The token had code before each call. The frame ends with no output, with the state that
`child2` left and the substate after `child2` was taken in. The gas of each message (63/64 of
all gas left) and the gas at the end are exact formulas in the gas that the children left. -/
theorem ok_reclaim (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0x17ffc320)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    isZero message.value ≠ 0 ∧
    equal message.caller.toU256
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) ≠ 0 ∧
    ∃ (c1 : ByteArray) (route1 : Route) (caller1 : Evm fork Nat) (msg1 : Message fork)
      (child1 : Evm fork Nat) (c2 : ByteArray) (route2 : Route) (caller2 : Evm fork Nat)
      (msg2 : Message fork) (child2 : Evm fork Nat),
      -- the first call
      state.getCode (state.getAccount (rcToken message)).codeHash = .ok c1 ∧
      BitVec.ofNat 256 c1.size ≠ 0 ∧
      SentVia message (rcSt message state (rcToken message)) (rcToken message) caller1 msg1 ∧
      caller1.substate = rcCallerSub substate message.currentTarget (rcToken message) route1 ∧
      msg1.data = memoryReadBytes (rcMem1 message) 128 36 ∧
      msg1.gas = (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
        (rcToken message) route1
        (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).subCall ∧
      Ran runChild caller1 msg1 child1 ∧ child1.error = none ∧ 32 ≤ child1.output.size ∧
      -- the second call
      child1.state.getCode (child1.state.getAccount (rcToken message)).codeHash = .ok c2 ∧
      BitVec.ofNat 256 c2.size ≠ 0 ∧
      SentVia message (rcSt message child1.state (rcToken message)) (rcToken message) caller2
        msg2 ∧
      caller2.substate = rcCallerSub (incorporateChild fork caller1 child1).substate
        message.currentTarget (rcToken message) route2 ∧
      msg2.data = memoryReadBytes (rcMem2 message child1.state
        (rcOut (rcMem1 message) child1.output)
        (loadWord (memoryReadBytes child1.output 0 32) 0 32)) 128 68 ∧
      msg2.gas = (rcCallGas fork
        (rcSub (incorporateChild fork caller1 child1).substate message.currentTarget
          (rcToken message))
        (rcToken message) route2
        (rcGas fork (incorporateChild fork caller1 child1).substate message.currentTarget
          (rcToken message) 514
          (rcGas fork substate message.currentTarget (rcToken message) 567 gas -
            (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
              (rcToken message) route1
              (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).cost +
            child1.gas - 39))).subCall ∧
      Ran runChild caller2 msg2 child2 ∧ child2.error = none ∧ 32 ≤ child2.output.size ∧
      loadWord (memoryReadBytes child2.output 0 32) 0 32 ≠ 0 ∧
      -- the end
      s.state = child2.state ∧ s.substate = (incorporateChild fork caller2 child2).substate ∧
      s.output = ByteArray.empty ∧
      s.gas = rcGas fork (incorporateChild fork caller1 child1).substate message.currentTarget
          (rcToken message) 514
          (rcGas fork substate message.currentTarget (rcToken message) 567 gas -
            (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
              (rcToken message) route1
              (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).cost +
            child1.gas - 39) -
        (rcCallGas fork
          (rcSub (incorporateChild fork caller1 child1).substate message.currentTarget
            (rcToken message))
          (rcToken message) route2
          (rcGas fork (incorporateChild fork caller1 child1).substate message.currentTarget
            (rcToken message) 514
            (rcGas fork substate message.currentTarget (rcToken message) 567 gas -
              (rcCallGas fork (rcSub substate message.currentTarget (rcToken message))
                (rcToken message) route1
                (rcGas fork substate message.currentTarget (rcToken message) 567 gas)).cost +
              child1.gas - 39))).cost +
        child2.gas - 39 - 79 := by
  obtain ⟨hval, hown, c1, route1, caller1, msg1, child1, sel, z, hc1, hcs1, hvia1, css1, md1, mg1,
    hran1, herr1, hz, ez⟩ := ok_reclaim_first hfork hglam hsize' hsel start hrun hok
  have msz := reclaimToken_p2_mem (message := message)
  have hsW : (rcOut (rcMem1 message) child1.output).size = 192 :=
    size_rcOut child1.output msz.1 (by decide)
  have hfpW : loadWord (memoryReadBytes (rcOut (rcMem1 message) child1.output) 64 32) 0 32 =
      (128 : U256) := fp_rcOut child1.output msz.1 (by decide) msz.2.1
  obtain ⟨hn, c2, route2, caller2, msg2, child2, hc2, hcs2, hvia2, css2, md2, mg2, hran2, herr2,
    h32, hne, hst, hss, hout, hsg⟩ := ok_reclaim_second hfork hglam hsW hfpW rfl hz ez hok
  have h32a : 32 ≤ child1.output.size := size_ge_of_not_lt hn
  have hw : loadWord (memoryReadBytes (rcOut (rcMem1 message) child1.output) 128 32) 0 32 =
      loadWord (memoryReadBytes child1.output 0 32) 0 32 :=
    word_rcOut child1.output msz.1 (by decide) h32a
  rw [hw] at md2
  exact ⟨hval, hown, c1, route1, caller1, msg1, child1, c2, route2, caller2, msg2, child2,
    hc1, hcs1, hvia1, css1, md1, mg1, hran1, herr1, h32a, hc2, hcs2, hvia2, css2, md2, mg2,
    hran2, herr2,
    h32, hne, hst, hss, hout, hsg⟩

end WbtcVerify

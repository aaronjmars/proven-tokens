import WbtcVerify.Wbtc.Sanity.ReclaimLib
import WbtcVerify.Wbtc.Gen.PReclaimToken
import WbtcVerify.Wbtc.Gen.PReclaimCodeA
import WbtcVerify.Wbtc.Gen.PReclaimMid
import WbtcVerify.Wbtc.Gen.PReclaimCodeB
import WbtcVerify.Wbtc.Gen.PReclaimEnd
import TokenKit.Evm.CallOutcome

/-!
# The pieces of a run of reclaimToken, for any message runner

Written by hand (not generated). `Sanity/Reclaim*.lean` puts these pieces together for concrete
callees under EthLib's real runner.

Proved, for the code of WBTC and every message runner `runChild`:
- `Goes`: the loop of the interpreter gives the same result from two frames. `Goes.of_reaches`,
  `Goes.trans`, `Goes.result`.
- `call_run`: the step of a CALL with no value whose ranges are inside the memory and that asks
  for all the gas: the message it sends (`Sent`), and the frame after the child, with the return
  data of the child.
- `after1_ok`, `after2_ok`: the opcodes after each of the two CALLs when the call succeeded
  (1537..1561 and 3212..3236): the flag check, four POPs, MLOAD 0x40, RETURNDATASIZE.
- `bubble1`: the opcodes 1537..1552 when the first call failed with 32 bytes of return data: the
  frame reverts with these 32 bytes.
- `seg1`: from pc 0 to the frame after the first CALL (balanceOf). `seg2`: from there to the
  frame after the second CALL (transfer). `seg3_ok`, `seg3_zero`: from there to the end (STOP, or
  a revert when the returned word is 0). `seg2_short`: the revert when the first call returned
  fewer than 32 bytes. `seg_nocode`: the revert when the token has no code. `seg_notowner`: the
  revert when the caller is not the owner.

Assumed: only the hypotheses written in each statement (fork from Berlin and before Glamsterdam,
the fields of the message, enough gas, gas under 2^64). Not covered here: a first call that
fails with return data of another size than 32 bytes, and a second call that fails.
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

/-! ## Two frames with the same result -/

/-- The loop of the interpreter gives the same result from `a` and from `b`. -/
def Goes (runChild : MessageRunner fork Nat bound) (a b : Evm fork Nat) : Prop :=
  ∀ within : GasMeter.gasHeld a.gas ≤ bound, ∃ w : GasMeter.gasHeld b.gas ≤ bound,
    Evm.runFrame (step fork) (step_decreases fork) bound runChild a within =
      Evm.runFrame (step fork) (step_decreases fork) bound runChild b w

theorem Goes.trans {runChild : MessageRunner fork Nat bound} {a b c : Evm fork Nat}
    (h1 : Goes runChild a b) (h2 : Goes runChild b c) : Goes runChild a c := fun within =>
  let ⟨w, e⟩ := h1 within
  let ⟨w2, e2⟩ := h2 w
  ⟨w2, e.trans e2⟩

/-- Steps with no call keep the result of the loop. -/
theorem Goes.of_reaches (runChild : MessageRunner fork Nat bound) {a b : Evm fork Nat}
    (h : Reaches (Step fork) a b) : Goes runChild a b := fun within =>
  ⟨Nat.le_trans (h.gasHeld_le Step.gasHeld_le) within,
    runFrame_eq_of_reaches Step.gasHeld_le Step.runFrame_eq h within⟩

/-- A frame that goes to a stopped frame: the loop returns the stopped frame. -/
theorem Goes.result {runChild : MessageRunner fork Nat bound} {a s : Evm fork Nat}
    (h : Goes runChild a s) (hs : s.running = false) (within : GasMeter.gasHeld a.gas ≤ bound) :
    Evm.runFrame (step fork) (step_decreases fork) bound runChild a within = .ok s := by
  obtain ⟨w, e⟩ := h within
  rw [e]
  exact runFrame_of_running_eq_false hs

/-! ## The step of the CALL -/

/-- The fields of a message that a CALL with no value sends. -/
def Sent (msg : Message fork) (sender to : Address) (code data : ByteArray) (depth : Nat)
    (static : Bool) : Prop :=
  msg.caller = sender ∧ msg.currentTarget = to ∧ msg.target = some to ∧
    msg.codeAddress = some to ∧ msg.code = code ∧ msg.data = data ∧ msg.value = 0 ∧
    msg.depth = depth ∧ msg.isStatic = static

/-- A substate with one more accessed address. -/
abbrev warm (ss : Substate) (A : Address) : Substate :=
  { ss with accessedAddresses := ss.accessedAddresses.insert A }

/-- Two ranges inside the memory need no growth. -/
theorem extendMemory_in2 {size : Nat} {i isz o osz : U256} (hin : i.toNat + isz.toNat ≤ size)
    (hout : o.toNat + osz.toNat ≤ size) : extendMemory size [(i, isz), (o, osz)] = ⟨0, 0⟩ :=
  extendMemory_eq_zero size _ fun p hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans hin (le_ceil32 size)))
    · rw [List.mem_singleton.mp hp]
      exact .inr (ceil32_le (ceil32_mod size) (Nat.le_trans hout (le_ceil32 size)))

/-- A number under 2^64 is the number of its word. -/
theorem toNat_ofNat_of_lt64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 256 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by decide))

/-- The step of a CALL with no value, whose ranges are inside the memory, that asks for at least
all the gas of the frame, to an address with the code `c`: the frame sends a message with all the
gas but the price of the access and one 64th, and after any child that the runner gives, the
frame goes on at the next opcode with the flag of the child on the stack, the output of the
child written at the output range, and the output of the child as return data. -/
theorem call_run (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {code : ByteArray} {message : Message fork} {pc : Nat} {g a i isz o osz : U256}
    {rest : List U256} {mem : ByteArray} {gas : Nat} {state : State.TransactionState}
    {substate : Substate} {z : Evm fork Nat}
    (hz : UsdtVerify.At code message pc (g :: a :: 0 :: i :: isz :: o :: osz :: rest) mem gas
      state substate z)
    (hstep : step fork z = callStep .call z)
    (hext : extendMemory mem.size [(i, isz), (o, osz)] = ⟨0, 0⟩)
    {c : ByteArray}
    (hcode : state.getCode (state.getAccount (toAddressMasked a)).codeHash = .ok c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hrest : rest.length < STACK_LIMIT)
    (hgas : 2600 ≤ gas) (hask : gas ≤ g.toNat)
    (runChild : MessageRunner fork Nat bound) (hb : gas ≤ bound) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (gas - 2600) / 2 ≤ msg.gas ∧
      caller.state = (state.recordAccountRead (toAddressMasked a)).recordAccountRead
        message.currentTarget ∧
      caller.substate = warm substate (toAddressMasked a) ∧
      Sent msg message.currentTarget (toAddressMasked a) c
        (memoryReadBytes mem i.toNat isz.toNat) (message.depth + 1) message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (gas - 2600) / 64 ≤ after.gas ∧ Goes runChild z after ∧
          Logic.At code message (pc + 1) ((if child.1.error.isNone then 1 else 0) :: rest)
            (memoryWrite mem o.toNat
              (child.1.output.extract 0 (min osz.toNat child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have htw : Fork.tangerineWhistle ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨zc, zj, zm, zp, zst, zmem, zg, zrun, zerr, zout, zs, zss⟩ := id hz
  have h0 : extendMemory z.memory.size [(i, isz), (o, osz)] = ⟨0, 0⟩ := by
    rw [zmem]
    exact hext
  have h0c : (extendMemory z.memory.size [(i, isz), (o, osz)]).cost = 0 := by rw [h0]
  have h0e : (extendMemory z.memory.size [(i, isz), (o, osz)]).expandBy = 0 := by rw [h0]
  have hE : 100 ≤ callBaseCost fork
        (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) ∧
      callBaseCost fork (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) ≤ 2600 := by
    rw [callBaseCost_of_berlin hfork hglam]
    split <;> omega
  generalize hEdef : callBaseCost fork
    (decide (toAddressMasked a ∉ z.substate.accessedAddresses)) = E at hE
  obtain ⟨cl, msg, hsent, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ :=
    callStep_call hfork zst (by rw [zs]; exact hcode) hdel (by rw [zm]; exact hdepth)
      (by rw [h0c, hEdef, zg]; omega)
  rw [h0c, hEdef] at m1 c7
  rw [h0e, memoryExtend_zero] at c6 m7
  obtain ⟨k1, k2⟩ := mcg_exact (fork := fork) htw (asked := g.toNat) (gas := z.gas) (E := E)
    (by rw [zg]; omega) (by rw [zg]; omega)
  rw [k1, zg] at m1
  rw [k2, zg] at c7
  have hlt : msg.gas < bound := by
    rw [m1]
    omega
  refine ⟨cl, msg, hlt, by rw [m1]; omega, by rw [c11, zs, zm], by rw [c12, zss],
    ⟨by rw [m2, zm], m3, m4, m5, m6, by rw [m7, zmem], m8, by rw [m9, zm], by rw [m10, zm]⟩,
    ?_⟩
  intro lt child hch
  obtain ⟨after, hres, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ :=
    resumeCall_eq (fork := fork) (caller := cl) (child := child.1) (o := o) (osz := osz)
      (by rw [c5]; exact hrest)
  refine ⟨after, by rw [a7, c7]; omega,
    fun within => ⟨_, runFrame_of_step_eq_child zrun (by rw [hstep]; exact hsent) lt hch hres⟩,
    a1.trans (c1.trans zc), a2.trans (c2.trans zj), a3.trans (c3.trans zm),
    by rw [a4, c4, zp], by rw [a5, c5], by rw [a6, c6, zmem], rfl, a8.trans (c8.trans zrun),
    a9.trans (c9.trans zerr), a10.trans (c10.trans zout), a11, a12, a13⟩

/-! ## Rules with the return data of the frame -/

/-- A frame is also a frame with an equal program counter, stack, memory and gas. -/
theorem lre {code : ByteArray} {message : Message fork} {p p2 : Nat} {s s2 : List U256}
    {m m2 : ByteArray} {g g2 : Nat} {st : State.TransactionState} {ss : Substate}
    {rd : ByteArray} (hp : p = p2) (hs : s = s2) (hm : m = m2) (hg : g = g2) :
    Logic.Hoare fork (Logic.At code message p s m g st ss rd)
      (Logic.At code message p2 s2 m2 g2 st ss rd) := by
  subst hp hs hm hg
  exact Triple.of_imp fun _ h => h

/-- RETURNDATACOPY of the 32 bytes of the return data to the start of a memory that holds
them. -/
theorem copy32 (hbyz : .byzantium ≤ fork) {code : ByteArray} {message : Message fork} {pc : Nat}
    {a b n : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3e) (ha : a = 0) (hb : b = 0) (hn : n = 32)
    (hrd : rd.size = 32) (hm : 32 ≤ mem.size) (hg : 6 ≤ gas) :
    Logic.Hoare fork (Logic.At code message pc (a :: b :: n :: rest) mem gas st ss rd)
      (Logic.At code message (pc + 1) rest (memoryWrite mem 0 (memoryReadBytes rd 0 32))
        (gas - 6) st ss rd) := by
  subst ha hb hn
  have he := extendMemory_of_le (size := mem.size) (start := (0 : U256)) (length := (32 : U256))
    (by show 0 + 32 ≤ mem.size; omega)
  have hcost : (extendMemory mem.size [((0 : U256), (32 : U256))]).cost = 0 := by rw [he]
  have hexp : (extendMemory mem.size [((0 : U256), (32 : U256))]).expandBy = 0 := by rw [he]
  have hwc : wordCount (32 : U256).toNat = 1 := by decide
  have r := (returndatacopyG (fork := fork) hbyz (code := code) (message := message) (pc := pc)
    (start := 0) (offset := 0) (size := 32) (rest := rest) (returnData := rd) (memory := mem)
    (gas := gas) (state := st) (substate := ss) hlt hbyte (by rw [hrd]; decide)
    (by rw [hcost, hwc]; omega)).toHoare
  rw [hcost, hexp, hwc, memoryExtend_zero] at r
  exact r

/-- REVERT with the first 32 bytes of a memory that holds them. -/
theorem revert32 (hbyz : .byzantium ≤ fork) {code : ByteArray} {message : Message fork}
    {pc : Nat} {a n : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) (ha : a = 0) (hn : n = 32)
    (hm : 32 ≤ mem.size) :
    Logic.Spec fork (Logic.At code message pc (a :: n :: rest) mem gas st ss rd)
      (Logic.Halted true (memoryReadBytes mem 0 32) (gas - 0) st ss) := by
  subst ha hn
  have he := extendMemory_of_le (size := mem.size) (start := (0 : U256)) (length := (32 : U256))
    (by show 0 + 32 ≤ mem.size; omega)
  have hcost : (extendMemory mem.size [((0 : U256), (32 : U256))]).cost = 0 := by rw [he]
  have hexp : (extendMemory mem.size [((0 : U256), (32 : U256))]).expandBy = 0 := by rw [he]
  have r := Logic.revert (fork := fork) hbyz (code := code) (message := message) (pc := pc)
    (start := 0) (size := 32) (rest := rest) (memory := mem) (gas := gas) (state := st)
    (substate := ss) (returnData := rd) hlt hbyte (by rw [hcost]; omega)
  rw [hcost, hexp, memoryExtend_zero] at r
  exact r

local macro "lstep " r:term : tactic => `(tactic| refine Triple.seq $r ?_)

set_option hygiene false in
/-- The opcodes after a CALL that succeeded, up to RETURNDATASIZE; `d` is the destination of the
JUMPI. -/
local macro "after_tac " d:term:max : tactic => `(tactic| (
  lstep Logic.unary (byte := 0x15) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) instruction_iszero (by gas_ok)
  lstep Logic.dup1 (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.unary (byte := 0x15) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) instruction_iszero (by gas_ok)
  lstep Logic.push (n := 2) (word := $d) (by decide) (by code_fact) (by code_fact)
    (decode_push 2 (by decide)) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.jumpi_taken (by code_fact) (by code_fact) (by gas_ok) (by decide) (by valid_dest)
  lstep Logic.jumpdest (by code_fact) (by code_fact) (by gas_ok)
  lstep Logic.pop (by code_fact) (by code_fact) (by gas_ok)
  lstep Logic.pop (by code_fact) (by code_fact) (by gas_ok)
  lstep Logic.pop (by code_fact) (by code_fact) (by gas_ok)
  lstep Logic.pop (by code_fact) (by code_fact) (by gas_ok)
  lstep Logic.push1 (byte := 0x40) (by code_fact) (by code_fact) (by code_fact) (by gas_ok)
    (by stk_ok)
  lstep (mloadInG (sz := mem.size) rfl (by show 64 + 32 ≤ mem.size; omega) (by code_fact)
    (by code_fact) (by gas_ok)).toHoare
  lstep Logic.returndatasize hbyz (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  exact lre (by decide) rfl rfl (by gas_ok)))

/-- 1537..1561, after the first CALL when it succeeded: the frame is at the size check of the
return data, with the size of the return data and the free memory pointer on the stack. -/
theorem after1_ok (hbyz : .byzantium ≤ fork) {message : Message fork} {x1 x2 x3 : U256}
    {rest : List U256} {mem : ByteArray} {gas : Nat} {st : State.TransactionState}
    {ss : Substate} {rd : ByteArray} (hfit : 96 ≤ mem.size) (hrest : rest.length < 1000)
    (hg : 39 ≤ gas) :
    Logic.Hoare fork (Logic.At CODE message 1537 (1 :: x1 :: x2 :: x3 :: rest) mem gas st ss rd)
      (Logic.At CODE message 1562
        (BitVec.ofNat 256 rd.size :: loadWord (memoryReadBytes mem 64 32) 0 32 :: rest) mem
        (gas - 39) st ss rd) := by
  after_tac (1553 : U256)

/-- 3212..3236, after the second CALL when it succeeded. -/
theorem after2_ok (hbyz : .byzantium ≤ fork) {message : Message fork} {x1 x2 x3 : U256}
    {rest : List U256} {mem : ByteArray} {gas : Nat} {st : State.TransactionState}
    {ss : Substate} {rd : ByteArray} (hfit : 96 ≤ mem.size) (hrest : rest.length < 1000)
    (hg : 39 ≤ gas) :
    Logic.Hoare fork (Logic.At CODE message 3212 (1 :: x1 :: x2 :: x3 :: rest) mem gas st ss rd)
      (Logic.At CODE message 3237
        (BitVec.ofNat 256 rd.size :: loadWord (memoryReadBytes mem 64 32) 0 32 :: rest) mem
        (gas - 39) st ss rd) := by
  after_tac (3228 : U256)

/-- 1537..1552, after the first CALL when it failed with 32 bytes of return data: the frame
reverts with these 32 bytes as its output, and keeps its state. -/
theorem bubble1 (hbyz : .byzantium ≤ fork) {message : Message fork} {rest : List U256}
    {mem : ByteArray} {gas : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hrd : rd.size = 32) (hm : 32 ≤ mem.size) (hrest : rest.length < 1000) (hg : 100 ≤ gas) :
    Logic.Spec fork (Logic.At CODE message 1537 (0 :: rest) mem gas st ss rd)
      (fun s => s.error = some .revert ∧ s.output = memoryReadBytes rd 0 32 ∧ s.state = st ∧
        s.substate = ss) := by
  have hsz : (memoryWrite mem 0 (memoryReadBytes rd 0 32)).size = mem.size :=
    size_memoryWrite (by rw [size_memoryReadBytes (by omega)]; omega)
  have hout : memoryReadBytes (memoryWrite mem 0 (memoryReadBytes rd 0 32)) 0 32 =
      memoryReadBytes rd 0 32 := by
    have h := memoryReadBytes_memoryWrite (memory := mem) (start := 0)
      (value := memoryReadBytes rd 0 32) (by rw [size_memoryReadBytes (by omega)]; omega)
    rw [size_memoryReadBytes (by omega)] at h
    exact h
  lstep Logic.unary (byte := 0x15) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) instruction_iszero (by gas_ok)
  lstep Logic.dup1 (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.unary (byte := 0x15) (by code_fact) (by code_fact)
    (ofByte_of_decode rfl (Fork.frontier_le _)) instruction_iszero (by gas_ok)
  lstep Logic.push (n := 2) (word := (1553 : U256)) (by decide) (by code_fact) (by code_fact)
    (decode_push 2 (by decide)) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.jumpi_of_eq_zero (by code_fact) (by code_fact) (by gas_ok) (by decide)
  lstep Logic.returndatasize hbyz (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.push1 (byte := 0x00) (by code_fact) (by code_fact) (by code_fact) (by gas_ok)
    (by stk_ok)
  lstep Logic.dup1 (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  lstep copy32 hbyz (by code_fact) (by code_fact) rfl rfl (by rw [hrd]; rfl) hrd hm (by gas_ok)
  lstep Logic.returndatasize hbyz (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)
  lstep Logic.push1 (byte := 0x00) (by code_fact) (by code_fact) (by code_fact) (by gas_ok)
    (by stk_ok)
  refine Spec.consequence
    (revert32 hbyz (by code_fact) (by code_fact) rfl (by rw [hrd]; rfl) (by rw [hsz]; exact hm))
    (fun _ h => h) ?_
  rintro s ⟨-, he, ho, -, hs, hss⟩
  exact ⟨by simpa using he, ho.trans hout, hs, hss⟩

/-! ## The pieces of reclaimToken -/

/-- The mask of an address. -/
abbrev MASK : U256 := 1461501637330902918203684832716283019655932542975

/-- The token word of the call data, masked once (as the code keeps it on the stack). -/
abbrev tokW (data : ByteArray) : U256 := bitwiseAnd (loadWord data 4 32) MASK

/-- The address of the token, as the first CALL computes it. -/
abbrev tokA (data : ByteArray) : Address := toAddressMasked (bitwiseAnd (tokW data) MASK)

/-- The address of the token, as the second CALL computes it from the kept word `t`. -/
abbrev tokB (t : U256) : Address := toAddressMasked (bitwiseAnd MASK (bitwiseAnd MASK t))

/-- The memory at the first CALL: the selector of balanceOf at 128, the address of the contract
at 132. -/
abbrev mem1 (C : Address) : ByteArray :=
  memoryWrite (memoryExtend (memW [(0 : U256), (0 : U256), (128 : U256), (0 : U256),
    (50942633119752846454219349998365661925608737367104304655302372697894809501696 : U256)]) 32)
    132 (wordBytes C.toU256)

/-- The owner, as the code reads it from slot 5 before the second CALL. -/
abbrev ownW (S : State.TransactionState) (C : Address) : U256 :=
  bitwiseAnd (div (storageAt S C (5 : U256)) (256 : U256)) MASK

/-- The memory at the second CALL: the selector of transfer at 128, the owner at 132, the
balance at 164. -/
abbrev mem2 (mem : ByteArray) (own bal : U256) : ByteArray :=
  memoryWrite (memoryExtend (memoryWrite (memoryExtend (memoryWrite (memoryExtend mem 0) 128
    (wordBytes
      (76450787359836037641860180984291677749980919077056822294353438043884394381312 : U256)))
    0) 132 (wordBytes (bitwiseAnd MASK (bitwiseAnd MASK own)))) 32) 164 (wordBytes bal)

/-- The state of the frame that waits for a CALL to `A`: slot 5 read, the account `A` read by
EXTCODESIZE and by CALL, and the account of the contract read. -/
abbrev callSt (S : State.TransactionState) (C A : Address) : State.TransactionState :=
  (((readSlot S C (5 : U256)).recordAccountRead A).recordAccountRead A).recordAccountRead C

/-- The substate of the frame that waits for a CALL to `A`: slot 5 and `A` accessed. -/
abbrev callSs (ss : Substate) (C A : Address) : Substate :=
  warm (warm (accessSlot ss C (5 : U256)) A) A

/-- EXTCODESIZE of an address with the code `c`, from Berlin and before Glamsterdam: at most
2600 gas. -/
theorem ext_step (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam) {code : ByteArray}
    {message : Message fork} {pc : Nat} {word : U256} {rest : List U256} {memory : ByteArray}
    {gas : Nat} {state : State.TransactionState} {substate : Substate} {c : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x3b)
    (hcode : state.getCode (state.getAccount (toAddressMasked word)).codeHash = .ok c)
    (hgas : 2600 ≤ gas) {evm : Evm fork Nat}
    (h : UsdtVerify.At code message pc (word :: rest) memory gas state substate evm) :
    ∃ (z : Evm fork Nat) (k : Nat), k ≤ 2600 ∧ Reaches (Step fork) evm z ∧
      UsdtVerify.At code message (pc + 1) (BitVec.ofNat 256 c.size :: rest) memory (gas - k)
        (state.recordAccountRead (toAddressMasked word)) (warm substate (toAddressMasked word))
        z := by
  have hb : externalBaseCost fork (decide (toAddressMasked word ∉ substate.accessedAddresses)) ≤
      2600 := by
    rw [externalBaseCost_of_berlin hfork hglam]
    split <;> omega
  obtain ⟨z, hr, hz⟩ := UsdtVerify.At.extcodesize (fork := fork) hfork hlt hbyte hcode rfl
    (Nat.le_trans hb hgas) evm h
  exact ⟨z, _, hb, hr, hz⟩

/-- From pc 0 to the frame after the first CALL, `token.balanceOf(this)`: the caller is the
owner and the token has code. The message that the CALL sends, and for any child that the runner
gives, the frame at 1537 with the flag of the child, its output at 128 and as return data. -/
theorem seg1 (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize : 4 ≤ message.data.size) (hsize2 : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x17ffc320) (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) ≠
        0)
    {c : ByteArray}
    (hcode : state.getCode (state.getAccount (tokA message.data)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    {gas : Nat} (hg : 8000 ≤ gas) (hg64 : gas < 2 ^ 64)
    (runChild : MessageRunner fork Nat bound) (hb : gas ≤ bound)
    {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas state substate evm) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (gas - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt state message.currentTarget (tokA message.data) ∧
      caller.substate = callSs substate message.currentTarget (tokA message.data) ∧
      Sent msg message.currentTarget (tokA message.data) c
        (memoryReadBytes (mem1 message.currentTarget) 128 36) (message.depth + 1)
        message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (gas - 8000) / 64 ≤ after.gas ∧ Goes runChild evm after ∧
          Logic.At CODE message 1537
            ((if child.1.error.isNone then 1 else 0) ::
              [(164 : U256), (1889567281 : U256), bitwiseAnd (tokW message.data) MASK,
                (0 : U256), tokW message.data, (570 : U256),
                BitVec.ofNat 256 (selector message.data)])
            (memoryWrite (mem1 message.currentTarget) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have hkb : slotCost (coldIn substate message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨z1, hr1, hz1⟩ := (Paths.reclaimToken_p2 (fork := fork) (message := message)
    (state := state) (substate := substate) hfork hsize hsize2 hsel (by rw [hval]; decide) hown
    (gas := gas) (by omega)).toHoare evm start
  generalize slotCost (coldIn substate message.currentTarget (5 : U256)) = k5 at hkb hz1
  obtain ⟨hms, hmfp, -⟩ := Paths.reclaimToken_p2_mem (message := message)
  have hcode1 : (readSlot state message.currentTarget (5 : U256)).getCode
      ((readSlot state message.currentTarget (5 : U256)).getAccount
        (tokA message.data)).codeHash = .ok c := hcode
  obtain ⟨z2, k2, hk2, hr2, hz2⟩ := ext_step hfork hglam (by code_fact) (by code_fact) hcode1
    (by omega) hz1
  obtain ⟨z3, hr3, hz3⟩ := (Paths.reclaimCodeA_p1 (fork := fork) (message := message) hfork hms
    hmfp hcs (gas := gas - (567 + k5) - k2) (by omega)).toHoare z2 hz2
  obtain ⟨z4, hr4, hz4⟩ := UsdtVerify.At.gas_rule (fork := fork) (by code_fact) (by code_fact)
    (show 2 ≤ gas - (567 + k5) - k2 - 25 by omega) (by simp [STACK_LIMIT]) z3 hz3
  have hcode4 : ((readSlot state message.currentTarget (5 : U256)).recordAccountRead
      (tokA message.data)).getCode
      (((readSlot state message.currentTarget (5 : U256)).recordAccountRead
        (tokA message.data)).getAccount (tokA message.data)).codeHash = .ok c := hcode
  obtain ⟨caller, msg, hlt, hlo, hcst, hcss, hsent, hall⟩ := call_run hfork hglam hz4
    (step_at_call hz4 (by code_fact) (by code_fact))
    (extendMemory_in2 (by rw [hms]; decide) (by rw [hms]; decide)) hcode4 hdel hdepth
    (by simp [STACK_LIMIT]) (by omega) (Nat.le_of_eq (toNat_ofNat_of_lt64 (by omega)).symm)
    runChild (by omega)
  refine ⟨caller, msg, hlt, by omega, hcst, hcss, hsent, ?_⟩
  intro lt child hch
  obtain ⟨after, hga, hgo, hat⟩ := hall lt child hch
  exact ⟨after, by omega,
    (Goes.of_reaches runChild (hr1.trans (hr2.trans (hr3.trans hr4)))).trans hgo, hat⟩

/-- From the frame after the first CALL, when it succeeded with at least 32 bytes of return
data, to the frame after the second CALL, `token.transfer(owner, balance)`. `bal` is the word
that the first call wrote at 128. -/
theorem seg2 (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {x1 x2 x3 t sel bal : U256} {mem : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hms : mem.size = 192)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = bal)
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) ≠ 0)
    {c : ByteArray}
    (hcode : st.getCode (st.getAccount (tokB t)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (hdepth : message.depth + 1 ≤ STACK_DEPTH_LIMIT)
    (hg : 8000 ≤ g) (hg64 : g < 2 ^ 64)
    (runChild : MessageRunner fork Nat bound) (hb : g ≤ bound)
    {a : Evm fork Nat}
    (ha : Logic.At CODE message 1537
      (1 :: x1 :: x2 :: x3 :: [(0 : U256), t, (570 : U256), sel]) mem g st ss rd a) :
    ∃ (caller : Evm fork Nat) (msg : Message fork), msg.gas < bound ∧
      (g - 8000) / 2 ≤ msg.gas ∧
      caller.state = callSt st message.currentTarget (tokB t) ∧
      caller.substate = callSs ss message.currentTarget (tokB t) ∧
      Sent msg message.currentTarget (tokB t) c
        (memoryReadBytes (mem2 mem (ownW st message.currentTarget) bal) 128 68)
        (message.depth + 1) message.isStatic ∧
      ∀ (lt : msg.gas < bound)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        runChild caller msg lt = .ok child →
        ∃ after : Evm fork Nat, (g - 8000) / 64 ≤ after.gas ∧ Goes runChild a after ∧
          Logic.At CODE message 3212
            ((if child.1.error.isNone then 1 else 0) ::
              [(196 : U256), (2835717307 : U256), bitwiseAnd MASK (bitwiseAnd MASK t), bal,
                ownW st message.currentTarget, bitwiseAnd MASK t, (1617 : U256), bal, t,
                (570 : U256), sel])
            (memoryWrite (mem2 mem (ownW st message.currentTarget) bal) 128
              (child.1.output.extract 0 (min 32 child.1.output.size)))
            after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate child.1.output after := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  have hkb : slotCost (coldIn ss message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨z1, hr1, hz1⟩ := after1_ok (fork := fork) hbyz (by omega) (by simp) (by omega) a ha
  have hz1b : UsdtVerify.At CODE message 1562
      [BitVec.ofNat 256 rd.size, (128 : U256), (0 : U256), t, (570 : U256), sel] mem (g - 39)
      st ss z1 := by
    have h := At.ofLogic hz1
    rw [hmfp] at h
    exact h
  obtain ⟨z2, hr2, hz2⟩ := (Paths.reclaimMid_p1 (fork := fork) (message := message)
    (state := st) (substate := ss) hfork hms hmfp hw hn (gas := g - 39) (by omega)).toHoare z1
    hz1b
  generalize slotCost (coldIn ss message.currentTarget (5 : U256)) = k5 at hkb hz2
  obtain ⟨hms2, hmfp2, -⟩ := Paths.reclaimMid_p1_mem (message := message) (state := st)
    (n := 0) (t := 0) (sel := 0) (bal := bal) hms hmfp hw
  have hcode1 : (readSlot st message.currentTarget (5 : U256)).getCode
      ((readSlot st message.currentTarget (5 : U256)).getAccount (tokB t)).codeHash = .ok c :=
    hcode
  obtain ⟨z3, k2, hk2, hr3, hz3⟩ := ext_step hfork hglam (by code_fact) (by code_fact) hcode1
    (by omega) hz2
  obtain ⟨z4, hr4, hz4⟩ := (Paths.reclaimCodeB_p1 (fork := fork) (message := message) hfork hms2
    hmfp2 hcs (gas := g - 39 - (514 + k5) - k2) (by omega)).toHoare z3 hz3
  obtain ⟨z5, hr5, hz5⟩ := UsdtVerify.At.gas_rule (fork := fork) (by code_fact) (by code_fact)
    (show 2 ≤ g - 39 - (514 + k5) - k2 - 25 by omega) (by simp [STACK_LIMIT]) z4 hz4
  have hcode5 : ((readSlot st message.currentTarget (5 : U256)).recordAccountRead
      (tokB t)).getCode
      (((readSlot st message.currentTarget (5 : U256)).recordAccountRead
        (tokB t)).getAccount (tokB t)).codeHash = .ok c := hcode
  obtain ⟨caller, msg, hlt, hlo, hcst, hcss, hsent, hall⟩ := call_run hfork hglam hz5
    (step_at_call hz5 (by code_fact) (by code_fact))
    (extendMemory_in2 (by rw [hms2]; decide) (by rw [hms2]; decide)) hcode5 hdel hdepth
    (by simp [STACK_LIMIT]) (by omega) (Nat.le_of_eq (toNat_ofNat_of_lt64 (by omega)).symm)
    runChild (by omega)
  refine ⟨caller, msg, hlt, by omega, hcst, hcss, hsent, ?_⟩
  intro lt child hch
  obtain ⟨after, hga, hgo, hat⟩ := hall lt child hch
  exact ⟨after, by omega,
    (Goes.of_reaches runChild
      (hr1.trans (hr2.trans (hr3.trans (hr4.trans hr5))))).trans hgo, hat⟩

/-- From the frame after the second CALL, when it succeeded with at least 32 bytes of return
data and a nonzero word `ret` at 128: the run ends with STOP, no error, an empty output, and
the state and substate that the call left. -/
theorem seg3_ok (hfork : .berlin ≤ fork) {message : Message fork}
    {x1 x2 x3 bal owner t2 t sel ret : U256} {mem : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hms : mem.size = 224)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = ret)
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) ≠ 0)
    (hret : isZero (isZero ret) ≠ 0) (hg : 200 ≤ g) {a : Evm fork Nat}
    (ha : Logic.At CODE message 3212
      (1 :: x1 :: x2 :: x3 :: [bal, owner, t2, (1617 : U256), bal, t, (570 : U256), sel]) mem g
      st ss rd a) :
    ∃ s : Evm fork Nat, Reaches (Step fork) a s ∧ s.running = false ∧ s.error = none ∧
      s.output = ByteArray.empty ∧ s.state = st ∧ s.substate = ss := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨z1, hr1, hz1⟩ := after2_ok (fork := fork) hbyz (by omega) (by simp) (by omega) a ha
  have hz1b : UsdtVerify.At CODE message 3237
      [BitVec.ofNat 256 rd.size, (128 : U256), bal, owner, t2, (1617 : U256), bal, t,
        (570 : U256), sel] mem (g - 39) st ss z1 := by
    have h := At.ofLogic hz1
    rw [hmfp] at h
    exact h
  obtain ⟨s, hr2, hrun, -, he, ho, -, hs, hss⟩ := (Paths.reclaimEnd_p2 (fork := fork)
    (message := message) (state := st) (substate := ss) hfork hms hmfp hw hn hret
    (gas := g - 39) (by omega)).toSpec z1 hz1b
  exact ⟨s, hr1.trans hr2, hrun, by simpa using he, ho, hs, hss⟩

/-- From the frame after the second CALL, when it succeeded with at least 32 bytes of return
data and the word 0 at 128 (transfer "returned false"): the run reverts with no data. -/
theorem seg3_zero (hfork : .berlin ≤ fork) {message : Message fork}
    {x1 x2 x3 bal owner t2 t sel ret : U256} {mem : ByteArray} {g : Nat}
    {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hms : mem.size = 224)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hw : loadWord (memoryReadBytes mem 128 32) 0 32 = ret)
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) ≠ 0)
    (hret : isZero (isZero ret) = 0) (hg : 200 ≤ g) {a : Evm fork Nat}
    (ha : Logic.At CODE message 3212
      (1 :: x1 :: x2 :: x3 :: [bal, owner, t2, (1617 : U256), bal, t, (570 : U256), sel]) mem g
      st ss rd a) :
    ∃ s : Evm fork Nat, Reaches (Step fork) a s ∧ s.running = false ∧
      s.error = some .revert ∧ s.output = ByteArray.empty ∧ s.state = st ∧ s.substate = ss := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨z1, hr1, hz1⟩ := after2_ok (fork := fork) hbyz (by omega) (by simp) (by omega) a ha
  have hz1b : UsdtVerify.At CODE message 3237
      [BitVec.ofNat 256 rd.size, (128 : U256), bal, owner, t2, (1617 : U256), bal, t,
        (570 : U256), sel] mem (g - 39) st ss z1 := by
    have h := At.ofLogic hz1
    rw [hmfp] at h
    exact h
  obtain ⟨s, hr2, hrun, -, he, ho, -, hs, hss⟩ := (Paths.reclaimEnd_p1 (fork := fork)
    (message := message) (state := st) (substate := ss) hfork hms hmfp hw hn hret
    (gas := g - 39) (by omega)).toSpec z1 hz1b
  exact ⟨s, hr1.trans hr2, hrun, by simpa using he, ho, hs, hss⟩

/-- From the frame after the first CALL, when it succeeded with fewer than 32 bytes of return
data: the run reverts with no data. -/
theorem seg2_short (hfork : .berlin ≤ fork) {message : Message fork} {x1 x2 x3 t sel : U256}
    {mem : ByteArray} {g : Nat} {st : State.TransactionState} {ss : Substate} {rd : ByteArray}
    (hms : mem.size = 192)
    (hmfp : loadWord (memoryReadBytes mem 64 32) 0 32 = (128 : U256))
    (hn : isZero (lessThan (BitVec.ofNat 256 rd.size) (32 : U256)) = 0)
    (hg : 200 ≤ g) {a : Evm fork Nat}
    (ha : Logic.At CODE message 1537
      (1 :: x1 :: x2 :: x3 :: [(0 : U256), t, (570 : U256), sel]) mem g st ss rd a) :
    ∃ s : Evm fork Nat, Reaches (Step fork) a s ∧ s.running = false ∧
      s.error = some .revert ∧ s.output = ByteArray.empty ∧ s.state = st ∧ s.substate = ss := by
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hfork
  obtain ⟨z1, hr1, hz1⟩ := after1_ok (fork := fork) hbyz (by omega) (by simp) (by omega) a ha
  have hz1b : UsdtVerify.At CODE message 1562
      [BitVec.ofNat 256 rd.size, (128 : U256), (0 : U256), t, (570 : U256), sel] mem (g - 39)
      st ss z1 := by
    have h := At.ofLogic hz1
    rw [hmfp] at h
    exact h
  obtain ⟨s, hr2, hrun, -, he, ho, -, hs, hss⟩ := (Paths.reclaimMid_p0 (fork := fork)
    (message := message) (state := st) (substate := ss) hfork hms hmfp
    (bal := loadWord (memoryReadBytes mem 128 32) 0 32) rfl hn (gas := g - 39)
    (by omega)).toSpec z1 hz1b
  exact ⟨s, hr1.trans hr2, hrun, by simpa using he, ho, hs, hss⟩

/-- From pc 0, when the caller is the owner and the code at the token address has size 0: the
run reverts with no data, before any call. -/
theorem seg_nocode (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    (hsize : 4 ≤ message.data.size) (hsize2 : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x17ffc320) (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) ≠
        0)
    {c : ByteArray}
    (hcode : state.getCode (state.getAccount (tokA message.data)).codeHash = .ok c)
    (hcs : isZero (isZero (BitVec.ofNat 256 c.size)) = 0)
    {gas : Nat} (hg : 8000 ≤ gas) {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas state substate evm) :
    ∃ s : Evm fork Nat, Reaches (Step fork) evm s ∧ s.running = false ∧
      s.error = some .revert ∧ s.output = ByteArray.empty ∧
      s.state = (readSlot state message.currentTarget (5 : U256)).recordAccountRead
        (tokA message.data) := by
  have hkb : slotCost (coldIn substate message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨z1, hr1, hz1⟩ := (Paths.reclaimToken_p2 (fork := fork) (message := message)
    (state := state) (substate := substate) hfork hsize hsize2 hsel (by rw [hval]; decide) hown
    (gas := gas) (by omega)).toHoare evm start
  generalize slotCost (coldIn substate message.currentTarget (5 : U256)) = k5 at hkb hz1
  obtain ⟨hms, hmfp, -⟩ := Paths.reclaimToken_p2_mem (message := message)
  have hcode1 : (readSlot state message.currentTarget (5 : U256)).getCode
      ((readSlot state message.currentTarget (5 : U256)).getAccount
        (tokA message.data)).codeHash = .ok c := hcode
  obtain ⟨z2, k2, hk2, hr2, hz2⟩ := ext_step hfork hglam (by code_fact) (by code_fact) hcode1
    (by omega) hz1
  obtain ⟨s, hr3, hrun, -, he, ho, -, hs, hss⟩ := (Paths.reclaimCodeA_p0 (fork := fork)
    (message := message) hfork hms hmfp hcs (gas := gas - (567 + k5) - k2)
    (by omega)).toSpec z2 hz2
  exact ⟨s, hr1.trans (hr2.trans hr3), hrun, by simpa using he, ho, hs⟩

/-- From pc 0, when the caller is not the owner: the run reverts with no data. -/
theorem seg_notowner (hfork : .berlin ≤ fork) {message : Message fork}
    {state : State.TransactionState} {substate : Substate}
    (hsize : 4 ≤ message.data.size) (hsize2 : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x17ffc320) (hval : message.value = 0)
    (hown : equal message.caller.toU256
      (bitwiseAnd MASK (div (storageAt state message.currentTarget (5 : U256)) (256 : U256))) =
        0)
    {gas : Nat} (hg : 8000 ≤ gas) {evm : Evm fork Nat}
    (start : UsdtVerify.At CODE message 0 [] .empty gas state substate evm) :
    ∃ s : Evm fork Nat, Reaches (Step fork) evm s ∧ s.running = false ∧
      s.error = some .revert ∧ s.output = ByteArray.empty ∧
      s.state = readSlot state message.currentTarget (5 : U256) := by
  have hkb : slotCost (coldIn substate message.currentTarget (5 : U256)) ≤ 2100 := by
    unfold slotCost
    split <;> omega
  obtain ⟨s, hr, hrun, -, he, ho, -, hs, hss⟩ := (Paths.reclaimToken_p1 (fork := fork)
    (message := message) (state := state) (substate := substate) hfork hsize hsize2 hsel
    (by rw [hval]; decide) hown (gas := gas) (by omega)).toSpec evm start
  exact ⟨s, hr, hrun, by simpa using he, ho, hs⟩

end WbtcVerify.Sanity

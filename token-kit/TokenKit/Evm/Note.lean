import TokenKit.Evm.RawMem
import TokenKit.Evm.Precompile

/-!
# MSIZE, CALLDATACOPY and LOG4: the `note` modifier of DSNote

DAI (and the other tokens of its family) log every call of `rely` and `deny` with an anonymous
LOG4 written in assembly: the mark is MSIZE, the bytes are two words and then the first 224
bytes of the call data, copied with CALLDATACOPY. None of the three opcodes is in the simulated
set of usdt-verify. The rules here are over EthLib's `Logic.StepG` (MSIZE, CALLDATACOPY) and
over the `StepG` of usdt-verify (LOG4), for the `At` of usdt-verify. The generator uses them
under `paths.note` of gen_paths.py.

- `msizeK`: MSIZE of a memory of known size.
- `calldatacopyG`, `calldatacopyK`: CALLDATACOPY, for EthLib's `At` and with the growth of the
  memory as numerals. EthLib has the rule over `Step` only; it is proved here over `StepG` from
  EthLib's `copyToMemory_cons`, as `returndatacopyG` of Precompile.lean.
- `copied`: the bytes that a copy of `k` bytes from `f` of some data writes (zeros past the end
  of the data).
- `size_rawC`: the size of a memory after a write of copied bytes.
- `logSub4`, `log4K`: the substate after a LOG4 and the rule of LOG4 of bytes inside the memory.
- `read_note`, `read_note5`: the bytes that `note` logs are two words and the copied bytes.
- `log4`, `logs_logSub4`: a log with four topics, for the readable corollaries.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- MSIZE pushes the size of the memory, here a known number, for 2 gas. -/
theorem msizeK {stack : List U256} {sz : Nat} {w : U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x59) (hsz : memory.size = sz) (hw : BitVec.ofNat 256 sz = w)
    (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (w :: stack) memory (gas - 2) state substate) := by
  subst hsz hw
  exact liftAt fun _ => Logic.msizeG hlt hbyte hgas hstack

/-- The bytes that a copy of `k` bytes from the offset `f` of `data` writes: the bytes of the
data, and zeros past its end. -/
abbrev copied (data : ByteArray) (f k : Nat) : ByteArray := ⟨(bufferRead data f k).toArray⟩

/-- CALLDATACOPY writes `size` bytes of the call data from `offset` at `start`, for 3 gas, 3 a
word and the growth of the memory. For EthLib's `At`. -/
theorem calldatacopyG {start offset size : U256} {rest : List U256} {returnData : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x37)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Logic.HoareG fork
      (Logic.At code message pc (start :: offset :: size :: rest) memory gas state substate
        returnData)
      (Logic.At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat (copied message.data offset.toNat size.toNat))
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate returnData) := by
  refine Logic.At.ruleG_of_follows hlt hbyte
    (ofByte_of_decode (op := .calldatacopy) rfl (Fork.frontier_le _)) instruction_calldatacopy
    ?_ ?_
  · rintro evm ⟨-, -, -, -, hst, -, -, -, -, -, -, -, -⟩ k low rfl
    have hst' : low.stack.val = start :: offset :: size :: rest := hst
    rw [copyToMemory_cons hst', copyToMemory_cons (evm := addGas k low) hst']
    exact follows_map_charge fun _ => rfl
  · rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
    subst hm
    have hcost : OPCODE_CALLDATACOPY_BASE = 3 := rfl
    have hword : OPCODE_COPY_PER_WORD = 3 := rfl
    have ok := copyToMemory_cons (base := OPCODE_CALLDATACOPY_BASE) (data := evm.message.data) hst
    dsimp only at ok
    rw [hcost, hword, hmem, hg, charge_nat hgas] at ok
    exact ⟨_, ok, ⟨hcode, hj, rfl, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩⟩

/-- CALLDATACOPY, with the size of the memory, its growth and the three operands as numerals. -/
theorem calldatacopyK {start offset size : U256} {rest : List U256} {sz c n o f k w : Nat}
    {m' : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0x37) (hsz : memory.size = sz)
    (hext : extendMemory sz [(start, size)] = ⟨c, n⟩) (ho : start.toNat = o)
    (hf : offset.toNat = f) (hk : size.toNat = k) (hw : wordCount k = w)
    (hmem : memoryWrite (memoryExtend memory n) o (copied message.data f k) = m')
    (hgas : 3 + 3 * w + c ≤ gas) :
    Logic.HoareG fork
      (At code message pc (start :: offset :: size :: rest) memory gas state substate)
      (At code message (pc + 1) rest m' (gas - (3 + 3 * w + c)) state substate) := by
  subst hsz ho hf hk hw hmem
  have h := fun rd => calldatacopyG (fork := fork) (code := code) (message := message)
    (pc := pc) (state := state) (substate := substate) (rest := rest) (start := start)
    (offset := offset) (size := size) (memory := memory) (gas := gas) (returnData := rd) hlt
    hbyte (by rw [hext]; exact hgas)
  rw [hext] at h
  exact liftAt h

/-- The size of a memory after a write of copied bytes. -/
theorem size_rawC {m data : ByteArray} {sz n o f k : Nat} (hs : m.size = sz)
    (hfit : o + k ≤ sz + n) :
    (memoryWrite (memoryExtend m n) o (copied data f k)).size = sz + n := by
  have hc : (copied data f k).size = k := by simp [ByteArray.size, bufferRead_length]
  rw [size_memoryWrite_of_fit (by
      intro _
      rw [size_memoryExtend, hc, hs]
      exact hfit),
    size_memoryExtend, hs]

/-- The substate after a LOG4 of the contract `target`: one more log, with four topics. -/
abbrev logSub4 (substate : Substate) (target : Address) (t1 t2 t3 t4 : U256)
    (data : ByteArray) : Substate :=
  { substate with
    logs := substate.logs.push
      { address := target
        topics := [U256.toBeBytes t1, U256.toBeBytes t2, U256.toBeBytes t3, U256.toBeBytes t4]
        data := data } }

/-- LOG4 of bytes inside the memory. -/
theorem log4K {start size t1 t2 t3 t4 : U256} {rest : List U256} {sz o k c : Nat}
    {d : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xa4)
    (hstatic : message.isStatic = false) (hsz : memory.size = sz) (ho : start.toNat = o)
    (hk : size.toNat = k) (hfit : o + k ≤ sz) (hcost : logCost 4 size = c)
    (hdata : memoryReadBytes memory o k = d) (hgas : c ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: size :: t1 :: t2 :: t3 :: t4 :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest memory (gas - c) state
        (logSub4 substate message.currentTarget t1 t2 t3 t4 d)) := by
  subst hsz ho hk hcost hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 4) (byte := 0xa4) (start := start)
    (size := size) (words := [t1, t2, t3, t4]) (rest := rest) (memory := memory) (gas := gas)
    rfl hlt hbyte rfl hstatic (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero]
  rfl

/-- The 288 bytes that `note` logs: the two words at 96 and 128 of the five words of memory, then
the 224 bytes copied from the call data at 160. -/
theorem read_note {ws : List U256} {data : ByteArray} {f : Nat} {w3 w4 : U256}
    (hlen : 32 * ws.length = 160)
    (h3 : loadWord (memoryReadBytes (memW ws) 96 32) 0 32 = w3)
    (h4 : loadWord (memoryReadBytes (memW ws) 128 32) 0 32 = w4) :
    memoryReadBytes (memoryWrite (memoryExtend (memW ws) 224) 160 (copied data f 224)) 96 288 =
      wordBytes w3 ++ wordBytes w4 ++ copied data f 224 := by
  have s0 : (memW ws).size = 160 := size_memWn ws hlen
  have hc : (copied data f 224).size = 224 := by simp [ByteArray.size, bufferRead_length]
  have h := memoryReadBytes_memoryWrite_eq_append (memory := memoryExtend (memW ws) 224)
    (value := copied data f 224) (s := 96) (k := 64) (by rw [size_memoryExtend, hc, s0]; decide)
  rw [hc] at h
  have r3 := readWord_raw h3 s0 (by decide)
  have r4 := readWord_raw h4 s0 (by decide)
  have e : memoryReadBytes (memW ws) 96 64 = wordBytes w3 ++ wordBytes w4 := by
    have e0 := memoryReadBytes_add (m := memW ws) (s := 96) (j := 32) (k := 32)
      (by rw [s0]; decide) (by decide) (by decide)
    exact e0.trans (by rw [r3]; exact congrArg (wordBytes w3 ++ ·) r4)
  have hx : memoryReadBytes (memoryExtend (memW ws) 224) 96 64 =
      wordBytes w3 ++ wordBytes w4 :=
    (memoryReadBytes_memoryExtend (by rw [s0]; decide)).trans e
  exact (h : memoryReadBytes (memoryWrite (memoryExtend (memW ws) 224) 160
    (copied data f 224)) 96 288 = _).trans (congrArg (· ++ copied data f 224) hx)

/-- `read_note` for a memory of five words, as a rewrite rule. -/
theorem read_note5 (a b c w3 w4 : U256) (data : ByteArray) (f : Nat) :
    memoryReadBytes (memoryWrite (memoryExtend (memW [a, b, c, w3, w4]) 224) 160
      (copied data f 224)) 96 288 = wordBytes w3 ++ wordBytes w4 ++ copied data f 224 :=
  read_note (by rfl) (memW_load 3 (by rfl) (by rfl) (by rfl))
    (memW_load 4 (by rfl) (by rfl) (by rfl))

/-- A log of the contract `C` with four topics. -/
abbrev log4 (C : Address) (t1 t2 t3 t4 : U256) (d : ByteArray) : Blocks.Log :=
  { address := C
    topics := [U256.toBeBytes t1, U256.toBeBytes t2, U256.toBeBytes t3, U256.toBeBytes t4]
    data := d }

/-- The logs after a LOG4. -/
theorem logs_logSub4 (ss : Substate) (C : Address) (t1 t2 t3 t4 : U256) (d : ByteArray) :
    (logSub4 ss C t1 t2 t3 t4 d).logs = ss.logs.push (log4 C t1 t2 t3 t4 d) := rfl

end TokenKit

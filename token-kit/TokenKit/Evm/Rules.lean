import UsdtVerify.Evm.GasRules
import UsdtVerify.Evm.Steps
import UsdtVerify.Evm.Storage
import UsdtVerify.Evm.Write
import UsdtVerify.Evm.Stuck
import UsdtVerify.Evm.Mirror
import EthLib.Execution.Proofs.Evm.Logic.Region
import TokenKit.Evm.Mem

/-!
# Opcode rules with the memory facts as side goals

The rules of Evm/GasRules.lean state the memory after MSTORE, the price of a memory growth and
the bytes that KECCAK256, LOG, RETURN and REVERT read as terms over `extendMemory memory.size`.
The rules here take those as side goals with numerals: the size of the memory, what
`extendMemory` gives at that size, and the bytes read. A generated proof closes them with
`decide` and the lemmas of Evm/Mem.lean.

- `mstoreK`, `mloadK`, `keccakMapK`, `log3K`, `returnK`, `revertK`, `revert0K`: memory.
- `sloadK`, `sstoreK`, `sstoreBadK`: storage, with the cold flag read off the substate.
- `calldataloadK`, `expK`: a numeral for the offset and for the size of the exponent.
- `logSub`, `logSub2`, `log2K`: the substate after a LOG3 and a LOG2, and the rule of LOG2.
- `decided_by`: a branch condition proved from an earlier, equivalent one.

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- The substate after a LOG3 of the contract `target`: one more log, with three topics. -/
abbrev logSub (substate : Substate) (target : Address) (t1 t2 t3 : U256) (data : ByteArray) :
    Substate :=
  { substate with
    logs := substate.logs.push
      { address := target
        topics := [U256.toBeBytes t1, U256.toBeBytes t2, U256.toBeBytes t3]
        data := data } }

/-- MSTORE, with the size of the memory and its growth as numerals. -/
theorem mstoreK {start value : U256} {rest : List U256} {sz c n o : Nat} {m' : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x52) (hsz : memory.size = sz)
    (hext : extendMemory sz [(start, 32)] = ⟨c, n⟩) (ho : start.toNat = o)
    (hmem : memoryWrite (memoryExtend memory n) o (wordBytes value) = m')
    (hgas : 3 + c ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: value :: rest) memory gas state substate)
      (At code message (pc + 1) rest m' (gas - (3 + c)) state substate) := by
  subst hsz ho hmem
  have h := Gas.mstoreG (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (value := value) (start := start) (memory := memory)
    (gas := gas) hlt hbyte (by rw [hext]; exact hgas)
  rw [hext] at h
  exact h

/-- MLOAD of a word inside the memory. -/
theorem mloadK {start v : U256} {rest : List U256} {sz o : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x51) (hsz : memory.size = sz)
    (ho : start.toNat = o) (hfit : o + 32 ≤ sz)
    (hval : loadWord (memoryReadBytes memory o 32) 0 32 = v) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (v :: rest) memory (gas - 3) state substate) := by
  subst hsz ho hval
  have hext : extendMemory memory.size [(start, (32 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by
      have h32 : (32 : U256).toNat = 32 := by decide
      rw [h32]; exact hfit)
  have h := Gas.mloadG (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (start := start) (memory := memory) (gas := gas)
    hlt hbyte (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (Gas.reshapeG ?_ ?_ ?_)
  · show _ :: rest = _ :: rest
    rw [memoryExtend_zero]
  · exact memoryExtend_zero memory
  · rfl

/-- KECCAK256 of the two words at 0 and 32: the slot of a mapping entry. -/
theorem keccakMapK {a b : U256} {rest : List U256} {sz : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x20) (hsz : memory.size = sz)
    (hfit : 64 ≤ sz) (hdata : memoryReadBytes memory 0 64 = wordBytes a ++ wordBytes b)
    (hgas : 42 ≤ gas) :
    Gas.HoareG fork (At code message pc ((0 : U256) :: (64 : U256) :: rest) memory gas state
        substate)
      (At code message (pc + 1) (mapSlot a b :: rest) memory (gas - 42) state substate) := by
  subst hsz
  have h0 : (0 : U256).toNat = 0 := by decide
  have h64 : (64 : U256).toNat = 64 := by decide
  have hext : extendMemory memory.size [((0 : U256), (64 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_le (by rw [h0, h64]; omega)
  have hcost : keccak256Cost (64 : U256) = 42 := by decide
  have h := Gas.keccak256G (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (start := 0) (size := 64) (memory := memory)
    (gas := gas) hlt hbyte (by rw [hext, hcost]; exact hgas)
  rw [hext, hcost] at h
  refine Gas.Triple.seqL h (Gas.reshapeG ?_ ?_ ?_)
  · show _ :: rest = _ :: rest
    rw [memoryExtend_zero, h0, h64, hdata]
    rfl
  · exact memoryExtend_zero memory
  · rfl

/-- LOG3 of bytes inside the memory. -/
theorem log3K {start size t1 t2 t3 : U256} {rest : List U256} {sz o k c : Nat} {d : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa3) (hstatic : message.isStatic = false)
    (hsz : memory.size = sz) (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hcost : logCost 3 size = c) (hdata : memoryReadBytes memory o k = d) (hgas : c ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: size :: t1 :: t2 :: t3 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - c) state
        (logSub substate message.currentTarget t1 t2 t3 d)) := by
  subst hsz ho hk hcost hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 3) (byte := 0xa3) (start := start)
    (size := size) (words := [t1, t2, t3]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero]
  rfl

/-- The substate after a LOG2 of the contract `target`: one more log, with two topics. -/
abbrev logSub2 (substate : Substate) (target : Address) (t1 t2 : U256) (data : ByteArray) :
    Substate :=
  { substate with
    logs := substate.logs.push
      { address := target
        topics := [U256.toBeBytes t1, U256.toBeBytes t2]
        data := data } }

/-- LOG2 of bytes inside the memory. -/
theorem log2K {start size t1 t2 : U256} {rest : List U256} {sz o k c : Nat} {d : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa2) (hstatic : message.isStatic = false)
    (hsz : memory.size = sz) (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hcost : logCost 2 size = c) (hdata : memoryReadBytes memory o k = d) (hgas : c ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: size :: t1 :: t2 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - c) state
        (logSub2 substate message.currentTarget t1 t2 d)) := by
  subst hsz ho hk hcost hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 2) (byte := 0xa2) (start := start)
    (size := size) (words := [t1, t2]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext]; exact hgas)
  rw [hext] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero]
  rfl

/-- RETURN of bytes inside the memory. -/
theorem returnK {start size : U256} {rest : List U256} {sz o k : Nat} {d : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xf3) (hsz : memory.size = sz)
    (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hdata : memoryReadBytes memory o k = d) :
    Gas.SpecG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted false d gas state substate) := by
  subst hsz ho hk hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.returnG (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (start := start) (size := size) (memory := memory)
    (gas := gas) hlt hbyte (by rw [hext]; exact Nat.zero_le _)
  rw [hext] at h
  refine h.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, hgas, hs, hss⟩
  rw [ho, memoryExtend_zero]

/-- REVERT with bytes inside the memory. -/
theorem revertK (hfork : .berlin ≤ fork) {start size : U256} {rest : List U256} {sz o k : Nat}
    {d : ByteArray} (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) (hsz : memory.size = sz)
    (ho : start.toNat = o) (hk : size.toNat = k) (hfit : o + k ≤ sz)
    (hdata : memoryReadBytes memory o k = d) :
    Gas.SpecG fork (At code message pc (start :: size :: rest) memory gas state substate)
      (Halted true d gas state substate) := by
  subst hsz ho hk hdata
  have hext : extendMemory memory.size [(start, size)] = ⟨0, 0⟩ := extendMemory_of_le hfit
  have h := Gas.revertG (fork := fork) (message := message) (state := state)
    (substate := substate) (Nat.le_trans (by decide) hfork) (rest := rest) (start := start)
    (size := size) (memory := memory) (gas := gas) hlt hbyte
    (by rw [hext]; exact Nat.zero_le _)
  rw [hext] at h
  refine h.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, hgas, hs, hss⟩
  rw [ho, memoryExtend_zero]

/-- REVERT with no bytes, over any memory. -/
theorem revert0K (hfork : .berlin ≤ fork) {start : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xfd) :
    Gas.SpecG fork (At code message pc (start :: (0 : U256) :: rest) memory gas state substate)
      (Halted true .empty gas state substate) := by
  have hext : extendMemory memory.size [(start, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_length_eq_zero _ _
  have h := Gas.revertG (fork := fork) (message := message) (state := state)
    (substate := substate) (Nat.le_trans (by decide) hfork) (rest := rest) (start := start)
    (size := 0) (memory := memory) (gas := gas) hlt hbyte (by rw [hext]; exact Nat.zero_le _)
  rw [hext] at h
  refine h.consequence (fun _ h => h) ?_
  rintro evm ⟨hr, he, ho, hgas, hs, hss⟩
  refine ⟨hr, he, ?_, hgas, hs, hss⟩
  rw [ho]
  have h0 : (0 : U256).toNat = 0 := by decide
  rw [h0]
  simp [memoryReadBytes]

/-- SLOAD from Berlin: the price reads the cold flag off the substate. -/
theorem sloadK (hfork : .berlin ≤ fork) {key : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x54)
    (hgas : slotCost (coldIn substate message.currentTarget key) ≤ gas) :
    Gas.HoareG fork (At code message pc (key :: rest) memory gas state substate)
      (At code message (pc + 1) (storageAt state message.currentTarget key :: rest) memory
        (gas - slotCost (coldIn substate message.currentTarget key))
        (readSlot state message.currentTarget key)
        (accessSlot substate message.currentTarget key)) :=
  Gas.sloadG hfork hlt hbyte rfl hgas

/-- SSTORE from Berlin, in a frame that is not static, of a contract with an account, with more
than 2300 gas. -/
theorem sstoreK (hfork : .berlin ≤ fork) {key new : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x55) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hstipend : 2300 < gas)
    (hgas : Gas.writeCost fork (originalAt state message.currentTarget key)
      (storageAt state message.currentTarget key) new
      (coldIn substate message.currentTarget key) ≤ gas) :
    Gas.HoareG fork (At code message pc (key :: new :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory
        (gas - Gas.writeCost fork (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new
          (coldIn substate message.currentTarget key))
        (writeSlot state message.currentTarget key new)
        (storeSub fork substate message.currentTarget key
          (originalAt state message.currentTarget key)
          (storageAt state message.currentTarget key) new)) :=
  Gas.sstoreWG hfork hlt hbyte hstatic hacc rfl hstipend hgas

/-- CALLDATALOAD at a numeral offset. -/
theorem calldataloadK {start : U256} {rest : List U256} {o : Nat} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x35) (ho : start.toNat = o) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (start :: rest) memory gas state substate)
      (At code message (pc + 1) (loadWord message.data o 32 :: rest) memory (gas - 3) state
        substate) := by
  subst ho
  exact Gas.calldataloadG hlt hbyte hgas

/-- EXP from Berlin, with the size of the exponent as a numeral. -/
theorem expK (hfork : .berlin ≤ fork) {base exponent : U256} {rest : List U256} {e : Nat}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x0a) (he : exponentBytes exponent = e)
    (hgas : 10 + 50 * e ≤ gas) :
    Gas.HoareG fork (At code message pc (base :: exponent :: rest) memory gas state substate)
      (At code message (pc + 1) (Evm.exp base exponent :: rest) memory (gas - (10 + 50 * e))
        state substate) := by
  subst he
  exact Gas.expLG (Nat.le_trans (by decide) hfork) hlt hbyte hgas

/-- A static frame, or a contract with no account, after any reads of slots. -/
theorem bad_readSlot {target other : Address} {n : U256}
    (h : message.isStatic = true ∨ ¬hasAccount state target) :
    message.isStatic = true ∨ ¬hasAccount (readSlot state other n) target :=
  h.imp id fun h h' => h (hasAccount_readSlot_iff.mp h')

/-- `ISZERO x` is 0 exactly when `x` is not 0. -/
theorem isZero_eq_zero_iff {x : U256} : isZero x = 0 ↔ x ≠ 0 := by
  unfold isZero
  constructor
  · intro h e
    rw [if_pos e] at h
    exact absurd h (by decide)
  · intro h
    exact if_neg h

/-- `ISZERO x` is not 0 exactly when `x` is 0. -/
theorem isZero_ne_zero_iff {x : U256} : isZero x ≠ 0 ↔ x = 0 := by
  unfold isZero
  constructor
  · intro h
    exact Classical.byContradiction fun e => h (if_neg e)
  · intro e h
    rw [if_pos e] at h
    exact absurd h (by decide)

/-- A branch condition that an earlier hypothesis `h` decides: the two are the same fact once
pairs of ISZERO and reads of slots are taken off. -/
macro "decided_by " h:term:max : term => `(by
  have hd := $h
  simp only [isZero_eq_zero_iff, isZero_ne_zero_iff, ne_eq, Classical.not_not,
    storageAt_readSlot] at hd ⊢
  exact hd)

end TokenKit

import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Opt
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# Rules for the environment opcodes of Solidity 0.8 code (SKY)

The path generator uses them with `paths.env08 = true` (`scripts/gen_paths.py`).

- `chainidK`: CHAINID (from Istanbul) pushes the chain id of the block of the message.
- `codecopyL`: CODECOPY over the steps that are monotone in gas (EthLib has it over the plain
  steps only). `codecopyK`: CODECOPY of one word of the code, with the size of the memory and its
  growth as numerals; the word that the code holds at the offset is a hypothesis (a fact of the
  code, checked by the kernel in the project of the token).
- `log2ZK`: LOG2 of no bytes, over any memory.
-/

namespace TokenKit

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- From Istanbul, CHAINID runs the read of the chain id of the block. -/
theorem instruction_chainidK (hfork : .istanbul ≤ fork) :
    instruction (Meter := Nat) fork .chainid =
      some (readFrame OPCODE_CHAINID fun evm =>
        BitVec.ofNat 256 evm.message.blockEnv.chainId.toNat) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hfork]

/-- CHAINID pushes the chain id of the block of the message, for 2 gas. -/
theorem chainidK (hfork : .berlin ≤ fork) {stack : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x46) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.chainId.toNat :: stack) memory
        (gas - 2) state substate) :=
  liftAt fun _ => Logic.push_of_readFrameG hlt hbyte
    (ofByte_of_decode (op := .chainid) rfl (Nat.le_trans (by decide) hfork))
    (instruction_chainidK (Nat.le_trans (by decide) hfork))
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- CODECOPY copies a range of the code to memory, with zeros past its end, over the steps that
are monotone in gas. It pays 3, 3 gas a word and the growth of memory. -/
theorem codecopyL {start offset size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x39)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Logic.HoareG fork (At code message pc (start :: offset :: size :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead code offset.toNat size.toNat).toArray⟩)
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate) :=
  liftAt fun rd => by
    refine Logic.At.ruleG_of_follows hlt hbyte
      (ofByte_of_decode (op := .codecopy) rfl (Fork.frontier_le _))
      instruction_codecopy ?_ ?_
    · rintro evm ⟨-, -, -, -, hst, -, -, -, -, -, -, -, -⟩ k low rfl
      have hst' : low.stack.val = start :: offset :: size :: rest := hst
      rw [copyToMemory_cons hst', copyToMemory_cons (evm := addGas k low) hst']
      exact follows_map_charge fun _ => rfl
    · rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
      have hcost : OPCODE_CODECOPY_BASE = 3 := rfl
      have hword : OPCODE_COPY_PER_WORD = 3 := rfl
      subst hcode
      rw [copyToMemory_cons hst]
      dsimp only
      rw [hcost, hword, hmem, hg, charge_nat hgas]
      exact ⟨_, rfl, rfl, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩

/-- CODECOPY of one word of the code: the word `w` that the code holds at the offset `f` is
written at `o`, like an MSTORE of `w`. It pays 6 and the growth of memory. -/
theorem codecopyK {start offset size w : U256} {rest : List U256} {sz c n o f : Nat}
    {m' : ByteArray}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x39) (hsz : memory.size = sz)
    (hext : extendMemory sz [(start, 32)] = ⟨c, n⟩) (ho : start.toNat = o)
    (hf : offset.toNat = f) (hk : size = 32)
    (hcw : (⟨(bufferRead code f 32).toArray⟩ : ByteArray) = wordBytes w)
    (hmem : memoryWrite (memoryExtend memory n) o (wordBytes w) = m')
    (hgas : 6 + c ≤ gas) :
    Logic.HoareG fork (At code message pc (start :: offset :: size :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest m' (gas - (6 + c)) state substate) := by
  subst hsz ho hf hk hmem
  have h32 : (32 : U256).toNat = 32 := by decide
  have hwc : wordCount 32 = 1 := by decide
  have h := codecopyL (fork := fork) (message := message) (state := state)
    (substate := substate) (rest := rest) (start := start) (offset := offset)
    (size := (32 : U256)) (memory := memory) (gas := gas) hlt hbyte
    (by rw [hext, h32, hwc]; omega)
  rw [hext, h32, hwc, hcw] at h
  have e : 3 + 3 * 1 + c = 6 + c := by omega
  rw [e] at h
  exact h

/-- LOG2 of no bytes: any offset, any memory, 1125 gas. -/
theorem log2ZK {start t1 t2 : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa2) (hstatic : message.isStatic = false)
    (hgas : 1125 ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: (0 : U256) :: t1 :: t2 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 1125) state
        (logSub2 substate message.currentTarget t1 t2 .empty)) := by
  have hext : extendMemory memory.size [(start, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_length_eq_zero _ _
  have hcost : logCost (2 : Fin 5).val (0 : U256) = 1125 := by decide
  have h0 : (0 : U256).toNat = 0 := by decide
  have hd : memoryReadBytes memory start.toNat (0 : U256).toNat = ByteArray.empty := by
    rw [h0]
    simp [memoryReadBytes]
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 2) (byte := 0xa2) (start := start)
    (size := 0) (words := [t1, t2]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext, hcost]; exact hgas)
  rw [hext, hcost] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero, hd]
  rfl

end TokenKit

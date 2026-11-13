import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Precompile
import EthLib.Execution.Proofs.Evm.Logic.Copy

/-!
# Rules that USDE needs and the shared library does not have yet

Nothing here is about USDE alone: every lemma is a candidate for the kit (see `status.json`,
`to_merge_into_kit`). They live here because the shared library is owned by another line of
work while this token is built.

- `chainidL`: CHAINID (from Istanbul) pushes the chain id of the block of the message.
- `calldatacopyL`: CALLDATACOPY over the steps that are monotone in gas (EthLib has it over the
  plain steps only).
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
theorem instruction_chainid (hfork : .istanbul ≤ fork) :
    instruction (Meter := Nat) fork .chainid =
      some (readFrame OPCODE_CHAINID fun evm =>
        BitVec.ofNat 256 evm.message.blockEnv.chainId.toNat) := by
  simp [instruction, stackOnlyStep, controlFlowStep, memoryDataStep, returnOpStep,
    environmentStep, HOrElse.hOrElse, OrElse.orElse, Option.orElse, hfork]

/-- CHAINID pushes the chain id of the block of the message, for 2 gas. -/
theorem chainidL (hfork : .berlin ≤ fork) {stack : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x46) (hgas : 2 ≤ gas) (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (BitVec.ofNat 256 message.blockEnv.chainId.toNat :: stack) memory
        (gas - 2) state substate) :=
  liftAt fun _ => Logic.push_of_readFrameG hlt hbyte
    (ofByte_of_decode (op := .chainid) rfl (Nat.le_trans (by decide) hfork))
    (instruction_chainid (Nat.le_trans (by decide) hfork))
    (fun _ _ hm _ _ => by rw [hm]) hgas hstack

/-- CALLDATACOPY copies a range of the call data to memory, with zeros past its end, over the
steps that are monotone in gas. It pays 3, 3 gas a word and the growth of memory. -/
theorem calldatacopyL {start offset size : U256} {rest : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = 0x37)
    (hgas : 3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost ≤
      gas) :
    Logic.HoareG fork (At code message pc (start :: offset :: size :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest
        (memoryWrite (memoryExtend memory (extendMemory memory.size [(start, size)]).expandBy)
          start.toNat ⟨(bufferRead message.data offset.toNat size.toNat).toArray⟩)
        (gas - (3 + 3 * wordCount size.toNat + (extendMemory memory.size [(start, size)]).cost))
        state substate) :=
  liftAt fun rd => by
    refine Logic.At.ruleG_of_follows hlt hbyte
      (ofByte_of_decode (op := .calldatacopy) rfl (Fork.frontier_le _))
      instruction_calldatacopy ?_ ?_
    · rintro evm ⟨-, -, -, -, hst, -, -, -, -, -, -, -, -⟩ k low rfl
      have hst' : low.stack.val = start :: offset :: size :: rest := hst
      rw [copyToMemory_cons hst', copyToMemory_cons (evm := addGas k low) hst']
      exact follows_map_charge fun _ => rfl
    · rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss, hrd⟩
      have hcost : OPCODE_CALLDATACOPY_BASE = 3 := rfl
      have hword : OPCODE_COPY_PER_WORD = 3 := rfl
      have hd : evm.message.data = message.data := by rw [hm]
      rw [copyToMemory_cons hst, hd]
      dsimp only
      rw [hcost, hword, hmem, hg, charge_nat hgas]
      exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, rfl, rfl, hrun, herr, hout, hs, hss, hrd⟩

/-- A LOG in a static frame is `Stuck`, at any gas and for any stack: the step fails before or at
the test of a static frame (EthLib's `logStep_ne_ok_of_isStatic`). -/
theorem logStaticStuck {n : Fin 5} {byte : UInt8} {stack : List U256} (hlt : pc < code.size)
    (hbyte : code[pc] = byte) (decoded : Op.decode byte = some (.log n))
    (hsim : Gas.simulated (.log n) = true) (hs : message.isStatic = true) :
    Gas.HoareG fork (At code message pc stack memory gas state substate) Gas.Stuck := by
  refine Gas.At.stuck hlt hbyte (ofByte_of_decode decoded (Fork.frontier_le _))
    (instruction_log n) (fun low hm _ _ _ => ?_) hsim
  rcases h : logStep n.val low with e | b
  · exact .inl ⟨e, rfl⟩
  · exact absurd h (logStep_ne_ok_of_isStatic (by rw [hm]; exact hs))

end TokenKit

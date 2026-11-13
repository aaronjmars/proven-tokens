import TokenKit.Evm.Precompile
import EnaVerify.Ena.Lib

/-!
# The ECRECOVER call of Solidity 0.8.20 and later (PUSH0)

`TokenKit.ecrecover_call_ok` (TokenKit/Evm/Precompile.lean) matches the code that Solidity puts
after the STATICCALL byte for byte, with `PUSH1 0` (`60 00`). From 0.8.20 (EVM Shanghai) the
compiler writes `PUSH0` (`5f`) there, so the code is two bytes shorter. This file has the same
two theorems for that code; the proofs are the ones of the kit with the PUSH0 rule of
`Ena/Lib.lean` (`push0GA`) in place of PUSH1. Nothing here is about ENA alone (candidate for the
kit, see `status.json`, `to_merge_into_kit`).

- `bubble_no_ok0`: `ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH0 DUP1 RETURNDATACOPY
  RETURNDATASIZE PUSH0 REVERT` from a frame with the flag 0: no run ends with no error.
- `ecrecover_call_ok0`: from Shapella and before Glamsterdam, a run of the real runner from the
  frame at `GAS STATICCALL` to address 1 followed by that code, that ends with no error: the
  call was made with at least 3000 gas, and the loop went on from the opcode after STATICCALL
  with 1 pushed and the output of `Precompiles.Ecrecover.compute` written to the output range.
-/

namespace TokenKit

open TokenKit
open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- The code that Solidity puts after a call whose failure it passes on:
`ISZERO DUP1 ISZERO PUSH2 dest JUMPI RETURNDATASIZE PUSH0 DUP1 RETURNDATACOPY RETURNDATASIZE
PUSH0 REVERT` (Solidity from 0.8.20, with PUSH0). From a frame with the flag 0 on top (the call failed), no run of the loop
returns a frame with no error: with enough gas it reverts with the return data, with less it
runs out of gas. For every runner. -/
theorem bubble_no_ok0 (hsh : .shapella ≤ fork) {rest : List U256} {rd : ByteArray}
    (hlt : pc + 13 < code.size)
    (b0 : code[pc]'(by omega) = 0x15) (b1 : code[pc + 1]'(by omega) = 0x80)
    (b2 : code[pc + 2]'(by omega) = 0x15) (b3 : code[pc + 3]'(by omega) = 0x61)
    (b6 : code[pc + 6]'(by omega) = 0x57) (b7 : code[pc + 7]'(by omega) = 0x3d)
    (b8 : code[pc + 8]'(by omega) = 0x5f) (b9 : code[pc + 9]'(by omega) = 0x80)
    (b10 : code[pc + 10]'(by omega) = 0x3e) (b11 : code[pc + 11]'(by omega) = 0x3d)
    (b12 : code[pc + 12]'(by omega) = 0x5f) (b13 : code[pc + 13]'(by omega) = 0xfd)
    (hrest : rest.length + 4 < STACK_LIMIT)
    {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : Logic.At code message pc (0 :: rest) memory gas state substate rd evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s) :
    s.error ≠ none := by
  have hfork : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hsh
  obtain ⟨Z, hZ⟩ : ∃ Z : U256, (0 : U256) = Z := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : U256, BitVec.ofNat 256 rd.size = N := ⟨_, rfl⟩
  have hZ0 : Z.toNat = 0 := by rw [← hZ]; rfl
  have hNle : N.toNat ≤ rd.size := by
    rw [← hN, BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  have hz1 : isZero (0 : U256) = 1 := by decide
  have hz2 : isZero (1 : U256) = 0 := by decide
  have hlim : STACK_LIMIT = 1024 := rfl
  rw [hlim] at hrest
  refine no_ok_of_specG
    (B := 3 * wordCount N.toNat + (extendMemory memory.size [(Z, N)]).cost +
      (extendMemory (memoryWrite (memoryExtend memory
        (extendMemory memory.size [(Z, N)]).expandBy) Z.toNat
        (memoryReadBytes rd Z.toNat N.toNat)).size [(Z, N)]).cost + 40)
    (Q := fun _ evm => evm.error ≠ none) (fun g hg => ?_) (fun _ _ h => h) start within hrun
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b0
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz1]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (by omega) b1 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- ISZERO
  refine Logic.SpecG.seq (Logic.unaryG (cost := 3) (f := isZero) (by omega) b2
    (ofByte_of_decode (op := .iszero) rfl (Fork.frontier_le _)) instruction_iszero
    (by omega)) ?_
  rw [hz2]
  -- PUSH2
  refine Logic.SpecG.seq (Logic.pushG (n := 2) (by decide) (by omega)
    (by rw [b3]; decide) (by decide) rfl (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- JUMPI, not taken
  refine Logic.SpecG.seq (Logic.jumpi_zeroG (pc := pc + 6) (by omega) b6 (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 7) hfork (by omega) b7 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH0
  refine Logic.SpecG.seq ((push0GA (pc := pc + 8) hsh (by omega) b8 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)).toG) ?_
  rw [hZ]
  -- DUP1
  refine Logic.SpecG.seq (Logic.dup1G (pc := pc + 9) (by omega) b9 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  -- RETURNDATACOPY
  refine Logic.SpecG.seq (returndatacopyG (pc := pc + 10) hfork (by omega) b10
    (by rw [hZ0]; omega) (by omega)) ?_
  -- RETURNDATASIZE
  refine Logic.SpecG.seq (Logic.returndatasizeG (pc := pc + 11) hfork (by omega) b11 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)) ?_
  rw [hN]
  -- PUSH0
  refine Logic.SpecG.seq ((push0GA (pc := pc + 12) hsh (by omega) b12 (by omega)
    (by rw [hlim]; simp only [List.length_cons]; omega)).toG) ?_
  rw [hZ]
  -- REVERT
  refine Logic.SpecG.consequence (Logic.revertG (pc := pc + 13) hfork (by omega) b13 (by omega))
    (fun _ h => h) ?_
  rintro evm ⟨-, he, -⟩
  rw [he]
  simp

/-- From Shapella and before Glamsterdam, under EthLib's real runner: a run from the frame at
`GAS STATICCALL` with the address 1 on top, followed by the code that passes a failure on
(`bubble_no_ok0`), that returns a frame `s` with no error.

Then the call was made and the precompile had its 3000 gas, and the loop went on from the opcode
after STATICCALL with 1 pushed. The memory is the one before, grown for both ranges, with the
start of the output of `Ecrecover.compute` (on the bytes of the input range) written to the
output range. The state is the one before with the two reads recorded, the substate is the one
before with address 1 accessed (no log, no refund), and the gas is exact.

`hdel`: the account at address 1 holds no EIP-7702 delegation code (a state fact). -/
theorem ecrecover_call_ok0 (hsh : .shapella ≤ fork) (hglam : fork < .glamsterdam)
    {inputStart inputSize outputStart outputSize : U256} {rest : List U256} {q : Nat}
    (hq : q = pc + 2) (hlt : q + 13 < code.size)
    (bg : code[pc]'(by omega) = 0x5a) (bs : code[pc + 1]'(by omega) = 0xfa)
    (b0 : code[q]'(by omega) = 0x15) (b1 : code[q + 1]'(by omega) = 0x80)
    (b2 : code[q + 2]'(by omega) = 0x15) (b3 : code[q + 3]'(by omega) = 0x61)
    (b6 : code[q + 6]'(by omega) = 0x57) (b7 : code[q + 7]'(by omega) = 0x3d)
    (b8 : code[q + 8]'(by omega) = 0x5f) (b9 : code[q + 9]'(by omega) = 0x80)
    (b10 : code[q + 10]'(by omega) = 0x3e) (b11 : code[q + 11]'(by omega) = 0x3d)
    (b12 : code[q + 12]'(by omega) = 0x5f) (b13 : code[q + 13]'(by omega) = 0xfd)
    (hrest : rest.length + 6 < STACK_LIMIT)
    (hdel : ∀ c, state.getCode (state.getAccount (toAddressMasked 1)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {bound : Nat} {evm s : Evm fork Nat}
    (start : At code message pc
      (1 :: inputStart :: inputSize :: outputStart :: outputSize :: rest)
      memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) evm
      within = .ok s)
    (hok : s.error = none) :
    3000 ≤ (messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
        (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
        (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
          routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)).subCall ∧
    ∃ after,
      At code message q (1 :: rest)
        (memoryWrite (memoryExtend memory
          (extendMemory memory.size
            [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
          outputStart.toNat
          ((Precompiles.Ecrecover.compute (memoryReadBytes (memoryExtend memory
              (extendMemory memory.size
                [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
              inputStart.toNat inputSize.toNat)).extract 0
            (min outputSize.toNat (Precompiles.Ecrecover.compute (memoryReadBytes
              (memoryExtend memory (extendMemory memory.size
                [(inputStart, inputSize), (outputStart, outputSize)]).expandBy)
              inputStart.toNat inputSize.toNat)).size)))
        (gas - 2 - ((messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
          (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
            routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)).cost +
          (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost) +
          ((messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2)
            (extendMemory memory.size [(inputStart, inputSize), (outputStart, outputSize)]).cost
            (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
              routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1))
                none)).subCall - 3000))
        ((state.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)
        { substate with
          accessedAddresses := substate.accessedAddresses.insert (toAddressMasked 1) }
        after ∧
      ∃ within' : GasMeter.gasHeld after.gas ≤ bound,
        Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after
          within' = .ok s := by
  subst hq
  have hparis : Fork.paris ≤ fork := Nat.le_trans (by decide) hsh
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  have hbyz : Fork.byzantium ≤ fork := Nat.le_trans (by decide) hparis
  have hlim : STACK_LIMIT = 1024 := rfl
  have hnp : ¬fork < Fork.paris := Nat.not_lt.mpr hparis
  -- the code after a failed call gives no run with no error
  have bubble : ∀ {mem g st ss rd after}
      (_ : Logic.At code message (pc + 1 + 1) (0 :: rest) mem g st ss rd after)
      (w : GasMeter.gasHeld after.gas ≤ bound),
      Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) after w =
        .ok s → False := by
    intro mem g st ss rd after hat w h
    have hat' : Logic.At code message (pc + 2) (0 :: rest) mem g st ss rd after := hat
    exact bubble_no_ok0 hsh hlt b0 b1 b2 b3 b6 b7 b8 b9 b10 b11 b12 b13
      (by rw [hlim] at hrest ⊢; omega) hat' w h hok
  -- GAS
  rcases gas_outcome (by omega) bg (by rw [hlim] at hrest ⊢; simp only [List.length_cons]; omega)
    start within hrun with herr | ⟨a1, hat1, w1, hrun1⟩
  · exact (herr hok).elim
  -- STATICCALL
  rcases staticcall_outcome hberlin hglam (by omega) bs hdel hat1.toLogic w1 hrun1 with
    herr | ⟨mem, g, st, ss, rd, a2, hat2, w2, hrun2⟩ |
    ⟨calleeCode, caller, msg, child, a2, hsend, hran, -, hat2, w2, hrun2⟩
  · exact (herr hok).elim
  · exact (bubble hat2 w2 hrun2).elim
  · obtain ⟨cs, css, cgas, -, -, -, ctarget, cca, -, cdis, cdata, cvalue, -⟩ := hsend
    rcases ecrecover_ran hran ctarget cca cdis (by rw [cvalue]; rfl) with
      ⟨-, herr⟩ | ⟨hg, herr, hstate, hsub, hout, hcg⟩
    · have hflag : (if child.error.isNone then (1 : U256) else 0) = 0 := by
        cases hce : child.error with
        | none => exact (herr hce).elim
        | some e => rfl
      rw [hflag] at hat2
      exact (bubble hat2 w2 hrun2).elim
    · have hflag : (if child.error.isNone then (1 : U256) else 0) = 1 := by rw [herr]; rfl
      obtain ⟨istate, isub⟩ := incorporateChild_precompile hparis herr hsub
      have hstart : startState fork msg caller.state = caller.state := by
        simp only [startState, hnp, ite_false]
      rw [cgas] at hg hcg
      refine ⟨hg, a2, ?_, w2, hrun2⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := hat2
      refine ⟨h1, h2, h3, h4, by rw [h5, hflag], ?_, ?_, h8, h9, h10, ?_, ?_⟩
      · rw [h6, hout, cdata]
      · rw [h7, hcg]
      · rw [h11, istate, hstate, hstart, cs]
        rfl
      · rw [h12, isub, css]
        rfl

end TokenKit

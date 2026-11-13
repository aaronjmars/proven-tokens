import LinkVerify.Link.Tac.Complete

/-!
# transferAndCall: the length of the `bytes` argument is below 2 ^ 64 in every run that ends well

Every theorem of Main.lean and Complete.lean assumes `tacN message < 2 ^ 64`. Here that bound is
proven for a run from the entry of the function that ends with no error and started with less
than `2 ^ 60` gas.

What the code does with the length word `L` before the copy (read from the bytes, and checked by
Lean in `dec_any_raw` against `CODE`):

- 568 to 579: `32 * ((L + 31) / 32) + 32`, in 256 bit arithmetic (it can wrap), no memory use;
- 580 to 588: the new free memory pointer `tacFpw L` (it can wrap too) is written as a VALUE at
  the fixed address 64: no growth of the memory;
- 589 to 591: `L` is written at the fixed address 96: the memory grows from 96 to 128, 3 gas;
- 595 to 604: CALLDATACOPY to the fixed address 128 (`96 + 32`), with the size `L` itself (not
  the rounded size, not the pointer).

So no address and no size before or at the copy is built from a rounded or wrapped word: the
first opcode that pays for the length is the CALLDATACOPY at 604, and it pays for the true `L`.
There is one case only, with no split: the decode `dec` of BlocksA.lean holds for every length
(`dec_any`, the same steps with no bound), so a run that ends with no error paid `decCost N`,
which holds `3 * ((N + 31) / 32)` for the copy alone. With `N ≥ 2 ^ 64` that is at least
`3 * 2 ^ 59 > 2 ^ 60`.

- `dec_any_raw`, `dec_any`: the block `dec` for a length of any size.
- `ok_tac_dec_gas`: a run that ends with no error had at least `decCost (tacN message)` gas.
- `ok_tac_len`: with less than `2 ^ 60` gas, the length is below `2 ^ 64`.
- `ok_tac_pre_gas`: `ok_tac_pre` with the bound on the gas in place of the bound on the length.

The steps of `dec_any_raw` are those of the generated `dec_raw`, less the facts that need the
bound.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxRecDepth 8192

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit
open LinkVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork} {sel : U256} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The block `dec` (530 to 1277) for a length of any size: the same frames and the same gas as
`dec_raw`, with no bound on `N`. -/
theorem dec_any_raw {sel : U256} {state : State.TransactionState} {substate : Substate} {N : Nat}
    (hfork : .berlin ≤ fork)
    (hL : (tacLen message).toNat = N)
    {gas : Nat} (hg : 278 + (memoryGasCost (128) - memoryGasCost (96)) + 3 * ((N + 31) / 32) + (memoryGasCost (128 + (N + 31) / 32 * 32) - memoryGasCost 128) ≤ gas) :
    Logic.HoareG fork (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (At CODE message 1277 [(96 : U256), (tacValue message), (tacTo message), (361 : U256), sel] (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memoryWrite (memoryExtend (memW [(0 : U256), (0 : U256), (96 : U256)]) (96 - (96))) (64) (wordBytes (tacFpw (tacLen message)))) (128 - (96))) (96) (wordBytes (tacLen message))) ((N + 31) / 32 * 32)) (128) (copied message.data (add (tacOff message) (36 : U256)).toNat (N))) (gas - (278 + (memoryGasCost (128) - memoryGasCost (96)) + 3 * ((N + 31) / 32) + (memoryGasCost (128 + (N + 31) / 32 * 32) - memoryGasCost 128))) state substate) := by
  step jumpdestR
  step pushR 2 (361 : U256)
  at_pc 534
  step pushR 1 (4 : U256)
  at_pc 536
  step dupR 0
  step calldataloadK (by code_fact) (by code_fact) (o := 4) (show (4 : U256).toNat = 4 by decide) (by gas_ok)
  step pushR 1 (1 : U256)
  at_pc 540
  step pushR 1 (160 : U256)
  at_pc 542
  step pushR 1 (2 : U256)
  at_pc 544
  step expK hfork (by code_fact) (by code_fact) (e := 1) (by decide +kernel) (by gas_ok)
  step foldK (y := (1461501637330902918203684832716283019655932542976 : U256)) (by decide +kernel)
  step binR 0x03 instruction_sub
  step foldK (y := (1461501637330902918203684832716283019655932542975 : U256)) (by decide +kernel)
  step binR 0x16 (instruction_of_stackOnlyStep rfl)
  step foldK (y := (tacTo message)) (rfl)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step pushR 1 (36 : U256)
  at_pc 550
  step dupR 0
  step calldataloadK (by code_fact) (by code_fact) (o := 36) (show (36 : U256).toNat = 36 by decide) (by gas_ok)
  step foldK (y := (tacValue message)) (rfl)
  step swap2K (by code_fact) (by code_fact) (by gas_ok)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step pushR 1 (100 : U256)
  at_pc 556
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step pushR 1 (68 : U256)
  at_pc 559
  step calldataloadK (by code_fact) (by code_fact) (o := 68) (show (68 : U256).toNat = 68 by decide) (by gas_ok)
  step foldK (y := (tacOff message)) (rfl)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step dupR 1
  step binR 0x01 instruction_add
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step dupR 3
  step binR 0x01 instruction_add
  step calldataloadK (by code_fact) (by code_fact) (o := (add (4 : U256) (tacOff message)).toNat) rfl (by gas_ok)
  step foldK (y := (tacLen message)) (rfl)
  step dupR 0
  step pushR 1 (32 : U256)
  at_pc 570
  step pushR 1 (31 : U256)
  at_pc 572
  step dupR 2
  step binR 0x01 instruction_add
  step dupR 1
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step binR 0x04 (instruction_of_stackOnlyStep rfl)
  step dupR 1
  step binR 0x02 (instruction_of_stackOnlyStep rfl)
  step binR 0x01 instruction_add
  step pushR 1 (64 : U256)
  at_pc 582
  step mloadK (by code_fact) (by code_fact) (size_memW3 (0 : U256) (0 : U256) (96 : U256)) (o := 64) (show (64 : U256).toNat = 64 by decide) (by omega) (memW_load64 (0 : U256) (0 : U256) (96 : U256) []) (by gas_ok)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step dupR 1
  step binR 0x01 instruction_add
  step foldK (y := (tacFpw (tacLen message))) (rfl)
  step pushR 1 (64 : U256)
  at_pc 588
  step mstoreS (by code_fact) (by code_fact) (size_memW3 (0 : U256) (0 : U256) (96 : U256)) (by omega) (o := 64) (show (64 : U256).toNat = 64 by decide) (sz' := 96) (by omega) (by gas_ok)
  have hs3 := size_wr (v := (tacFpw (tacLen message))) (o := 64) (sz' := 96) (size_memW3 (0 : U256) (0 : U256) (96 : U256)) (by omega) (by omega)
  step dupR 1
  step dupR 1
  step mstoreS (by code_fact) (by code_fact) hs3 (by omega) (o := 96) (show (96 : U256).toNat = 96 by decide) (sz' := 128) (by omega) (by gas_ok)
  have hs6 := size_wr (v := (tacLen message)) (o := 96) (sz' := 128) hs3 (by omega) (by omega)
  step swap3K (by code_fact) (by code_fact) (by gas_ok)
  step swap2K (by code_fact) (by code_fact) (by gas_ok)
  step swap1K (by code_fact) (by code_fact) (by gas_ok)
  step pushR 1 (32 : U256)
  at_pc 597
  step dupR 4
  step binR 0x01 instruction_add
  step foldK (y := (128 : U256)) (by decide +kernel)
  step dupR 3
  step dupR 3
  step dupR 0
  step dupR 2
  step dupR 4
  step calldatacopyS (by code_fact) (by code_fact) hs6 (by omega) (show (128 : U256).toNat = 128 by decide) hL (by gas_ok)
  step popR
  step swap5K (by code_fact) (by code_fact) (by gas_ok)
  step swap7K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step pushR 2 (1277 : U256)
  at_pc 612
  step swap6K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step popR
  step popR
  step popR
  step popR
  step popR
  step jumpR
  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)

/-- The block `dec` for a length of any size, with the names of its memory and its gas. -/
theorem dec_any {N : Nat} (hfork : .berlin ≤ fork) (hL : (tacLen message).toNat = N)
    {gas : Nat} (hg : decCost N ≤ gas) :
    Logic.HoareG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (At CODE message 1277 [(96 : U256), (tacValue message), (tacTo message), (361 : U256), sel]
        (decMem message N) (gas - decCost N) state substate) :=
  dec_any_raw hfork hL hg

/-- A run from the entry of the function that ends with no error paid for the whole decode: the
gas it started with is at least `decCost` of the length, whatever the length. -/
theorem ok_tac_dec_gas (hfork : .berlin ≤ fork) {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    decCost (tacN message) ≤ gas :=
  (Complete.ok_splitLE (B := decCost (tacN message)) (c := decCost (tacN message))
    (Nat.le_refl _) (fun g hg => dec_any (N := tacN message) hfork rfl hg) start hrun hok).1

/-- A run from the entry of the function that ends with no error and started with less than
`2 ^ 60` gas has a `bytes` argument whose length word is below `2 ^ 64`: the CALLDATACOPY at 604
takes 3 gas for each 32 bytes of that length. -/
theorem ok_tac_len (hfork : .berlin ≤ fork) {gas : Nat} {evm s : Evm fork Nat}
    (hgas : gas < 2 ^ 60)
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    tacN message < 2 ^ 64 := by
  have h := ok_tac_dec_gas hfork start hrun hok
  have h3 : 3 * ((tacN message + 31) / 32) ≤ gas := by
    unfold decCost at h
    omega
  omega

/-- D. `ok_tac_pre` with a bound on the gas in place of the bound on the length: a run from the
entry of the function that ends with no error and started with less than `2 ^ 60` gas. -/
theorem ok_tac_pre_gas (hfork : .berlin ≤ fork) {gas : Nat} {evm s : Evm fork Nat}
    (hgas : gas < 2 ^ 60)
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    tacN message < 2 ^ 64 ∧
    message.isStatic = false ∧ hasAccount state message.currentTarget ∧
    TacToSet message ∧ TacToOther message ∧ TacFunded message state ∧ TacFits message state ∧
    ∃ c : ByteArray, TacCode message state c ∧
      ((TacNoCode c ∧ tacDoneGas fork message state substate ≤ gas ∧ s.running = false ∧
          s.output = wordBytes (1 : U256) ∧
          s.gas = gas - tacDoneGas fork message state substate ∧
          s.state = tacDoneSt message state ∧
          s.substate = tacDoneSs fork message state substate) ∨
       (TacHasCode c ∧ tacCallGas fork message state substate + 5 ≤ gas ∧
          ∃ z : Evm fork Nat,
            At CODE message 3088
              (tacCallStack message sel (tacAsked fork message state substate gas))
              (tacMem message) (gas - (tacCallGas fork message state substate + 5))
              (tacCallSt message state) (tacCallSs fork message state substate) z ∧
            EndsL runChild z s)) :=
  have hN := ok_tac_len hfork hgas start hrun hok
  ⟨hN, ok_tac_pre hfork hN start hrun hok⟩

end LinkVerify.Tac

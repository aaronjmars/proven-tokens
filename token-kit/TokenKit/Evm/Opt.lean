import UsdtVerify.Evm.Calldata
import UsdtVerify.Evm.Exact
import TokenKit.Evm.Rules
import TokenKit.Evm.Logic
import TokenKit.Evm.Stack

/-!
# Rules for code compiled with the optimizer

Solidity 0.8 with the optimizer on reads the selector with SHR, builds masks with SHL, checks
the size of the call data with SLT and packs flags with OR. The dispatcher is no list that the
code walks entry by entry, so the path generator (`scripts/gen_paths.py`, `dispatch.mode =
"walk"`) runs it like any other code; the lemmas here decide its comparisons from the hypotheses
on the call.

SHL, SHR, SLT, SGT and XOR are not in the simulated set of usdt-verify (the opcodes that its
`StepG` covers, for the lift to the two-counter gas meter), so a token that runs them has its
block lemmas and path theorems over EthLib's `Logic.StepG` (a step from a frame that is monotone
in gas; `TokenKit/Evm/Logic.lean`), and its completeness theorems over `runFrame`, not over the
`Ends` of usdt-verify. The generators call that the logic mode.

- `bin3L`: a two-operand opcode of price 3 of any fork up to Berlin (SHL, SHR, SLT, SGT, OR, XOR),
  over `Logic.StepG`. `bin3K`: the same over the `StepG` of usdt-verify, for a simulated opcode.
- `hoareL`, `specL`, `stuckL`, `haltGasL`: a triple or a specification over the `StepG` of
  usdt-verify is one over `Logic.StepG`; the same for a triple to a stuck frame.
- `Complete.no_ok_stuckL`: no successful run from a frame that reaches a stuck frame.
- `shr_selector`: the first word of the call data shifted right by 224 bits is the selector.
- `size_lt4_zero`, `size_lt4_ne`: the test `CALLDATASIZE < 4` from the size of the call data.
- `equal_key_zero`: EQ of a key of a list with a word that is not in the list.
- `log3ZK`: LOG3 of no bytes, over any memory.
- `reverted_error`: a frame that halted on a revert has an error.
- `and_mask_comm`: the mask of an address on the right of AND is the mask on the left.

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

/-- A two-operand opcode of price 3 that a fork up to Berlin added (or an older one). -/
theorem bin3K {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (hdec : Op.decode byte = some op) (hsince : op.since ≤ fork)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hcost : cost = 3)
    (hsim : Gas.simulated op = true) (hgas : 3 ≤ gas) :
    Gas.HoareG fork (At code message pc (x :: y :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y :: rest) memory (gas - 3) state substate) := by
  subst hcost
  exact Gas.binaryG hlt hbyte (ofByte_of_decode hdec hsince) hrun hgas hsim

/-- A two-operand opcode of price 3, over `Logic.StepG`: no limit to the simulated set. -/
theorem bin3L {byte : UInt8} {op : Op} {cost : Nat} {f : U256 → U256 → U256} {x y : U256}
    {rest : List U256} (hlt : pc < code.size) (hbyte : code[pc] = byte)
    (hdec : Op.decode byte = some op) (hsince : op.since ≤ fork)
    (hrun : instruction (Meter := Nat) fork op = some (binaryOp cost f)) (hcost : cost = 3)
    (hgas : 3 ≤ gas) :
    Logic.HoareG fork (At code message pc (x :: y :: rest) memory gas state substate)
      (At code message (pc + 1) (f x y :: rest) memory (gas - 3) state substate) := by
  subst hcost
  apply ruleL hlt hbyte (ofByte_of_decode hdec hsince) hrun (runMono_binaryOp 3 f)
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  rw [binaryOp_cons hst, charge_nat (by rw [hg]; exact hgas)]
  exact ⟨_, rfl, hcode, hj, hm, by simp [hpc], rfl, hmem, by simp [hg], hrun, herr, hout, hs, hss⟩

/-- A triple over the `StepG` of usdt-verify is a triple over `Logic.StepG`. -/
theorem hoareL {P Q : Evm fork Nat → Prop} (h : Gas.HoareG fork P Q) : Logic.HoareG fork P Q :=
  Gas.Triple.lift h

/-- A specification over the `StepG` of usdt-verify is a specification over `Logic.StepG`. -/
theorem specL {P Q : Evm fork Nat → Prop} (h : Gas.SpecG fork P Q) : Logic.SpecG fork P Q :=
  Gas.Triple.lift (R' := Logic.StepG fork) h

/-- A triple to a stuck frame of usdt-verify is a triple to a stuck frame of EthLib. -/
theorem stuckL {P : Evm fork Nat → Prop} (h : Gas.HoareG fork P Gas.Stuck) :
    Logic.HoareG fork P Logic.Stuck := fun evm hp =>
  let ⟨z, hr, hz⟩ := Gas.Triple.lift (R' := Logic.StepG fork) h evm hp
  ⟨z, hr, hz.1, hz.2.2⟩

/-- A specification over `Logic.StepG` to a halt, with an equal gas. -/
theorem haltGasL {P : Evm fork Nat → Prop} {rev : Bool} {out : ByteArray} {g g' : Nat}
    {st : State.TransactionState} {ss : Substate}
    (h : Logic.SpecG fork P (Halted rev out g st ss)) (hg : g = g') :
    Logic.SpecG fork P (Halted rev out g' st ss) := hg ▸ h

/-- The first word of the call data, shifted right by 224 bits, is the selector. -/
theorem shr_selector (data : ByteArray) :
    bitwiseShr (224 : U256) (loadWord data 0 32) = BitVec.ofNat 256 (selector data) := by
  rw [← selector_word]
  have hne : (BitVec.ofNat 256 (2 ^ 224) : U256) ≠ 0 := by decide
  have h224 : (BitVec.ofNat 256 (2 ^ 224) : U256).toNat = 2 ^ 224 := by decide
  have hs : (224 : U256).toNat = 224 := by decide
  have hmask : (BitVec.ofNat 256 0xffffffff : U256).toNat = 2 ^ 32 - 1 := by decide
  have hw : (loadWord data 0 32).toNat < 2 ^ 256 := (loadWord data 0 32).isLt
  have hq : (loadWord data 0 32).toNat / 2 ^ 224 < 2 ^ 32 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    exact hw
  apply BitVec.eq_of_toNat_eq
  have hdiv : (div (loadWord data 0 32) (BitVec.ofNat 256 (2 ^ 224))).toNat =
      (loadWord data 0 32).toNat / 2 ^ 224 := by
    unfold div
    rw [if_neg hne, BitVec.toNat_ofNat, h224]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hw)
  have hshr : (bitwiseShr (224 : U256) (loadWord data 0 32)).toNat =
      (loadWord data 0 32).toNat / 2 ^ 224 := by
    unfold bitwiseShr
    rw [hs, if_pos (by decide), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [hshr]
  unfold bitwiseAnd
  rw [BitVec.toNat_and, hdiv, hmask, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt hq]

/-- With 4 bytes of call data or more, the test `CALLDATASIZE < 4` is 0. -/
theorem size_lt4_zero {n : Nat} (h4 : 4 ≤ n) (hn : n < 2 ^ 256) :
    lessThan (BitVec.ofNat 256 n) (4 : U256) = 0 := by
  have h4' : (4 : U256).toNat = 4 := by decide
  have h : ¬(BitVec.ofNat 256 n : U256).toNat < (4 : U256).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h4']
    omega
  exact if_neg h

/-- With fewer than 4 bytes of call data, the test `CALLDATASIZE < 4` is not 0. -/
theorem size_lt4_ne {n : Nat} (h : n < 4) : lessThan (BitVec.ofNat 256 n) (4 : U256) ≠ 0 := by
  have h4' : (4 : U256).toNat = 4 := by decide
  have hl : (BitVec.ofNat 256 n : U256).toNat < (4 : U256).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans h (by decide)), h4']
    exact h
  have e : lessThan (BitVec.ofNat 256 n) (4 : U256) = 1 := if_pos hl
  rw [e]
  decide

/-- EQ of a key of a list with a word that is not in the list is 0. -/
theorem equal_key_zero {x k : U256} {l : List U256} (h : x ∉ l) (hk : k ∈ l) : equal k x = 0 :=
  if_neg (fun (e : k = x) => h (e ▸ hk))

/-- LOG3 of no bytes: any offset, any memory, 1500 gas. -/
theorem log3ZK {start t1 t2 t3 : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa3) (hstatic : message.isStatic = false)
    (hgas : 1500 ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: (0 : U256) :: t1 :: t2 :: t3 :: rest) memory gas state
        substate)
      (At code message (pc + 1) rest memory (gas - 1500) state
        (logSub substate message.currentTarget t1 t2 t3 .empty)) := by
  have hext : extendMemory memory.size [(start, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_length_eq_zero _ _
  have hcost : logCost (3 : Fin 5).val (0 : U256) = 1500 := by decide
  have h0 : (0 : U256).toNat = 0 := by decide
  have hd : memoryReadBytes memory start.toNat (0 : U256).toNat = ByteArray.empty := by
    rw [h0]
    simp [memoryReadBytes]
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 3) (byte := 0xa3) (start := start)
    (size := 0) (words := [t1, t2, t3]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext, hcost]; exact hgas)
  rw [hext, hcost] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero, hd]
  rfl

/-- A frame that halted on a revert has an error. -/
theorem reverted_error {out : ByteArray} {g : Nat} {st : State.TransactionState}
    {ss : Substate} (e : Evm fork Nat) (h : Halted true out g st ss e) : e.error ≠ none := by
  rw [h.2.1]; simp

/-- The mask of an address on the right of AND is the mask on the left. -/
theorem and_mask_comm (w : U256) :
    bitwiseAnd w (1461501637330902918203684832716283019655932542975 : U256) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

namespace Complete

variable {stack : List U256} {bound : Nat} {runChild : MessageRunner fork Nat bound}
  {evm s : Evm fork Nat}

/-- No successful run from a frame that, with any gas from `B` on, reaches a stuck frame along
`Logic.StepG` (EthLib's `no_ok_stuck`, for the `At` of usdt-verify). -/
theorem no_ok_stuckL {B : Nat}
    (h : ∀ g, B ≤ g →
      Logic.HoareG fork (At code message pc stack memory g state substate) Logic.Stuck)
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  Logic.no_ok_stuck (fun g hg => lowerPre (h g hg)) start.toLogic within hrun hok

end Complete

end TokenKit

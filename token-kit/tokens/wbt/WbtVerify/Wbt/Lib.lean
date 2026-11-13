import TokenKit.Evm.Opt
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt
import TokenKit.Evm.SupplyOpt

/-!
# Rules that WBT needs and the shared library does not have yet

- `logSub1`, `log1ZK`: the substate after a LOG1 and the rule of a LOG1 of no bytes (the events
  `Pause()` and `Unpause()`).
- `logStuckW`: a LOG in a static frame is stuck (it fails with any gas). The path generator
  uses it for a LOG that comes before the first SSTORE of a path (`transferOwnership`,
  `renounceOwnership`): there the completeness proof first splits on `message.isStatic`.

- `add_bound_submax`, `add_nat_submax`, `add_fact_submax`, `size_of_slt_u`, `mul_one_right`,
  `zero_or`: the shapes of Solidity 0.8 code compiled with the optimizer off.
- `log1`, `logs_logSub1`: a log with one topic, for the readable corollaries.
- `and_255_comm`, `and_255_idem`: the mask of a byte, as the unoptimized code repeats it.
- `D_congr`: the sum of the balances minus the total supply reads the storage of the contract
  only (for the functions that only read: name() and symbol()).

Nothing here is about WBT: the file is to be merged into the kit (`TokenKit/Evm/`), see
`status.json`, `to_merge_into_kit`.
-/

namespace WbtVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-- The substate after a LOG1 of the contract `target`: one more log, with one topic. -/
abbrev logSub1 (substate : Substate) (target : Address) (t1 : U256) (data : ByteArray) :
    Substate :=
  { substate with
    logs := substate.logs.push
      { address := target
        topics := [U256.toBeBytes t1]
        data := data } }

/-- LOG1 of no bytes: any offset, any memory, 750 gas. -/
theorem log1ZK {start t1 : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0xa1) (hstatic : message.isStatic = false)
    (hgas : 750 ≤ gas) :
    Gas.HoareG fork
      (At code message pc (start :: (0 : U256) :: t1 :: rest) memory gas state substate)
      (At code message (pc + 1) rest memory (gas - 750) state
        (logSub1 substate message.currentTarget t1 .empty)) := by
  have hext : extendMemory memory.size [(start, (0 : U256))] = ⟨0, 0⟩ :=
    extendMemory_of_length_eq_zero _ _
  have hcost : logCost (1 : Fin 5).val (0 : U256) = 750 := by decide
  have h0 : (0 : U256).toNat = 0 := by decide
  have hd : memoryReadBytes memory start.toNat (0 : U256).toNat = ByteArray.empty := by
    rw [h0]
    simp [memoryReadBytes]
  have h := Gas.logG (fork := fork) (code := code) (message := message) (pc := pc)
    (state := state) (substate := substate) (n := 1) (byte := 0xa1) (start := start)
    (size := 0) (words := [t1]) (rest := rest) (memory := memory) (gas := gas) rfl
    hlt hbyte rfl hstatic (by rw [hext, hcost]; exact hgas)
  rw [hext, hcost] at h
  refine Gas.Triple.seqL h (restate rfl rfl (memoryExtend_zero memory) rfl rfl ?_)
  show ({ substate with logs := _ } : Substate) = _
  rw [memoryExtend_zero, hd]
  rfl

/-- A LOG in a static frame is `Stuck`, at any fork and any gas: EthLib's `logStep` ends with
`writeInStaticContext` (or with an earlier error), never with a frame. -/
theorem logStuckW {n : Fin 5} {byte : UInt8} {stack : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (hdec : Op.decode byte = some (.log n))
    (hbad : message.isStatic = true) :
    Gas.HoareG fork (At code message pc stack memory gas state substate) Gas.Stuck := by
  refine Gas.At.stuck hlt hbyte (ofByte_of_decode hdec (Fork.frontier_le _)) (instruction_log n)
    (fun low hm _ _ _ => ?_) (by cases n using Fin.cases <;> rfl)
  rcases h : logStep n.val low with e | b
  · exact .inl ⟨e, rfl⟩
  · exact absurd h (logStep_ne_ok_of_isStatic (by rw [hm]; exact hbad))

/-! ## The shapes of Solidity 0.8 code compiled with the optimizer off -/

/-- The largest word, as the unoptimized code pushes it (a PUSH32 of 32 bytes ff). -/
theorem max_toNat :
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256).toNat =
      2 ^ 256 - 1 := by decide

/-- The check below, for any word `m` that is the largest word. -/
theorem add_bound_gen {a v m : U256} (hm : m.toNat = 2 ^ 256 - 1)
    (h : isZero (greaterThan a (sub m v)) ≠ 0) :
    a.toNat + v.toNat < 2 ^ 256 := by
  have hle := Supply.le_of_cond_gt1 h
  have hv := v.isLt
  have ha := a.isLt
  simp only [sub, BitVec.toNat_sub] at hle
  omega

/-- The check of a Solidity 0.8 addition with the optimizer off, `ISZERO (GT a (MAX - v))`: the
sum is below `2^256`. -/
theorem add_bound_submax {a v : U256}
    (h : isZero (greaterThan a (sub
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) v))
      ≠ 0) :
    a.toNat + v.toNat < 2 ^ 256 :=
  add_bound_gen max_toNat h

/-- After that check the sum does not wrap. -/
theorem add_nat_submax {a v : U256}
    (h : isZero (greaterThan a (sub
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) v))
      ≠ 0) :
    (add a v).toNat = a.toNat + v.toNat := by
  have hb := add_bound_submax h
  simp only [add, BitVec.toNat_add]
  omega

/-- The same over the integers (the form the supply proofs use). -/
theorem add_fact_submax {a v : U256}
    (h : isZero (greaterThan a (sub
      (115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256) v))
      ≠ 0) :
    ((add a v).toNat : Int) = a.toNat + v.toNat := by
  rw [add_nat_submax h]
  omega

/-- `4 + (x - 4)` is `x`: the unoptimized decoder computes the end of the call data so. -/
theorem add4_sub4 (x : U256) : add (4 : U256) (sub x (4 : U256)) = x := by
  simp only [add, sub]
  bv_omega

/-- The check of the size of the call data with the optimizer off:
`ISZERO (SLT ((4 + (CALLDATASIZE - 4)) - 4) k)` is not 0. -/
theorem size_of_slt_u {n : Nat} {k : U256} (h4 : 4 ≤ n) (hn : n < 2 ^ 256)
    (hk : k.toNat < 2 ^ 255)
    (h : isZero (signedLessThan
      (sub (add (4 : U256) (sub (BitVec.ofNat 256 n) (4 : U256))) (4 : U256)) k) ≠ 0) :
    4 + k.toNat ≤ n := by
  rw [add4_sub4] at h
  exact Readable.size_of_slt h4 hn hk h

/-- A multiplication by 1 (a value at offset 0 of a slot, unoptimized). -/
theorem mul_one_right (w : U256) : mul w (1 : U256) = w := by
  simp only [mul]
  exact BitVec.mul_one w

/-- An OR with 0 on the left. -/
theorem zero_or (w : U256) : bitwiseOr (0 : U256) w = w := by
  simp only [bitwiseOr]
  exact BitVec.zero_or

/-- A word that is not 0, as a jump condition with no ISZERO (`require(flag)`). -/
theorem ne_of_cond0 {w : U256} (h : w ≠ 0) : w ≠ 0 := h

/-- A log of the contract `C` with one topic. -/
abbrev log1 (C : Address) (t1 : U256) (data : ByteArray) : Blocks.Log :=
  { address := C
    topics := [U256.toBeBytes t1]
    data := data }

theorem logs_logSub1 (ss : Substate) (C : Address) (t1 : U256) (d : ByteArray) :
    (logSub1 ss C t1 d).logs = ss.logs.push (log1 C t1 d) := rfl

/-- `D` reads the storage words of `C` only. -/
theorem D_congr {b t : U256} {C : Address} {S S' : State.TransactionState}
    (h : ∀ n, storageAt S' C n = storageAt S C n) :
    Supply.D b t C S' = Supply.D b t C S := by
  unfold Supply.D Supply.sumBal
  rw [h t, Supply.sumTo_congr (g := Supply.bal b C S) _ (fun i _ => by
    show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
    rw [h])]

/-- The mask of a byte on the right of AND is the mask on the left. -/
theorem and_255_comm (w : U256) : bitwiseAnd w (255 : U256) = bitwiseAnd (255 : U256) w := by
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

/-- The mask of a byte, twice. -/
theorem and_255_idem (w : U256) :
    bitwiseAnd (255 : U256) (bitwiseAnd (255 : U256) w) = bitwiseAnd (255 : U256) w := by
  simp only [bitwiseAnd, ← BitVec.and_assoc, BitVec.and_self]

end WbtVerify

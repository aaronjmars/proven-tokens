import TokenKit.Evm.SafeL
import TokenKit.Evm.RawMem
import TokenKit.Evm.Opt
import TokenKit.Evm.Readable
import TokenKit.Evm.ReadableOpt
import TokenKit.Evm.SupplyOpt
import TokenKit.Evm.Supply2
import EthLib.Execution.Proofs.Evm.Logic.Copy
import WbtcVerify.Wbtc.Code

/-!
# Rules that WBTC needs and the shared library does not have yet

Nothing here is about WBTC alone, but for `codeWord_4507`: every other lemma is a candidate for
the kit (see `status.json`, `to_merge_into_kit`). They live here because the shared library is
owned by another line of work while this token is built. The lemmas are copies of the ones of
tokens/link (Lib.lean, Sep.lean) and tokens/wbt (Lib.lean), in the namespace of this token.

Solidity 0.4 with the optimizer (the dispatcher):

- `and_div_selector`, `div_and_selector`: the selector word, `(calldata[0] / 2^224) & 0xffffffff`
  in either order of AND, is the number `selector`.
- `size_isZero_zero`, `size_isZero_ne`: the test `CALLDATASIZE == 0` (not used by WBTC).
- `equal_key_zero_r`: EQ of a word that is no key with a key, the word first.
- `Supply.add_fact_ltc`: the SafeMath addition `c = a + b; assert(c >= a)`.

Logs:

- `logSub1`, `log1ZK`: the substate after a LOG1 and the rule of a LOG1 of no bytes (the events
  `Pause()` and `Unpause()`).
- `logStuckW`: a LOG in a static frame is stuck (it fails with any gas). The path generator
  uses it for a LOG that comes before the first SSTORE of a path (`claimOwnership`).
- `log1`, `logs_logSub1`: a log with one topic, for the readable corollaries.
- `D_congr`: the sum of the balances minus the total supply reads the storage of the contract
  only.

The code:

- `codeWord_4507`: the 32 bytes of the code from 4507 (0x119b) are the topic of the event
  `Transfer(address,address,uint256)`. The code reads it with CODECOPY (it is no PUSH32).
-/

namespace WbtcVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 Address)
open EthLib.Base
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {memory : ByteArray} {gas : Nat} {state : State.TransactionState} {substate : Substate}

/-! ## Solidity 0.4 with the optimizer -/

/-- The selector word of Solidity 0.4: the mask on the left. -/
theorem and_div_selector (data : ByteArray) :
    bitwiseAnd (4294967295 : U256) (div (loadWord data 0 32)
      (26959946667150639794667015087019630673637144422540572481103610249216 : U256)) =
      BitVec.ofNat 256 (selector data) :=
  selector_word data

/-- The selector word of Solidity 0.4: the mask on the right. -/
theorem div_and_selector (data : ByteArray) :
    bitwiseAnd (div (loadWord data 0 32)
      (26959946667150639794667015087019630673637144422540572481103610249216 : U256))
      (4294967295 : U256) = BitVec.ofNat 256 (selector data) := by
  rw [← and_div_selector]
  unfold bitwiseAnd
  exact BitVec.and_comm _ _

/-- With call data that is not empty, the test `CALLDATASIZE == 0` is 0. -/
theorem size_isZero_zero {n : Nat} (h1 : 1 ≤ n) (hn : n < 2 ^ 256) :
    isZero (BitVec.ofNat 256 n) = 0 := by
  apply isZero_eq_zero_iff.mpr
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  simp at this
  omega

/-- With no call data, the test `CALLDATASIZE == 0` is not 0. -/
theorem size_isZero_ne {n : Nat} (h : n < 1) : isZero (BitVec.ofNat 256 n) ≠ 0 := by
  have h0 : n = 0 := by omega
  subst h0
  decide

/-- EQ of a word that is not in a list with a key of the list is 0, the word first. -/
theorem equal_key_zero_r {x k : U256} {l : List U256} (h : x ∉ l) (hk : k ∈ l) : equal x k = 0 :=
  if_neg (fun (e : x = k) => h (e ▸ hk))

/-- The SafeMath addition of Solidity 0.4 with the optimizer on: `c = v + b; assert(c >= b)`. -/
theorem Supply.add_fact_ltc {v b : U256} (h : isZero (lessThan (add v b) b) ≠ 0) :
    ((add v b).toNat : Int) = v.toNat + b.toNat := by
  have e : add v b = add b v := by
    unfold add
    exact BitVec.add_comm _ _
  rw [e] at h ⊢
  have := TokenKit.Supply.add_fact_lt h
  omega

/-! ## Logs -/

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

/-! ## The code -/

theorem codeWord_4507 : (⟨(bufferRead CODE 4507 32).toArray⟩ : ByteArray) =
    wordBytes (0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef : U256) := by
  simp only [bufferRead, byteAt_CODE]
  decide +kernel

end WbtcVerify

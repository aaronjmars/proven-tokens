import BnbVerify.Bnb.Invariant
import TokenKit.Evm.Readable2
import TokenKit.Evm.Witness
import TokenKit.Evm.CallOutcome
import UsdtVerify.Evm.Call
import EthLib.Execution.Proofs.Evm.Logic.Call
import EthLib.Execution.Proofs.Evm.Logic.Keeps

/-!
# withdrawEther(amount): the function of BNB that sends a message

`withdrawEther` checks that the caller is the owner (slot 4) and then does
`owner.transfer(amount)`: a CALL to the owner with the value `amount`, no data, and the gas
`2300 * (amount == 0)` (for a value that is not 0 the EVM adds the stipend of 2300, so the
message gets at most 2300 gas in both cases). After the CALL it reverts when the call failed and
stops when it did not. It writes no storage and logs nothing itself. Hand-written.

What is proved, and for which notion of run:

1. Over `Ends` (the loop of steps of one frame, as for the other functions), which says nothing
   past a CALL (a frame that reaches a CALL has `Ends` to every frame):
   - `withdrawEther_needs`, `withdrawEther_only_owner`: a run that ends with no error has value 0
     and a caller that is the owner. So only the owner can make it succeed. These lift to the
     interpreter loop `runFrame` under ANY runner by `Ends.run` (`withdrawEther_only_owner_run`).
   - `withdrawEther_to_call` (the generated `Paths.withdrawEther_p2`): from pc 0, for the owner,
     the frame reaches the CALL at pc 3010 with the exact stack, memory, gas, state and substate.
   - `withdrawEther_reaches_call`: a concrete call for which this happens (not vacuous).
2. Over the interpreter loop `runFrame` under ANY message runner `runChild`
   (`withdrawEther_run`): if the run ends with no error then the caller is the owner, the runner
   was asked to run exactly one message, the message of `Payout` (from the contract to the
   owner, value `amount`, no data, at most 2300 gas, from a frame whose state reads as the start
   state), that message ended with no error, and the end of the frame is: empty return data,
   the exact gas, and the state and substate that the message left (EthLib's
   `incorporateChild`). The contract itself adds no write and no log.
   Every case of the CALL is covered (TokenKit's `call_outcome`), with no side condition on the
   amount, the frame, the balance, the depth or the gas:
   - `amount = 0`: the CALL sends its message with no value (in a static frame too);
   - `amount` above the ether of the contract, or the depth limit: the CALL pushes 0, the code
     reverts, so the run has an error;
   - `amount` not 0 in a static frame, gas below the price of the CALL, or a state that fails to
     give the code of the owner: the frame halts with an error;
   - the message of the CALL ends with an error: the code reverts.
   Two hypotheses remain, both stated in the theorems:
   - `hglam`: the fork is before Glamsterdam (EthLib's rules of CALL are for these forks; from
     Glamsterdam the gas of a CALL has two counters);
   - `hdel`: the code of the owner is no EIP-7702 delegation (from Pectra).
3. The supply invariant (`supply_withdrawEther`): a successful `withdrawEther` keeps `Inv`
   under the LOCAL assumption `KeepsInv runChild message state` on the runner. It is EthLib's
   `KeepsOn` (as upstream's `KeepsInvAt`) over the set `Payout message state`: only the one
   message that the CALL of this `withdrawEther` sends from the start state, when the runner
   ends it with no error, keeps `Inv` of the contract from the state of the calling frame to the
   state of the ended frame. It says nothing of any other message.
   The assumption is discharged for EthLib's real runner `processRunner` in
   Bnb/Sanity/Withdraw.lean, for an owner with no code and for an owner whose code is STOP.
   It is NOT proved for every owner: an owner contract runs with at most 2300 gas, which is
   below the price of a storage write, but that general fact is not proved here.

Retired in the fix round of audit 3 (finding BNB-1): the former `supply_withdrawEther` took a
hypothesis `hrunner` over EVERY message of the runner, which is false for `processRunner`
(machine-checked in audit-3/lean/BnbRunnerFalse.lean). That statement is gone; the theorem of
the same name here takes `KeepsInv` instead. The former `withdrawEther_run` had seven side
conditions (`hv`, `hstatic`, `hbal`, `hcode`, `hdel`, `hdepth`, `hcallgas`); the theorem of the
same name here has `hdel` only, in a weaker form, and the same conclusion (the gas is now
written with TokenKit's `callGas`; the price of the memory of the CALL is 0).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace BnbVerify

open UsdtVerify
open TokenKit TokenKit.Complete

open EthLib.Base (Fork U256 Address)
open EthLib.Execution

/-- The invariant reads the storage words of `C` only. -/
theorem Supply.inv2_congr {b1 b2 t : U256} {C : Address} {S S' : State.TransactionState}
    (h : ∀ n, storageAt S' C n = storageAt S C n) :
    Supply.Inv2 b1 b2 t C S' ↔ Supply.Inv2 b1 b2 t C S := by
  have e (b : U256) : Supply.sumBal b C S' = Supply.sumBal b C S :=
    Supply.sumTo_congr (f := Supply.bal b C S') (g := Supply.bal b C S) _ (fun i _ => by
      show ((storageAt S' C _).toNat : Int) = ((storageAt S C _).toNat : Int)
      rw [h])
  unfold Supply.Inv2 Supply.D2
  rw [e b1, e b2, h t]

end BnbVerify

namespace BnbVerify.Withdraw

open UsdtVerify
open TokenKit TokenKit.Complete
open BnbVerify BnbVerify.Paths BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-! ## The code after the CALL -/

theorem t3011_ok {f x1 x2 x3 x4 : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hc : isZero (isZero f) ≠ 0)
    (hrest : rest.length ≤ 900)
    (hg : 30 ≤ gas) :
    Gas.HoareG fork (At CODE message 3011 (f :: x1 :: x2 :: x3 :: x4 :: rest) mem gas state substate)
      (At CODE message 3026 (rest) mem (gas - 30) state substate) := by
  step swap4K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step popR
  step popR
  step popR
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (3026 : U256)
  at_pc 3021
  step jumpiR hc
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

theorem t3011_rev {f x1 x2 x3 x4 : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hc : isZero (isZero f) = 0)
    (hrest : rest.length ≤ 900)
    (hg : 30 ≤ gas) :
    Gas.HoareG fork (At CODE message 3011 (f :: x1 :: x2 :: x3 :: x4 :: rest) mem gas state substate)
      (At CODE message 3022 (rest) mem (gas - 30) state substate) := by
  step swap4K (by code_fact) (by code_fact) (by gas_ok)
  step popR
  step popR
  step popR
  step popR
  step unR 0x15 instruction_iszero
  step unR 0x15 instruction_iszero
  step pushR 2 (3026 : U256)
  at_pc 3021
  step jumpi0R hc
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

theorem t3022 {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hfork : .berlin ≤ fork)
    (hrest : rest.length ≤ 900)
    (hg : 6 ≤ gas) :
    Gas.SpecG fork (At CODE message 3022 (rest) mem gas state substate)
      (Halted true ByteArray.empty (gas - 6) state substate) := by
  step pushR 1 (0 : U256)
  at_pc 3024
  step dupR 0
  step Gas.reshapeG (g' := gas - 6) rfl rfl (by gas_ok)
  exact revert0K hfork (by code_fact) (by code_fact)

theorem t3026 {a : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hrest : rest.length ≤ 900)
    (hg : 12 ≤ gas) :
    Gas.HoareG fork (At CODE message 3026 (a :: (701 : U256) :: rest) mem gas state substate)
      (At CODE message 701 (rest) mem (gas - 12) state substate) := by
  step jumpdestR
  step jumpdestR
  step popR
  step jumpR
  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl

theorem t701 {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hg : 1 ≤ gas) :
    Gas.SpecG fork (At CODE message 701 (rest) mem gas state substate)
      (Halted false ByteArray.empty (gas - 1) state substate) := by
  step jumpdestR
  step Gas.reshapeG (g' := gas - 1) rfl rfl (by gas_ok)
  exact Gas.stopG (by code_fact) (by code_fact)

/-- After a CALL that did not fail (flag not 0): 43 gas to STOP, nothing written. -/
theorem tail_ok {f x1 x2 x3 x4 a : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hc : isZero (isZero f) ≠ 0)
    (hrest : rest.length ≤ 800)
    (hg : 43 ≤ gas) :
    Gas.SpecG fork
      (At CODE message 3011 (f :: x1 :: x2 :: x3 :: x4 :: a :: (701 : U256) :: rest) mem gas
        state substate)
      (Halted false ByteArray.empty (gas - 43) state substate) := by
  step t3011_ok hc (by simp only [List.length_cons]; omega) (by omega)
  step t3026 (by omega) (by omega)
  exact haltGas (t701 (by omega)) (by omega)

/-- After a CALL that failed (flag 0): 36 gas to REVERT with no data. -/
theorem tail_rev {f x1 x2 x3 x4 : U256} {rest : List U256} {mem : ByteArray} {gas : Nat}
    (hfork : .berlin ≤ fork)
    (hc : isZero (isZero f) = 0)
    (hrest : rest.length ≤ 800)
    (hg : 36 ≤ gas) :
    Gas.SpecG fork
      (At CODE message 3011 (f :: x1 :: x2 :: x3 :: x4 :: rest) mem gas state substate)
      (Halted true ByteArray.empty (gas - 36) state substate) := by
  step t3011_rev hc (by omega) (by omega)
  exact haltGas (t3022 hfork (by omega) (by omega)) (by omega)

/-! ## Only the owner -/

/-- From Berlin: a run of `withdrawEther` that ends with no error (`Ends`) had the two checks
pass, in the shape of the bytecode. -/
theorem withdrawEther_needs (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    (isZero message.value) ≠ 0 ∧
      (isZero (isZero (equal (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (storageAt state message.currentTarget (4 : U256)) (1 : U256))))))) ≠ 0 := by
  have hsize : 1 ≤ message.data.size := size_of_selector hsel (by decide)
  by_cases hc1 : (isZero message.value) = 0
  · exact (no_okE (B := 216) (fun g hg => withdrawEther_p0 hfork hsize hsize' hsel hc1 (by omega))
      (fun _ e h => halted_true_error e h) start hrun hok).elim
  · by_cases hc2 : (isZero (isZero (equal (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (storageAt state message.currentTarget (4 : U256)) (1 : U256))))))) = 0
    · exact (no_okE (B := (341 + (slotCost (coldIn substate message.currentTarget (4 : U256)))))
        (fun g hg => withdrawEther_p1 hfork hsize hsize' hsel hc1 hc2 (by omega))
        (fun _ e h => halted_true_error e h) start hrun hok).elim
    · exact ⟨hc1, hc2⟩

theorem eq_of_cond {a b : U256} (h : isZero (isZero (equal a b)) ≠ 0) : a = b := by
  by_cases e : a = b
  · exact e
  · exfalso
    apply h
    have e' : equal a b = 0 := if_neg e
    rw [e']
    decide

/-- Only the owner: from Berlin, a run of `withdrawEther` that ends with no error (`Ends`) has
value 0 and a caller whose address word is the low 160 bits of slot 4 (the owner). -/
theorem withdrawEther_only_owner (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    message.value = 0 ∧
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 =
        bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          (storageAt state message.currentTarget 4) := by
  obtain ⟨hc1, hc2⟩ := withdrawEther_needs hfork hsize' hsel start hrun hok
  refine ⟨Readable.value_of_cond hc1, ?_⟩
  have h := eq_of_cond hc2
  rw [Readable.div_one, mask_idem] at h
  exact h

/-- `withdrawEther_only_owner` for the interpreter loop under any message runner. -/
theorem withdrawEther_only_owner_run (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.value = 0 ∧
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 =
        bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
          (storageAt state message.currentTarget 4) :=
  withdrawEther_only_owner hfork hsize' hsel start (Ends.run hrun) hok

/-! ## Through the CALL, under any runner -/

/-- The state at the CALL: the start state with slot 4 recorded as read (twice). -/
abbrev atCall (m : Message fork) (S : State.TransactionState) : State.TransactionState :=
  readSlot (readSlot S m.currentTarget (4 : U256)) m.currentTarget (4 : U256)

/-- The substate at the CALL: slot 4 accessed. -/
abbrev subAtCall (m : Message fork) (ss : Substate) : Substate :=
  accessSlot (accessSlot ss m.currentTarget (4 : U256)) m.currentTarget (4 : U256)

/-- The word of the owner, as the bytecode leaves it on the stack. -/
abbrev ownerWord (m : Message fork) (S : State.TransactionState) : U256 :=
  bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (div (storageAt (readSlot S m.currentTarget (4 : U256)) m.currentTarget (4 : U256)) (1 : U256)))

/-- The owner word is the low 160 bits of slot 4. -/
theorem ownerWord_eq (m : Message fork) (S : State.TransactionState) :
    ownerWord m S = bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (storageAt S m.currentTarget 4) := by
  simp only [ownerWord, storageAt_readSlot, Readable.div_one, mask_idem]

/-- The gas from pc 0 to the CALL. -/
abbrev prefixCost (m : Message fork) (ss : Substate) : Nat :=
  (440 + (slotCost (coldIn ss m.currentTarget (4 : U256))) + (slotCost (coldIn (accessSlot ss m.currentTarget (4 : U256)) m.currentTarget (4 : U256))))

/-- The gas word that the CALL asks for: 2300 when the amount is 0, and 0 if not. -/
abbrev askedWord (m : Message fork) : U256 :=
  mul (isZero (loadWord m.data 4 32)) (2300 : U256)

/-- The gas of the CALL (TokenKit's `callGas`, EthLib's `messageCallGas`): what the frame pays
(`cost`) and what the message gets (`subCall`). The two ranges of the CALL are empty, so its
memory costs nothing. -/
abbrev callGas (fork : Fork) (m : Message fork) (S : State.TransactionState) (ss : Substate)
    (gas : Nat) : MessageCallGas :=
  TokenKit.callGas fork (atCall m S) (subAtCall m ss) (askedWord m) (ownerWord m S)
    (loadWord m.data 4 32) (gas - prefixCost m ss)

/-- The owner: the address in the low 160 bits of slot 4. -/
abbrev ownerOf (m : Message fork) (S : State.TransactionState) : Address :=
  toAddressMasked (storageAt S m.currentTarget 4)

/-- The address that the CALL goes to is the owner. -/
theorem toAddressMasked_ownerWord (m : Message fork) (S : State.TransactionState) :
    toAddressMasked (ownerWord m S) = ownerOf m S := by
  rw [ownerWord_eq]
  exact toAddressMasked_mask _

/-- The gas asked for plus the stipend is at most 2300: the CALL asks for 2300 when the amount
is 0 (no stipend) and for 0 when it is not (stipend 2300). -/
theorem askedWord_le (m : Message fork) :
    (askedWord m).toNat + (if loadWord m.data 4 32 = 0 then 0 else CALL_STIPEND) ≤ 2300 := by
  by_cases h : loadWord m.data 4 32 = 0
  · show (mul (isZero (loadWord m.data 4 32)) (2300 : U256)).toNat + _ ≤ 2300
    rw [h, if_pos rfl]
    decide
  · have hz : isZero (loadWord m.data 4 32) = 0 :=
      Classical.byContradiction fun hne => h (Readable.value_of_cond hne)
    show (mul (isZero (loadWord m.data 4 32)) (2300 : U256)).toNat + _ ≤ 2300
    rw [hz, if_neg h]
    decide

/-- A state that reads as `S` has the storage words of `S`. -/
theorem readsAs_storageAt {tx S : State.TransactionState} (h : ReadsAs tx S) (C : Address)
    (n : U256) : storageAt tx C n = storageAt S C n := by
  unfold storageAt
  rw [(h.1 C List.not_mem_nil).2.1]

/-- A state that reads as `S` has the accounts of `S`. -/
theorem readsAs_getAccount {tx S : State.TransactionState} (h : ReadsAs tx S) (a : Address) :
    tx.getAccount a = S.getAccount a := by
  unfold State.TransactionState.getAccount
  rw [(h.1 a List.not_mem_nil).1]

/-- The state of the calling frame once it takes in the frame that ended the message is the
state of that frame, with or without an error (a failed message was rolled back before). -/
theorem incorporateChild_state (caller child : Evm fork Nat) :
    (incorporateChild fork caller child).state = child.state := by
  unfold incorporateChild
  split <;> rfl

/-! ## The message of the CALL and the local assumption on the runner -/

/-- The one message `msg` that the CALL of the call `message` of `withdrawEther` sends from the
start state `S`, and the frame `caller` that hands it to the runner.

The state of `caller` reads as `S`: it has the accounts, the storage and the code of `S` (it
differs in the reads that it records). The message goes from the contract to the owner in `S`,
runs the code that the owner holds in `S`, has no data, carries the `amount` of the call, is
one deeper, is static when the call is, and gets at most 2300 gas. -/
def Payout (message : Message fork) (S : State.TransactionState) (caller : Evm fork Nat)
    (msg : Message fork) : Prop :=
  ∃ c, S.getCode (S.getAccount (ownerOf message S)).codeHash = .ok c ∧
    ReadsAs caller.state S ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = ownerOf message S ∧
    msg.target = some (ownerOf message S) ∧ msg.codeAddress = some (ownerOf message S) ∧
    msg.code = c ∧ msg.data = .empty ∧ msg.value = loadWord message.data 4 32 ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧ msg.gas ≤ 2300

/-- `Inv C` is kept from the state `tx` to the state `tx'`. -/
def InvKept (C : Address) (tx tx' : State.TransactionState) : Prop := Inv C tx → Inv C tx'

/-- The local assumption on the runner (EthLib's `KeepsOn`): the message of `Payout message S`,
when the runner ends it with no error, keeps `Inv` of the contract from the state of the calling
frame to the state of the ended frame. It is about that one message only. -/
def KeepsInv {bound : Nat} (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (S : State.TransactionState) : Prop :=
  KeepsOn runChild (Payout message S) (InvKept message.currentTarget)

/-- From pc 0 to the CALL, for the owner and with the gas: the generated path. -/
theorem withdrawEther_to_call (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hv : message.value = 0)
    (howner : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (storageAt state message.currentTarget 4))
    {gas : Nat} (hg : prefixCost message substate ≤ gas) :
    Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)
      (At CODE message 3010
        (askedWord message :: ownerWord message state :: loadWord message.data 4 32 ::
          (96 : U256) :: (0 : U256) :: (96 : U256) :: (0 : U256) :: (96 : U256) ::
          loadWord message.data 4 32 :: askedWord message :: ownerWord message state ::
          loadWord message.data 4 32 :: (701 : U256) ::
          BitVec.ofNat 256 (selector message.data) :: [])
        (memW [(0 : U256), (0 : U256), (96 : U256)]) (gas - prefixCost message substate)
        (atCall message state) (subAtCall message substate)) := by
  have hsize : 1 ≤ message.data.size := size_of_selector hsel (by decide)
  refine withdrawEther_p2 hfork hsize hsize' hsel (by rw [hv]; decide) ?_ hg
  rw [Readable.div_one, mask_idem, howner]
  intro h
  have e : equal (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      (storageAt state message.currentTarget 4))
      (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (storageAt state message.currentTarget 4)) = 1 := if_pos rfl
  rw [e] at h
  exact absurd h (by decide)

/-- From Berlin and before Glamsterdam, under ANY message runner: a run of `withdrawEther` by the
interpreter loop that ends with no error. There is no side condition on the amount, the frame,
the balance, the depth or the gas: in every case where the CALL sends no message, or its message
fails, the run has an error (see the head of the file). `hdel`: the code of the owner is no
EIP-7702 delegation.

Then: value 0, the caller is the owner, the runner ran one message `msg` from the frame `caller`
and gave the frame `child` with no error; `msg` is the message of `Payout` (from the contract to
the owner, with the value `amount`, at most 2300 gas) with the gas `(callGas ..).subCall`; the
frame ends with no return data, the exact gas, and the state and substate of
`incorporateChild`. -/
theorem withdrawEther_run (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hdel : ∀ c, state.getCode (state.getAccount (ownerOf message state)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    message.value = 0 ∧
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
        (storageAt state message.currentTarget 4) ∧
    ∃ caller msg lt child, runChild caller msg lt = .ok child ∧
      child.1.error = none ∧
      Payout message state caller msg ∧
      caller.state = ((atCall message state).recordAccountRead
        (toAddressMasked (ownerWord message state))).recordAccountRead message.currentTarget ∧
      (loadWord message.data 4 32 ≠ 0 → msg.shouldTransferValue = true) ∧
      msg.gas = (callGas fork message state substate gas).subCall ∧
      child.1.gas ≤ msg.gas ∧
      s.output = ByteArray.empty ∧
      s.gas = gas - prefixCost message substate -
        (callGas fork message state substate gas).cost + child.1.gas - 43 ∧
      s.state = (incorporateChild fork caller child.1).state ∧
      s.substate = (incorporateChild fork caller child.1).substate := by
  have hsize : 1 ≤ message.data.size := size_of_selector hsel (by decide)
  obtain ⟨hc1, hc2⟩ := withdrawEther_needs hfork hsize' hsel start (Ends.run hrun) hok
  obtain ⟨hval, howner⟩ := withdrawEther_only_owner hfork hsize' hsel start (Ends.run hrun) hok
  refine ⟨hval, howner, ?_⟩
  obtain ⟨hcg, z, w, hz, hrunz⟩ := ok_split (B := prefixCost message substate)
    (c := prefixCost message substate) (Nat.le_refl _)
    (fun g hg => withdrawEther_p2 hfork hsize hsize' hsel hc1 hc2 hg) start within hrun hok
  have hto := toAddressMasked_ownerWord message state
  have hdel' : ∀ c, (atCall message state).getCode ((atCall message state).getAccount
      (toAddressMasked (ownerWord message state))).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none := by
    intro c hc
    rw [hto] at hc
    exact hdel c hc
  rcases call_outcome (code := CODE) (pc := 3010) (asked := askedWord message)
      (to := ownerWord message state) (v := loadWord message.data 4 32)
      (rest := (96 : U256) :: loadWord message.data 4 32 :: askedWord message ::
        ownerWord message state :: loadWord message.data 4 32 :: (701 : U256) ::
        BitVec.ofNat 256 (selector message.data) :: [])
      hfork hglam (by code_fact) (by code_fact) hdel' hz w hrunz with
    herr | ⟨mem, g, st, ss, after, hat, w2, hrun2⟩ |
    ⟨calleeCode, caller, msg, child, after, hcode, ⟨lt, c, hch, rfl⟩, hle, hsend, hat, w2, hrun2⟩
  · exact absurd hok herr
  · exact (no_okE (B := 36) (fun g hg => tail_rev hfork (by decide) (by simp) hg)
      (fun _ e h => halted_true_error e h) hat (Ends.run hrun2) hok).elim
  · obtain ⟨cst, csub, mgas, mcaller, mtarget, mt, mca, mcode, mdata, mval, mtv, mdep, mstat⟩ :=
      hsend
    by_cases hce : c.1.error = none
    · have hflag : isZero (isZero (if c.1.error.isNone = true then (1 : U256) else 0)) ≠ 0 := by
        rw [hce]
        decide
      obtain ⟨-, -, ho, hgas, hst, hss⟩ := ok_exactE (B := 43) (cost := 43) (by omega)
        (fun g hg => tail_ok hflag (by simp) hg) hat (Ends.run hrun2) hok
      have hcode' : state.getCode (state.getAccount (ownerOf message state)).codeHash =
          .ok calleeCode := by
        rw [hto] at hcode
        exact hcode
      have hreads : ReadsAs caller.state state := by
        rw [cst]
        exact ((((ReadsAs.refl state).recordStorageRead _ _).recordStorageRead _ _
          ).recordAccountRead _).recordAccountRead _
      have hmg : msg.gas ≤ 2300 := by
        rw [mgas]
        exact Nat.le_trans (callGas_subCall_le _ _ _ _ _ _ _) (askedWord_le message)
      exact ⟨caller, msg, lt, c, hch, hce,
        ⟨calleeCode, hcode', hreads, mcaller, by rw [mtarget, hto], by rw [mt, hto],
          by rw [mca, hto], mcode, mdata, mval, mdep, mstat, hmg⟩,
        cst, mtv, mgas, hle, ho, hgas, hst, hss⟩
    · have hflag : isZero (isZero (if c.1.error.isNone = true then (1 : U256) else 0)) = 0 := by
        have hn : c.1.error.isNone = false := by
          cases he : c.1.error with
          | none => exact absurd he hce
          | some _ => rfl
        rw [hn]
        decide
      exact (no_okE (B := 36) (fun g hg => tail_rev hfork hflag (by simp) hg)
        (fun _ e h => halted_true_error e h) hat (Ends.run hrun2) hok).elim

/-- The supply invariant through `withdrawEther`, from Berlin and before Glamsterdam, under the
local assumption `KeepsInv runChild message state` on the runner: the one message that the CALL
of this call sends (`Payout message state`), when it ends with no error, keeps `Inv`. The
contract itself writes nothing. `hdel` as in `withdrawEther_run`. The assumption is discharged
for `processRunner` in Bnb/Sanity/Withdraw.lean (owner with no code, owner with the code STOP). -/
theorem supply_withdrawEther (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x3bed33ce)
    (hdel : ∀ c, state.getCode (state.getAccount (ownerOf message state)).codeHash = .ok c →
      .pectra ≤ fork → delegatedAddress c = none)
    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}
    (hkeeps : KeepsInv runChild message state)
    (hinv : Inv message.currentTarget state)
    (start : At CODE message 0 [] .empty gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  obtain ⟨-, -, caller, msg, lt, child, hch, herr, hpay, -, -, -, -, -, -, hst, -⟩ :=
    withdrawEther_run hfork hglam hsize' hsel hdel start within hrun hok
  rw [hst, incorporateChild_state]
  refine hkeeps caller msg lt child hch hpay herr ?_
  obtain ⟨-, -, hreads, -⟩ := hpay
  exact (Supply.inv2_congr (fun n => readsAs_storageAt hreads _ n)).mpr hinv

/-! ## A concrete call that reaches the CALL -/

/-- The four bytes of the selector of `withdrawEther(uint256)`. -/
def SEL_withdrawEther : ByteArray := ⟨#[0x3b, 0xed, 0x33, 0xce]⟩

theorem size_SEL_withdrawEther : SEL_withdrawEther.size = 4 := by decide

/-- The call `withdrawEther(1)` from `caller` to `C`, with no value. -/
abbrev m_withdrawEther (b : BlockEnvironment fork) (t : TransactionEnvironment fork)
    (C caller : Address) : Message fork :=
  sMsg b t C caller CODE (data1 SEL_withdrawEther 1)

/-- The state of the witness: one account at `C` whose slot 4 (owner) is the word of `caller`. -/
abbrev s_withdrawEther (C caller : Address) : State.TransactionState :=
  sState C [((4 : U256),
    bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)]

/-- The path to the CALL is not empty: when the owner calls `withdrawEther(1)`, the frame runs
from pc 0 to the CALL at pc 3010, with the stack of a CALL of 1 wei to the owner. -/
theorem withdrawEther_reaches_call (hfork : .berlin ≤ fork) (b : BlockEnvironment fork)
    (t : TransactionEnvironment fork) (C caller : Address) (ss : Substate) :
    ∃ (gas : Nat) (evm z : Evm fork Nat) (rest : List U256),
      At CODE (m_withdrawEther b t C caller) 0 [] .empty gas (s_withdrawEther C caller) ss evm ∧
      Reaches (Step fork) evm z ∧
      At CODE (m_withdrawEther b t C caller) 3010
        ((0 : U256) ::
          bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 ::
          (1 : U256) :: (96 : U256) :: (0 : U256) :: (96 : U256) :: (0 : U256) :: rest)
        (memW [(0 : U256), (0 : U256), (96 : U256)]) 0
        (atCall (m_withdrawEther b t C caller) (s_withdrawEther C caller))
        (subAtCall (m_withdrawEther b t C caller) ss) z := by
  have hdata : (m_withdrawEther b t C caller).data = data1 SEL_withdrawEther 1 := rfl
  have hsz : (m_withdrawEther b t C caller).data.size = 36 := by
    rw [hdata]; exact size_data1 size_SEL_withdrawEther _
  have hsl : selector (m_withdrawEther b t C caller).data = selector SEL_withdrawEther := by
    rw [hdata]; exact selector_data1 size_SEL_withdrawEther _
  have hA1 : loadWord (m_withdrawEther b t C caller).data 4 32 = 1 := by
    rw [hdata]; exact Witness.arg1_data1 size_SEL_withdrawEther _
  have hk : storageAt (s_withdrawEther C caller) (m_withdrawEther b t C caller).currentTarget 4 =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 := by
    show storageAt (sState C [((4 : U256),
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256)]) C 4 = _
    rw [storageAt_sState_cons, if_pos rfl]
  have hspec := withdrawEther_to_call (fork := fork) (message := m_withdrawEther b t C caller)
    (state := s_withdrawEther C caller) (substate := ss) hfork
    (by rw [hsz]; decide) (by rw [hsl]; decide) rfl
    (by rw [hk]; exact (mask_idem _).symm) (Nat.le_refl _)
  obtain ⟨z, hr, hz⟩ := hspec (sFrame (m_withdrawEther b t C caller) (s_withdrawEther C caller) ss _)
    (at_sFrame _ rfl _ _ _)
  have e1 : askedWord (m_withdrawEther b t C caller) = 0 := by
    show mul (isZero (loadWord (m_withdrawEther b t C caller).data 4 32)) (2300 : U256) = 0
    rw [hA1]; decide
  have e2 : ownerWord (m_withdrawEther b t C caller) (s_withdrawEther C caller) =
      bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) caller.toU256 := by
    rw [ownerWord_eq, hk, mask_idem]
  rw [e1, e2, hA1, Nat.sub_self] at hz
  exact ⟨_, _, z, _, at_sFrame _ rfl _ _ _, reaches_toStep hr, hz⟩

end BnbVerify.Withdraw

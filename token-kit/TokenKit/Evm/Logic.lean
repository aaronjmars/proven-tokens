import UsdtVerify.Evm.Exact
import UsdtVerify.Evm.Split
import EthLib.Execution.Proofs.Evm.Instructions.AccountData
import EthLib.Execution.Proofs.Evm.Logic.Rules
import EthLib.Execution.Proofs.Evm.Logic.RunMono
import EthLib.Execution.Proofs.Evm.Logic.LessGas
import EthLib.Base.Proofs.Address
import TokenKit.Evm.Rules

/-!
# Opcodes outside the simulated set: ADDRESS and BALANCE

The rules of usdt-verify are over its `StepG`, which holds only at the opcodes of its simulated
set. ADDRESS, BALANCE and CALL are not in that set. The rules here are over EthLib's
`Logic.StepG` (a step from a frame that is monotone in gas), which has no such limit, and over
the `At` of usdt-verify.

- `StepLift` instance: a rule over the `StepG` of usdt-verify also runs in a goal over
  `Logic.StepG`, so the tactic `step` chains both kinds.
- `addressL`: ADDRESS (EthLib's `addressG`).
- `runMono_balance`, `balanceL`: BALANCE from Berlin. EthLib has no rule for it at the pinned
  revision; it is proved here from EthLib's `balanceStep_cons`, as EthLib proves SLOAD.
- `etherOf S a`: the ether balance of the account `a` in the state `S`, as a word.
- `accessAccount`, `coldAccount`: the substate after an access to an account and whether the
  account was cold.
- `toAddressMasked_mask`: the address of a word masked to 160 bits.
- `ok_exactL`, `no_okL`: a specification over `Logic.StepG`, held for every gas from a bound on,
  fixes the end of every run of the interpreter loop that ends with no error (EthLib's
  `halted_of_specG` and `no_ok_of_specG`, for the `At` of usdt-verify).

Nothing here is about one token.
-/

namespace TokenKit

open UsdtVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {code : ByteArray} {message : Message fork} {pc : Nat}
  {stack : List U256} {memory : ByteArray} {gas : Nat} {state : State.TransactionState}
  {substate : Substate}

/-- Every step of the `StepG` of usdt-verify is a step of EthLib's `Logic.StepG`. -/
instance stepLiftLogic : Gas.StepLift (Gas.StepG fork) (Logic.StepG fork) :=
  ⟨fun h => ⟨h.1, h.2.2⟩⟩

/-- The ether balance of the account `a` in the state `S`, as a word. -/
abbrev etherOf (S : State.TransactionState) (a : Address) : U256 := (S.getAccount a).balance

/-- The substate after an access to the account `a`. -/
abbrev accessAccount (substate : Substate) (a : Address) : Substate :=
  { substate with accessedAddresses := substate.accessedAddresses.insert a }

/-- Whether the account `a` is cold: not yet accessed in this transaction. -/
abbrev coldAccount (substate : Substate) (a : Address) : Bool :=
  decide (a ∉ substate.accessedAddresses)

/-- The address of a word masked to 160 bits is the address of the word. -/
theorem toAddressMasked_mask (w : U256) :
    toAddressMasked (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w) =
      toAddressMasked w := by
  apply EthLib.Base.Address.toU256_injective
  apply BitVec.eq_of_toNat_eq
  rw [EthLib.Base.toNat_toU256_toAddressMasked, EthLib.Base.toNat_toU256_toAddressMasked]
  have h : (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) w).toNat =
      w.toNat % 2 ^ 160 := by
    simp only [bitwiseAnd, BitVec.toNat_and]
    rw [Nat.and_comm]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 160
  rw [h, Nat.mod_mod]

/-- The address of the masked word of an address is the address. -/
theorem toAddressMasked_mask_toU256 (a : Address) :
    toAddressMasked (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
      a.toU256) = a := by
  rw [toAddressMasked_mask, EthLib.Base.toAddressMasked_toU256]

/-- The rule of one opcode over `Logic.StepG`, for the `At` of usdt-verify: EthLib's
`Logic.At.ruleG`, for an instruction that is monotone in gas. -/
theorem ruleL {byte : UInt8} {op : Op}
    {run : Evm fork Nat → Except EvmError (Evm fork Nat)} {post : Evm fork Nat → Prop}
    (hlt : pc < code.size) (hbyte : code[pc] = byte) (decoded : Op.ofByte fork byte = some op)
    (hrun : instruction fork op = some run) (hm : RunMono run)
    (h : ∀ evm, At code message pc stack memory gas state substate evm →
      ∃ after, run evm = .ok after ∧ post after) :
    Logic.HoareG fork (At code message pc stack memory gas state substate) post :=
  liftPre fun _ => Logic.At.ruleG hlt hbyte decoded hrun hm fun evm hat => h evm (At.ofLogic hat)

/-- ADDRESS pushes the address of the current account as a word, for 2 gas. -/
theorem addressL (hlt : pc < code.size) (hbyte : code[pc] = 0x30) (hgas : 2 ≤ gas)
    (hstack : stack.length < STACK_LIMIT) :
    Logic.HoareG fork (At code message pc stack memory gas state substate)
      (At code message (pc + 1) (message.currentTarget.toU256 :: stack) memory (gas - 2) state
        substate) :=
  liftAt fun _ => Logic.addressG hlt hbyte hgas hstack

/-- BALANCE is monotone in gas. -/
theorem runMono_balance : RunMono (fork := fork) balanceStep := by
  intro evm k
  rcases hs : evm.stack with ⟨_ | ⟨x, rest⟩, hp⟩
  · refine .inl (.inl ⟨.stackUnderflow, ?_⟩)
    simp [balanceStep, popWord, Stack.pop, hs, bind, Except.bind]
  · have h : evm.stack.val = x :: rest := by rw [hs]
    rw [balanceStep_cons h, balanceStep_cons (evm := addGas k evm) h]
    simp only [accessAddress]
    split <;> exact follows_map_charge fun _ => rfl

/-- BALANCE from Berlin: the word on top of the stack, read as an address, is replaced by the
ether balance of that account in the state; the account is recorded as read and accessed; the
price is the one of a cold or a warm access. -/
theorem balanceL (hfork : .berlin ≤ fork) {word : U256} {rest : List U256}
    (hlt : pc < code.size) (hbyte : code[pc] = 0x31)
    (hgas : accountAccessCost fork (coldAccount substate (toAddressMasked word)) ≤ gas) :
    Logic.HoareG fork (At code message pc (word :: rest) memory gas state substate)
      (At code message (pc + 1) ((state.getAccount (toAddressMasked word)).balance :: rest) memory
        (gas - accountAccessCost fork (coldAccount substate (toAddressMasked word)))
        (state.recordAccountRead (toAddressMasked word))
        (accessAccount substate (toAddressMasked word))) := by
  apply ruleL hlt hbyte (ofByte_of_decode (op := .balance) rfl (Fork.frontier_le _)) rfl
    runMono_balance
  rintro evm ⟨hcode, hj, hm, hpc, hst, hmem, hg, hrun, herr, hout, hs, hss⟩
  subst hm hg hs hss
  rw [balanceStep_cons hst]
  simp only [accessAddress, ge_iff_le, hfork, ↓reduceIte, balanceCost_of_berlin_le hfork]
  rw [charge_nat hgas]
  refine ⟨_, rfl, hcode, hj, rfl, by simp [hpc], ?_, hmem, ?_, hrun, herr, hout, rfl, rfl⟩
  · show _ :: rest = _ :: rest
    rfl
  · simp

namespace Complete

variable {bound : Nat} {runChild : MessageRunner fork Nat bound} {evm s : Evm fork Nat}

/-- A successful run ends as a specification over `Logic.StepG` to a normal halt states, with
the exact gas (EthLib's `halted_of_specG`, for the `At` of usdt-verify). -/
theorem ok_exactL {B cost : Nat} {out : ByteArray}
    {st' : State.TransactionState} {ss' : Substate}
    (h : ∀ g, B ≤ g → Logic.SpecG fork (At code message pc stack memory g state substate)
      (Halted false out (g - cost) st' ss'))
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) :
    cost ≤ gas ∧ s.running = false ∧ s.output = out ∧ s.gas = gas - cost ∧ s.state = st' ∧
      s.substate = ss' :=
  halted_of_specG (B := B) (fun g hg _ => lowerPre (h g hg)) start.toLogic within hrun hok

/-- No successful run from a frame where a specification over `Logic.StepG` to an error holds
(EthLib's `no_ok_of_specG`, for the `At` of usdt-verify). -/
theorem no_okL {B : Nat} {Q : Nat → Evm fork Nat → Prop}
    (h : ∀ g, B ≤ g → Logic.SpecG fork (At code message pc stack memory g state substate) (Q g))
    (herr : ∀ g e, Q g e → e.error ≠ none)
    (start : At code message pc stack memory gas state substate evm)
    (within : GasMeter.gasHeld evm.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound runChild evm within = .ok s)
    (hok : s.error = none) : False :=
  no_ok_of_specG (fun g hg => lowerPre (h g hg)) herr start.toLogic within hrun hok

end Complete

end TokenKit

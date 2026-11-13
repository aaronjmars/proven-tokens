import LinkVerify.Link.Sanity.TacLib
import LinkVerify.Link.Sanity.Addr

/-!
# Sanity: transferAndCall runs, with the CALL, under EthLib's real runner

The theorems on `transferAndCall` (selector 0x4000aea0) have many hypotheses. This file gives
concrete calls on concrete states where they all hold, so those theorems are not empty, and
runs them with the loop of the interpreter from pc 0. Written by hand (not generated).

The call is always `transferAndCall(to, 1, "")` from `Witness.CALLER1`: the call data are the
selector and the four words `to`, `1`, `0x60`, `0` (132 bytes). The recipient `to` is the address
of the word 0x1000 (no precompile). The contract is at an address `C` whose word is the word of
LINK on mainnet (`hC`); the closed forms take `LINK_ADDRESS`.

- W1 `transferAndCall_stop_runs` (`_closed`): the recipient has the code of one byte STOP. Under
  `processRunner`, from Paris and before Glamsterdam, the run ends with no error and the output
  `true`; the caller has 4 tokens left of 5 and the recipient has 1.
- W2 `transferAndCall_nocode_runs` (`_closed`): the recipient has no code. For every runner and
  every bound the run ends with no error and the output `true`, with the same two balances.
- W3a `transferAndCall_low_runs` (`_closed`): the caller has 0 tokens. For every runner the run
  ends with the error of the invalid opcode 0xfe (SafeMath of 2017).
- W3b `transferAndCall_reverts` (`_closed`): the recipient has the code of one byte INVALID, so
  its message fails. Under `processRunner` the whole call ends with the error REVERT.
- W4 `calleeKeeps_stop`: the assumption on the message of the CALL, with the code of the message
  named (`CalleeKeepsOf`), holds for a STOP recipient under `processRunner` with no hypothesis on
  keccak. `supply_tac_530_of` and `supply_transferAndCall_stop` carry it to the sum invariant.
  The literal `CalleeKeeps` of Any.lean is NOT proved from "the recipient is STOP": it speaks of
  every message to the recipient with the call data, whatever its code, so it does not follow
  from the code that the state gives for the recipient (see the note at W4).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 8192

namespace LinkVerify.Sanity

open UsdtVerify
open TokenKit
open LinkVerify LinkVerify.Tac LinkVerify.Paths

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.State (EMPTY_CODE_HASH)
open EthLib.Execution.State.TransactionState
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork}

/-! ## The call -/

/-- The four bytes of the selector of `transferAndCall(address,uint256,bytes)`. -/
def SEL_transferAndCall : ByteArray := ⟨#[0x40, 0x00, 0xae, 0xa0]⟩

theorem size_SEL_transferAndCall : SEL_transferAndCall.size = 4 := by decide

/-- The call `transferAndCall(0x1000, amount, "")` from `Witness.CALLER1` to `C`. -/
abbrev m_tac (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (amount : U256) : Message fork :=
  sMsg b t C Witness.CALLER1 CODE (data4 SEL_transferAndCall 0x1000 amount 0x60 0)

section Facts

variable (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
  (amount : U256)

theorem tac_data :
    (m_tac b t C amount).data = data4 SEL_transferAndCall 0x1000 amount 0x60 0 := rfl

theorem tac_size : (m_tac b t C amount).data.size = 132 := by
  rw [tac_data]
  exact size_data4 size_SEL_transferAndCall _ _ _ _

theorem tac_sel : selector (m_tac b t C amount).data = 0x4000aea0 := by
  rw [tac_data, selector_data4 size_SEL_transferAndCall]
  decide

/-- The recipient of the call. -/
theorem tac_to : tacTo (m_tac b t C amount) = 0x1000 := by
  unfold tacTo
  rw [tac_data, Witness.arg1_data4 size_SEL_transferAndCall]
  decide

/-- The amount of the call. -/
theorem tac_value : tacValue (m_tac b t C amount) = amount := by
  unfold tacValue
  rw [tac_data, Witness.arg2_data4 size_SEL_transferAndCall]

/-- The `bytes` argument of the call is empty. -/
theorem tac_len : tacLen (m_tac b t C amount) = 0 := by
  have e : (add (4 : U256) (0x60 : U256)).toNat = 100 := by decide
  unfold tacLen tacOff
  rw [tac_data, Witness.arg3_data4 size_SEL_transferAndCall, e,
    Witness.arg4_data4 size_SEL_transferAndCall]

theorem tac_n : tacN (m_tac b t C amount) = 0 := by
  unfold tacN
  rw [tac_len] <;> rfl

theorem tac_nlt : tacN (m_tac b t C amount) < 2 ^ 64 := by
  rw [tac_n]
  decide

theorem tac_caller : (m_tac b t C amount).caller.toU256 = Witness.CALLER1W :=
  Witness.caller1_toU256

theorem tac_target : (m_tac b t C amount).currentTarget = C := rfl

end Facts

/-! ## Words and addresses -/

theorem g1 : bitwiseAnd (0x1000 : U256)
    (1461501637330902918203684832716283019655932542975 : U256) = 0x1000 := by decide

theorem g2 : bitwiseAnd Witness.CALLER1W
    (1461501637330902918203684832716283019655932542975 : U256) = Witness.CALLER1W := by decide

theorem g3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    Witness.CALLER1W = Witness.CALLER1W := by decide

theorem g4 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256)
    (0x1000 : U256) = 0x1000 := by decide

/-- The address of the word 0x1000 is no precompile, at any fork. -/
theorem notPrecompile_rcpt :
    Precompiles.isPrecompile fork (toAddressMasked (0x1000 : U256)).toU256.toNat = false := by
  rw [EthLib.Base.toNat_toU256_toAddressMasked]
  have h : (0x1000 : U256).toNat % 2 ^ 160 = 4096 := by decide
  rw [h]
  rfl

/-- `LINK_ADDRESS` is not the address of the word 0x1000. -/
theorem link_ne_rcpt : LINK_ADDRESS ≠ toAddressMasked (0x1000 : U256) := by
  intro h
  have h2 : LINK_ADDRESS.toU256.toNat = (toAddressMasked (0x1000 : U256)).toU256.toNat :=
    congrArg (fun a : Address => a.toU256.toNat) h
  rw [EthLib.Base.toNat_toU256_toAddressMasked, link_address_word] at h2
  exact absurd h2 (by decide)

/-- The balance slots of the caller and of the recipient differ. -/
theorem key_ne : mapSlot Witness.CALLER1W 1 ≠ mapSlot (0x1000 : U256) 1 := by decide +kernel

/-- The address of the recipient on the stack at the CALL. -/
theorem tac_rcpt (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (amount : U256) :
    toAddressMasked (tacToW (m_tac b t C amount)) = toAddressMasked (0x1000 : U256) := by
  show toAddressMasked (bitwiseAnd (tacTo (m_tac b t C amount))
    (1461501637330902918203684832716283019655932542975 : U256)) = _
  rw [toAddressMasked_mask', tac_to]

/-! ## The conditions of the paths, on the call -/

section Conds

variable (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)

/-- The recipient is not the zero address. -/
theorem tac_set (amount : U256) : TacToSet (m_tac b t C amount) := by
  simp only [TacToSet, tac_to] <;> decide +kernel

/-- The recipient is not the token. -/
theorem tac_other (amount : U256)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256)) :
    TacToOther (m_tac b t C amount) := by
  simp only [TacToOther, tac_to, tac_target, hC] <;> decide +kernel

/-- The caller has 5 tokens: the amount 1 is covered. -/
theorem tac_funded {S : State.TransactionState}
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5) :
    TacFunded (m_tac b t C 1) S := by
  simp only [TacFunded, tac_value, tac_caller, tac_target, g2, hbal] <;> decide +kernel

/-- The recipient has 0 tokens: its new balance does not wrap. -/
theorem tac_fits {S : State.TransactionState} (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0) :
    TacFits (m_tac b t C 1) S := by
  simp (disch := supply_side) only [TacFits, tac_value, tac_to, tac_caller, tac_target,
    g1, g2, g3, g4, storageAt_readSlot, Readable.storageAt_writeSlot_ite, hbal, hto]
    <;> decide +kernel

/-- The caller has 0 tokens: the amount 1 is above the balance. -/
theorem tac_low {S : State.TransactionState}
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 0) :
    TacLow (m_tac b t C 1) S := by
  simp only [TacLow, tac_value, tac_caller, tac_target, g2, hbal] <;> decide +kernel

/-- The two balances after the token move, in the state at the CALL. -/
theorem tac_call_balances {S : State.TransactionState} (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0) :
    storageAt (tacCallSt (m_tac b t C 1) S) C (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt (tacCallSt (m_tac b t C 1) S) C (mapSlot (0x1000 : U256) 1) = 1 := by
  constructor
  · simp (disch := supply_side) only [tacCallSt, tac_callSt, storageAt_rar, tac_value, tac_to,
      tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto]
      <;> decide +kernel
  · simp (disch := supply_side) only [tacCallSt, tac_callSt, storageAt_rar, tac_value, tac_to,
      tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto]
      <;> decide +kernel

/-- The two balances after the token move, in the end state with no code at the recipient. -/
theorem tac_done_balances {S : State.TransactionState} (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0) :
    storageAt (tacDoneSt (m_tac b t C 1) S) C (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt (tacDoneSt (m_tac b t C 1) S) C (mapSlot (0x1000 : U256) 1) = 1 := by
  constructor
  · simp (disch := supply_side) only [tacDoneSt, tac_noneSt, storageAt_rar, tac_value, tac_to,
      tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto]
      <;> decide +kernel
  · simp (disch := supply_side) only [tacDoneSt, tac_noneSt, storageAt_rar, tac_value, tac_to,
      tac_caller, tac_target, g1, g2, g3, g4, storageAt_readSlot,
      Readable.storageAt_writeSlot_ite, hbal, hto]
      <;> decide +kernel

end Conds

/-! ## The run to the CALL, on the call -/

/-- `tac_call_run` on the concrete call, under `processRunner`, with `tacCallGas + 13000` gas as
the gas of the frame and as the bound: the recipient has code `c` in the state `S`. -/
theorem tac_wit_call (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    {c : ByteArray}
    (hcode : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash = .ok c)
    (h5 : TacHasCode c) (hdel : .pectra ≤ fork → delegatedAddress c = none) :
    ∃ (caller : Evm fork Nat) (msg : Message fork),
      msg.gas < tacCallGas fork (m_tac b t C 1) S ss + 13000 ∧
      caller.state = ((tacCallSt (m_tac b t C 1) S).recordAccountRead
        (toAddressMasked (0x1000 : U256))).recordAccountRead (m_tac b t C 1).currentTarget ∧
      msg.target = some (toAddressMasked (0x1000 : U256)) ∧
      msg.codeAddress = some (toAddressMasked (0x1000 : U256)) ∧
      msg.code = c ∧ msg.value = 0 ∧
      ∀ (lt : msg.gas < tacCallGas fork (m_tac b t C 1) S ss + 13000)
        (child : { child : Evm fork Nat // GasMeter.gasHeld child.gas ≤ msg.gas }),
        processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000) caller msg lt =
          .ok child →
        ∃ (after : Evm fork Nat)
          (w : GasMeter.gasHeld after.gas ≤ tacCallGas fork (m_tac b t C 1) S ss + 13000),
          At CODE (m_tac b t C 1) 3089
            ((if child.1.error.isNone then 1 else 0) ::
              tacRest (m_tac b t C 1) (BitVec.ofNat 256 (selector (m_tac b t C 1).data)))
            (tacMem (m_tac b t C 1)) after.gas (incorporateChild fork caller child.1).state
            (incorporateChild fork caller child.1).substate after ∧
          147 ≤ after.gas ∧
          Evm.runFrame (step fork) (step_decreases fork)
              (tacCallGas fork (m_tac b t C 1) S ss + 13000)
              (processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000))
              (sFrame (m_tac b t C 1) S ss (tacCallGas fork (m_tac b t C 1) S ss + 13000))
              (Nat.le_refl _) =
            Evm.runFrame (step fork) (step_decreases fork)
              (tacCallGas fork (m_tac b t C 1) S ss + 13000)
              (processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000)) after w := by
  have hcodeT : TacCode (m_tac b t C 1) S c := by
    unfold TacCode
    rw [tac_to]
    exact hcode
  obtain ⟨cl, msg, hlt, hs, mt, mca, mc, mv, hafter⟩ :=
    tac_call_run hfork hglam (message := m_tac b t C 1) (state := S) (substate := ss)
      (by rw [tac_size]; decide) (by rw [tac_size]; decide) (tac_sel b t C 1) rfl rfl hacc
      (tac_nlt b t C 1) hcodeT (tac_set b t C 1) (tac_other b t C 1 hC) (tac_funded b t C hbal)
      (tac_fits b t C hacc hbal hto) h5 hdel (show 0 + 1 ≤ STACK_DEPTH_LIMIT by decide)
      (processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000)) (Nat.le_refl _)
      (evm := sFrame (m_tac b t C 1) S ss (tacCallGas fork (m_tac b t C 1) S ss + 13000))
      (at_sFrame _ rfl _ _ _) (Nat.le_refl _)
  rw [tac_rcpt] at hs mt mca
  exact ⟨cl, msg, hlt, hs, mt, mca, mc, mv, hafter⟩

/-! ## W1: the recipient is a contract that stops -/

/-- W1. From Paris and before Glamsterdam, a full run of `transferAndCall(0x1000, 1, "")` under
EthLib's real runner. In any state `S` where the contract `C` has an account, the caller has 5
tokens, the recipient has 0, and the recipient (the address of the word 0x1000) has the code of
one byte STOP: the interpreter loop under `processRunner`, from pc 0, ends with no error and the
output `true`; the caller has 4 tokens and the recipient has 1. -/
theorem transferAndCall_stop_runs (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hcode : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash =
      .ok Payee.STOP_CODE) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t C 1) 0 [] .empty gas S ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state C (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt s.state C (mapSlot (0x1000 : U256) 1) = 1 := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨cl, msg, hlt, hcls, mt, mca, mc, mv, hafter⟩ :=
    tac_wit_call hfork hglam b t C S ss hC hacc hbal hto hcode
      (by unfold TacHasCode; decide +kernel) (fun _ => Payee.delegatedAddress_stop)
  obtain ⟨child, hch, hce, hcst⟩ :=
    stop_message_runs hparis hlt mc mt (noPre_of mca notPrecompile_rcpt) mv
  obtain ⟨after, w, hat, hga, hrun12⟩ := hafter hlt child hch
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 1 := by
    rw [hce] <;> rfl
  rw [hflag] at hat
  obtain ⟨s, hrf, hH⟩ :=
    (tac_after_ok (fork := fork) (message := m_tac b t C 1)
      (sel := BitVec.ofNat 256 (selector (m_tac b t C 1).data)) (flag := 1)
      (tac_nlt b t C 1) (by decide) hga).runFrame
      (runChild := processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000)) hat w
  obtain ⟨-, he, ho, -, hs, -⟩ := hH
  obtain ⟨hb1, hb2⟩ := tac_call_balances b t C hacc hbal hto
  have hst : s.state = ((tacCallSt (m_tac b t C 1) S).recordAccountRead
      (toAddressMasked (0x1000 : U256))).recordAccountRead (m_tac b t C 1).currentTarget := by
    rw [hs, state_incorporate_ok hce, hcst, hcls]
  refine ⟨tacCallGas fork (m_tac b t C 1) S ss + 13000,
    sFrame (m_tac b t C 1) S ss (tacCallGas fork (m_tac b t C 1) S ss + 13000), s,
    at_sFrame _ rfl _ _ _, ⟨Nat.le_refl _, hrun12.trans hrf⟩, by simpa using he, ho, ?_, ?_⟩
  · rw [hst, storageAt_rar, storageAt_rar]
    exact hb1
  · rw [hst, storageAt_rar, storageAt_rar]
    exact hb2

/-- The hash of the code STOP is not the hash of the empty code. -/
theorem stop_hash_ne : hashOf Payee.STOP_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

/-- The state of W1: the contract at `LINK_ADDRESS` where the caller has 5 tokens, and the
recipient (the address of the word 0x1000) with the code of one byte STOP. -/
abbrev stopState : State.TransactionState :=
  codeState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)] (toAddressMasked (0x1000 : U256))
    Payee.STOP_CODE

/-- The caller has 5 tokens in a `codeState` over the one balance. -/
theorem bal_codeState (a : Address) (code : ByteArray) :
    storageAt (codeState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)] a code) LINK_ADDRESS
      (mapSlot Witness.CALLER1W 1) = 5 := by
  rw [storageAt_codeState, storageAt_sState_cons, if_pos rfl]

/-- The recipient has 0 tokens in a `codeState` over the one balance. -/
theorem to_codeState (a : Address) (code : ByteArray) :
    storageAt (codeState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)] a code) LINK_ADDRESS
      (mapSlot (0x1000 : U256) 1) = 0 := by
  rw [storageAt_codeState, storageAt_sState_cons, if_neg key_ne, storageAt_sState_nil]

/-- W1, closed. A full run with no hypothesis left but the fork range: the token at
`LINK_ADDRESS`, the caller `Witness.CALLER1` with 5 tokens, the recipient at the address of the
word 0x1000 with the code of one byte STOP. The call `transferAndCall(0x1000, 1, "")`, run by the
interpreter loop under EthLib's `processRunner` from pc 0, ends with no error and the output
`true`; the caller ends with 4 tokens and the recipient with 1. -/
theorem transferAndCall_stop_runs_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t LINK_ADDRESS 1) 0 [] .empty gas stopState ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state LINK_ADDRESS (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt s.state LINK_ADDRESS (mapSlot (0x1000 : U256) 1) = 1 :=
  transferAndCall_stop_runs hparis hglam b t LINK_ADDRESS stopState ss link_address_word
    (hasAccount_codeState _ _ link_ne_rcpt) (bal_codeState _ _) (to_codeState _ _)
    (getCode_codeState _ _ _ stop_hash_ne)

/-! ## W2: the recipient has no code -/

/-- W2. From Berlin, a full run of `transferAndCall(0x1000, 1, "")` to a recipient with no code,
for every runner and every bound. In any state `S` where the contract `C` has an account, the
caller has 5 tokens, the recipient has 0 and has no code: the run from pc 0 ends with no error
and the output `true`; the caller has 4 tokens and the recipient has 1. -/
theorem transferAndCall_nocode_runs (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hcode : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash =
      .ok ByteArray.empty) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t C 1) 0 [] .empty gas S ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state C (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt s.state C (mapSlot (0x1000 : U256) 1) = 1 := by
  have hcodeT : TacCode (m_tac b t C 1) S ByteArray.empty := by
    unfold TacCode
    rw [tac_to]
    exact hcode
  obtain ⟨s, hr, hrun, hH⟩ := Triple.seq
    (transferAndCall_p1 (fork := fork) (message := m_tac b t C 1) (state := S) (substate := ss)
      hfork (by rw [tac_size]; decide) (by rw [tac_size]; decide) (tac_sel b t C 1)
      (show isZero (0 : U256) ≠ 0 by decide)
      (gas := tacDoneGas fork (m_tac b t C 1) S ss + 2508) (by omega))
    (tac_done (fork := fork) (message := m_tac b t C 1)
      (sel := BitVec.ofNat 256 (selector (m_tac b t C 1).data)) (state := S) (substate := ss)
      hfork rfl hacc (tac_nlt b t C 1) hcodeT (tac_set b t C 1) (tac_other b t C 1 hC)
      (tac_funded b t C hbal) (tac_fits b t C hacc hbal hto)
      (by unfold TacNoCode; decide +kernel)
      (gas := tacDoneGas fork (m_tac b t C 1) S ss + 2508 - 207) (by omega))
    (sFrame (m_tac b t C 1) S ss _) (at_sFrame _ rfl _ _ _)
  obtain ⟨-, he, ho, -, hs, -⟩ := hH
  obtain ⟨hb1, hb2⟩ := tac_done_balances b t C hacc hbal hto
  refine ⟨_, _, s, at_sFrame _ rfl _ _ _,
    fun rc within => Witness.endsL_of_reaches hr hrun rc within, by simpa using he, ho, ?_, ?_⟩
  · rw [hs]
    exact hb1
  · rw [hs]
    exact hb2

/-- In `sState C kvs` an address other than `C` has no code. -/
theorem getCode_sState_other {C a : Address} (kvs : List (U256 × U256)) (hne : C ≠ a) :
    (sState C kvs).getCode ((sState C kvs).getAccount a).codeHash = .ok ByteArray.empty := by
  have hO : (sState C kvs).getAccount a = State.EMPTY_ACCOUNT := by
    unfold State.TransactionState.getAccount
    have hnone : (sState C kvs).getAccountOptional a = none := by
      simp [sState, State.TransactionState.ofBlock, State.TransactionState.getAccountOptional,
        State.State.getAccountOptional, Std.ExtTreeMap.getElem?_insert, hne]
    rw [hnone] <;> rfl
  rw [hO]
  simp [State.TransactionState.getCode, State.EMPTY_ACCOUNT]

/-- W2, closed. No hypothesis left but the fork (from Berlin): the token at `LINK_ADDRESS`, the
caller with 5 tokens, the recipient at the address of the word 0x1000 with no account. For every
runner the call ends with no error and the output `true`, with 4 and 1 tokens. -/
theorem transferAndCall_nocode_runs_closed (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t LINK_ADDRESS 1) 0 [] .empty gas
        (sState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)]) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧
      s.error = none ∧ s.output = wordBytes (1 : U256) ∧
      storageAt s.state LINK_ADDRESS (mapSlot Witness.CALLER1W 1) = 4 ∧
      storageAt s.state LINK_ADDRESS (mapSlot (0x1000 : U256) 1) = 1 :=
  transferAndCall_nocode_runs hfork b t LINK_ADDRESS
    (sState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)]) ss link_address_word
    (hasAccount_sState _ _)
    (by rw [storageAt_sState_cons, if_pos rfl])
    (by rw [storageAt_sState_cons, if_neg key_ne, storageAt_sState_nil])
    (getCode_sState_other _ link_ne_rcpt)

/-! ## W3a: the amount is above the balance -/

/-- W3a. From Berlin, a full run of `transferAndCall(0x1000, 1, "")` from a caller with 0 tokens,
for every runner and every bound: the run from pc 0 ends with the error of the invalid opcode
0xfe (the `assert` of SafeMath, compiled in 2017). -/
theorem transferAndCall_low_runs (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 0) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t C 1) 0 [] .empty gas S ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧
      s.error = some (.invalidOpcode 0xfe) := by
  obtain ⟨s, hr, hrun, hF⟩ := Triple.seq
    (transferAndCall_p1 (fork := fork) (message := m_tac b t C 1) (state := S) (substate := ss)
      hfork (by rw [tac_size]; decide) (by rw [tac_size]; decide) (tac_sel b t C 1)
      (show isZero (0 : U256) ≠ 0 by decide)
      (gas := tac_lowCost (m_tac b t C 1) ss (tacN (m_tac b t C 1)) + 207) (by omega))
    (tac_invalid_low (fork := fork) (message := m_tac b t C 1)
      (sel := BitVec.ofNat 256 (selector (m_tac b t C 1).data)) (state := S) (substate := ss)
      hfork (tac_nlt b t C 1) (tac_set b t C 1) (tac_other b t C 1 hC) (tac_low b t C hbal)
      (gas := tac_lowCost (m_tac b t C 1) ss (tacN (m_tac b t C 1)) + 207 - 207) (by omega))
    (sFrame (m_tac b t C 1) S ss _) (at_sFrame _ rfl _ _ _)
  obtain ⟨-, he, -⟩ := hF
  exact ⟨_, _, s, at_sFrame _ rfl _ _ _,
    fun rc within => Witness.endsL_of_reaches hr hrun rc within, he⟩

/-- W3a, closed. No hypothesis left but the fork (from Berlin): the token at `LINK_ADDRESS` with
no balance at all. For every runner the call ends with the error of the invalid opcode. -/
theorem transferAndCall_low_runs_closed (hfork : .berlin ≤ fork)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t LINK_ADDRESS 1) 0 [] .empty gas (sState LINK_ADDRESS []) ss evm ∧
      (∀ {bound : Nat} (runChild : MessageRunner fork Nat bound),
        GasMeter.gasHeld evm.gas ≤ bound → EndsL runChild evm s) ∧
      s.error = some (.invalidOpcode 0xfe) :=
  transferAndCall_low_runs hfork b t LINK_ADDRESS (sState LINK_ADDRESS []) ss link_address_word
    (storageAt_sState_nil _ _)

/-! ## W3b: the message of the recipient fails -/

/-- W3b. From Paris and before Glamsterdam, a full run of `transferAndCall(0x1000, 1, "")` under
EthLib's real runner, to a recipient whose code is the one byte INVALID (0xfe): the message of
the CALL fails, the CALL gives the flag 0, and the whole call ends with the error REVERT and no
output. (The frame stops with its state as it is; the message layer rolls a failed message
back.) -/
theorem transferAndCall_reverts (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (C : Address)
    (S : State.TransactionState) (ss : Substate)
    (hC : C.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256))
    (hacc : hasAccount S C)
    (hbal : storageAt S C (mapSlot Witness.CALLER1W 1) = 5)
    (hto : storageAt S C (mapSlot (0x1000 : U256) 1) = 0)
    (hcode : S.getCode (S.getAccount (toAddressMasked (0x1000 : U256))).codeHash =
      .ok INVALID_CODE) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t C 1) 0 [] .empty gas S ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = some .revert ∧ s.output = ByteArray.empty := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨cl, msg, hlt, hcls, mt, mca, mc, mv, hafter⟩ :=
    tac_wit_call hfork hglam b t C S ss hC hacc hbal hto hcode
      (by unfold TacHasCode; decide +kernel) (fun _ => delegatedAddress_invalid)
  obtain ⟨child, hch, hce⟩ :=
    invalid_message_runs hparis hlt mc mt (noPre_of mca notPrecompile_rcpt) mv
  obtain ⟨after, w, hat, hga, hrun12⟩ := hafter hlt child hch
  have hflag : (if child.1.error.isNone then (1 : U256) else 0) = 0 := by
    rw [hce] <;> rfl
  rw [hflag] at hat
  obtain ⟨s, hrf, hH⟩ :=
    (tac_after_fail_any (fork := fork) (message := m_tac b t C 1)
      (sel := BitVec.ofNat 256 (selector (m_tac b t C 1).data)) hfork
      (show af_failCost ≤ after.gas by unfold af_failCost; omega)).runFrame
      (runChild := processRunner fork (tacCallGas fork (m_tac b t C 1) S ss + 13000)) hat w
  obtain ⟨-, he, ho, -⟩ := hH
  exact ⟨tacCallGas fork (m_tac b t C 1) S ss + 13000,
    sFrame (m_tac b t C 1) S ss (tacCallGas fork (m_tac b t C 1) S ss + 13000), s,
    at_sFrame _ rfl _ _ _, ⟨Nat.le_refl _, hrun12.trans hrf⟩, by simpa using he, ho⟩

/-- The hash of the code INVALID is not the hash of the empty code. -/
theorem invalid_hash_ne : hashOf INVALID_CODE ≠ EMPTY_CODE_HASH := by decide +kernel

/-- The state of W3b: as `stopState`, with the code of one byte INVALID at the recipient. -/
abbrev invalidState : State.TransactionState :=
  codeState LINK_ADDRESS [(mapSlot Witness.CALLER1W 1, 5)] (toAddressMasked (0x1000 : U256))
    INVALID_CODE

/-- W3b, closed. No hypothesis left but the fork range: the token at `LINK_ADDRESS`, the caller
with 5 tokens, the recipient with the code of one byte INVALID. Under EthLib's `processRunner`
the call ends with the error REVERT. -/
theorem transferAndCall_reverts_closed (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (b : BlockEnvironment fork) (t : TransactionEnvironment fork) (ss : Substate) :
    ∃ (gas : Nat) (evm s : Evm fork Nat),
      At CODE (m_tac b t LINK_ADDRESS 1) 0 [] .empty gas invalidState ss evm ∧
      (∃ within : GasMeter.gasHeld evm.gas ≤ gas,
        Evm.runFrame (step fork) (step_decreases fork) gas (processRunner fork gas) evm within =
          .ok s) ∧
      s.error = some .revert ∧ s.output = ByteArray.empty :=
  transferAndCall_reverts hparis hglam b t LINK_ADDRESS invalidState ss link_address_word
    (hasAccount_codeState _ _ link_ne_rcpt) (bal_codeState _ _) (to_codeState _ _)
    (getCode_codeState _ _ _ invalid_hash_ne)

/-! ## W4: the assumption on the message of the CALL, for a STOP recipient

`CalleeKeeps runChild message state` (Any.lean) is about EVERY message `msg` with the recipient
as its current target and the call data of the CALL, run from a state that reads as the state at
the CALL. It does not say which code `msg` runs. So it does not follow from "the state gives the
code STOP for the recipient": a message with these two fields and any other code is in its
scope, and for such a message one needs the induction of `Reenter` over all messages
(`calleeKeeps_processRunner_local` with a clean run, or the global
`calleeKeeps_processRunner_sepAll_noCollision`).

What the CALL of `transferAndCall` sends is one message whose code is the code that the state
gives for the recipient (`SentIn`, from `ok_tac_whole`). `CalleeKeepsOf` is `CalleeKeeps` for
that message: it names the code, the target, the code address and the value. For the code STOP it
holds under `processRunner` with no hypothesis on keccak (`calleeKeeps_stop`), and it is enough
for the sum invariant (`supply_tac_530_of`), where the only hypothesis on keccak left is the one
of the token move itself (`Sep (callKeys message)`, as for `transfer`). -/

section Keeps

variable {message : Message fork} {sel : U256} {state : State.TransactionState}
  {substate : Substate} {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- The assumption on the one message that the CALL of `transferAndCall` sends, with its code
named: a message to the recipient with the code `c`, no value, run by `runChild` from the state
at the CALL (with its two reads recorded) to a frame with no error, keeps the invariant. -/
def CalleeKeepsOf (runChild : MessageRunner fork Nat bound) (message : Message fork)
    (state : State.TransactionState) (c : ByteArray) : Prop :=
  ∀ (caller : Evm fork Nat) (msg : Message fork) (child : Evm fork Nat),
    Ran runChild caller msg child →
    msg.code = c →
    msg.target = some (toAddressMasked (tacToW message)) →
    msg.codeAddress = some (toAddressMasked (tacToW message)) →
    msg.value = 0 →
    caller.state = ((tacCallSt message state).recordAccountRead
      (toAddressMasked (tacToW message))).recordAccountRead message.currentTarget →
    child.error = none →
    Inv message.currentTarget caller.state → Inv message.currentTarget child.state

/-- From Paris, a message with no value whose code is the one byte STOP, to an address that is no
precompile, run by `processRunner`: it ends with no error, in the state of its caller. -/
theorem stop_child_keeps (hparis : .paris ≤ fork) {caller child : Evm fork Nat}
    {msg : Message fork} {a : Address}
    (hran : Ran (processRunner fork bound) caller msg child)
    (hcode : msg.code = Payee.STOP_CODE) (ht : msg.target = some a)
    (hca : msg.codeAddress = some a)
    (hnp : Precompiles.isPrecompile fork a.toU256.toNat = false) (hv : msg.value = 0) :
    child.error = none ∧ child.state = caller.state :=
  have h := Payee.stop_message hparis hran hcode ht (noPre_of hca hnp)
  ⟨h.1, h.2.2 (fun x => x.2 hv)⟩

/-- W4. From Paris, the assumption on the message of the CALL holds for EthLib's real runner and
a STOP recipient that is no precompile, for every bound, with no hypothesis on keccak: the
message leaves the state of its caller as it is. -/
theorem calleeKeeps_stop (hparis : .paris ≤ fork)
    (hnp : Precompiles.isPrecompile fork
      (toAddressMasked (tacToW message)).toU256.toNat = false) :
    CalleeKeepsOf (processRunner fork (Meter := Nat) bound) message state Payee.STOP_CODE := by
  intro caller msg child hran hc ht hca hv hs herr hinv
  rw [(stop_child_keeps hparis hran hc ht hca hnp hv).2]
  exact hinv

/-- From 530: a successful `transferAndCall` keeps the invariant, under the assumption on the one
message of its CALL with its code named. `hc`: the state gives the code `c` for the recipient.
`hsep`: the hypothesis on keccak for the keys of this call (the token move). -/
theorem supply_tac_530_of (hfork : .berlin ≤ fork) (hglam : fork < .glamsterdam)
    (hN : tacN message < 2 ^ 64) (hsep : Sep (callKeys message))
    {c : ByteArray} (hc : TacCode message state c)
    (hdel : .pectra ≤ fork → delegatedAddress c = none)
    (keeps : CalleeKeepsOf runChild message state c)
    (hinv : Inv message.currentTarget state)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state
      substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have hc0 : state.getCode (state.getAccount (toAddressMasked (tacTo message))).codeHash =
      .ok c := hc
  have same : ∀ c', TacCode message state c' → c' = c := by
    intro c' hc'
    have hc1 : state.getCode (state.getAccount (toAddressMasked (tacTo message))).codeHash =
        .ok c' := hc'
    exact Except.ok.inj (hc1.symm.trans hc0)
  obtain ⟨hstat, hacc, h1, h2, h3, h4, hrn, hout, c', hcode, hcase⟩ :=
    ok_tac_whole hfork hglam hN (fun c' hc' hp => by rw [same c' hc']; exact hdel hp)
      start hrun hok
  rcases hcase with ⟨h5, -, -, hst, -⟩ |
    ⟨h5, -, caller, msg, child, hran, herr, -, hsent, -, hst, -⟩
  · rw [hst]
    exact inv_tacDoneSt hsep hacc h3 h4 hinv
  · obtain ⟨s1, -, -, -, -, mt, mca, mc, -, mv, -⟩ := hsent
    rw [hst]
    refine keeps caller msg child hran (mc.trans (same c' hcode)) mt mca mv s1 herr ?_
    have hI := inv_tacCallSt hsep hacc h3 h4 hinv
    rw [s1]
    unfold Inv at hI ⊢
    rw [Supply.sumBal_recordAccountRead, Supply.sumBal_recordAccountRead]
    exact hI

/-- The sum invariant through `transferAndCall` to a STOP recipient, under EthLib's real runner,
from Paris and before Glamsterdam, with no assumption on the runner and no hypothesis on keccak
but the one of the token move (`hsep`). The gas is below `2 ^ 60`. -/
theorem supply_transferAndCall_stop (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x4000aea0)
    {gas : Nat} (hgas : gas < 2 ^ 60)
    (hsep : Sep (callKeys message))
    (hstop : TacCode message state Payee.STOP_CODE)
    (hnp : Precompiles.isPrecompile fork
      (toAddressMasked (tacToW message)).toU256.toNat = false)
    (hinv : Inv message.currentTarget state)
    {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL (processRunner fork (Meter := Nat) bound) evm s) (hok : s.error = none) :
    Inv message.currentTarget s.state := by
  have hfork : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨-, hcg, z, hz, hzr⟩ := ok_transferAndCall hfork hsize' hsel start hrun hok
  have hN := ok_tac_len hfork (show gas - 207 < 2 ^ 60 by omega) hz hzr hok
  exact supply_tac_530_of hfork hglam hN hsep hstop (fun _ => Payee.delegatedAddress_stop)
    (calleeKeeps_stop hparis hnp) hinv hz hzr hok

end Keeps

end LinkVerify.Sanity

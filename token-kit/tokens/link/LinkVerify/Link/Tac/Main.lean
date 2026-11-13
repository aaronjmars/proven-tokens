import LinkVerify.Link.Tac.Defs

/-!
# transferAndCall: the triples of the function

`transferAndCall(address to, uint256 value, bytes data)`, selector 0x4000aea0, from the frame at
530 that the dispatcher reaches (`transferAndCall_p1`). The memory is symbolic: the length of the
data is `tacN message`, any number below `2 ^ 64`.

Forward, for every gas from a bound on:

- `tac_revert_zero`, `tac_revert_self`: the recipient is zero, or the token: REVERT.
- `tac_invalid_low`, `tac_invalid_over`: the amount is above the balance, or the balance of the
  recipient would wrap: the invalid opcode.
- `tac_stuck_static`: a static frame, or a frame with no account: the first SSTORE fails.
- `tac_done`: the recipient has no code: both writes, both logs, RETURN of true.
- `tac_second_check`: the second test of the code (before the CALL) cannot fail.
- `tac_to_gas`: the recipient has code: the frame at the GAS opcode before the CALL.
- `tac_at_call`: the same, to the CALL itself (GAS reads the gas left, so this one is a plain
  triple at one gas).
- `tac_call_range`: the call data is inside the memory, and its size.
- `tac_after_ok`, `tac_after_fail`: after the CALL, from any state and substate: RETURN of true
  when the flag is not zero, REVERT when it is zero.
-/

set_option autoImplicit false
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

variable {fork : Fork} {message : Message fork}

/-- The stack under the seven arguments of the CALL (and under its flag after it). -/
def tacRest (message : Message fork) (sel : U256) : List U256 :=
  [BitVec.ofNat 256 (tacF message + tacW message + 132), (2764107062 : U256),
    bitwiseAnd (tacTo message) (1461501637330902918203684832716283019655932542975 : U256),
    tacTo message, (96 : U256), tacValue message, tacTo message, (2583 : U256), (0 : U256),
    (96 : U256), tacValue message, tacTo message, (1260 : U256), tacTo message, (0 : U256),
    (96 : U256), tacValue message, tacTo message, (361 : U256), sel]

/-- The seven arguments of the CALL on the stack, with `asked` the gas it asks for: the
recipient, no value, the call data from the free memory pointer, and no room for an answer. -/
def tacCallStack (message : Message fork) (sel asked : U256) : List U256 :=
  asked :: bitwiseAnd (tacTo message) (1461501637330902918203684832716283019655932542975 : U256)
    :: (0 : U256) :: tacFpw (tacLen message) :: BitVec.ofNat 256 (tacW message + 132)
    :: tacFpw (tacLen message) :: (0 : U256) :: tacRest message sel

/-- The gas the CALL asks for, from the gas at the entry of the function: all the gas left at the
GAS opcode, less 710. -/
def tacAsked (fork : Fork) (message : Message fork) (state : State.TransactionState)
    (substate : Substate) (gas : Nat) : U256 :=
  sub (BitVec.ofNat 256 (gas - tacCallGas fork message state substate - 2)) (710 : U256)

variable {sel : U256} {state : State.TransactionState} {substate : Substate}

/-! ## The failing paths -/

/-- B1. The recipient is the zero address: REVERT with no data, nothing written. -/
theorem tac_revert_zero (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64)
    (h : TacToZero message) {gas : Nat} (hg : tac_zeroCost (tacN message) ≤ gas) :
    Logic.SpecG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (Halted true ByteArray.empty (gas - tac_zeroCost (tacN message)) state substate) :=
  tac_zero hfork hN h
    (isZero_eq_zero_iff.mpr (isZero_ne_zero_iff.mpr (isZero_eq_zero_iff.mpr h))) hg

/-- B2. The recipient is the token itself: REVERT with no data, nothing written. -/
theorem tac_revert_self (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64)
    (h1 : TacToSet message) (h2 : TacToSelf message) {gas : Nat}
    (hg : tac_selfCost (tacN message) ≤ gas) :
    Logic.SpecG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (Halted true ByteArray.empty (gas - tac_selfCost (tacN message)) state substate) :=
  tac_self hfork hN h1 h2 hg

/-- B3. The amount is above the balance of the caller: the invalid opcode (SafeMath of 2017). -/
theorem tac_invalid_low (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacLow message state) {gas : Nat}
    (hg : tac_lowCost message substate (tacN message) ≤ gas) :
    Logic.SpecG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (Faulted (.invalidOpcode 0xfe) (tac_lowSt message state) (tac_lowSs message substate)) :=
  tac_low hfork hN h1 h2 h3 hg

/-- A static frame, or a frame whose account the state does not have: the first SSTORE fails. -/
theorem tac_stuck_static (hfork : .berlin ≤ fork) (hN : tacN message < 2 ^ 64)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget) {gas : Nat}
    (hg : tac_stuckCost message substate (tacN message) ≤ gas) :
    Logic.HoareG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      Logic.Stuck :=
  tac_stuck hfork hN h1 h2 h3 (hbad.imp id fun h h' => h (hasAccount_readSlot_iff.mp h')) hg

/-- B4. The new balance of the recipient would wrap: the invalid opcode. -/
theorem tac_invalid_over (hfork : .berlin ≤ fork) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hN : tacN message < 2 ^ 64)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (h4 : TacOver message state) {gas : Nat}
    (hg : tac_overCost fork message state substate (tacN message) + 2300 < gas) :
    Logic.SpecG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (Faulted (.invalidOpcode 0xfe) (tac_overSt message state)
        (tac_overSs fork message state substate)) :=
  tac_over hfork hstatic hacc hN h1 h2 h3 h4 hg

/-! ## The recipient has no code -/

/-- B5. The recipient has no code: the two writes of the transfer, both logs, the read of the
account of the recipient, and RETURN of true. -/
theorem tac_done (hfork : .berlin ≤ fork) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hN : tacN message < 2 ^ 64)
    {c : ByteArray} (hcode : TacCode message state c)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (h4 : TacFits message state) (h5 : TacNoCode c) {gas : Nat}
    (hg : tacDoneGas fork message state substate + 2300 < gas) :
    Logic.SpecG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (Halted false (wordBytes (1 : U256)) (gas - tacDoneGas fork message state substate)
        (tacDoneSt message state) (tacDoneSs fork message state substate)) :=
  tac_none hfork hstatic hacc hN hcode h1 h2 h3 h4 h5 hg

/-! ## The recipient has code -/

/-- B6. The second test of the code, just before the CALL, cannot fail once the first test saw
code: the state there gives the same code, and the word it tests is not zero. -/
theorem tac_second_check {c : ByteArray} (hcode : TacCode message state c) (h5 : TacHasCode c) :
    (tacDoneSt message state).getCode ((tacDoneSt message state).getAccount (toAddressMasked
      (bitwiseAnd (tacTo message)
        (1461501637330902918203684832716283019655932542975 : U256)))).codeHash = .ok c ∧
    isZero (isZero (BitVec.ofNat 256 c.size)) ≠ 0 := by
  refine ⟨?_, code_twice h5⟩
  simpa only [tacDoneSt, tac_noneSt, TacCode, getCode_writeSlot, getAccount_writeSlot,
    getAccount_readSlot, getCode_readSlot, getAccount_rar, getCode_rar, toAddressMasked_mask']
    using hcode

/-- B7, to the GAS opcode. The recipient has code: the two writes, both logs, both reads of the
account, and the seven arguments of the CALL on the stack but the gas. -/
theorem tac_to_gas (hfork : .berlin ≤ fork) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hN : tacN message < 2 ^ 64)
    {c : ByteArray} (hcode : TacCode message state c)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (h4 : TacFits message state) (h5 : TacHasCode c) {gas : Nat}
    (hg : tacCallGas fork message state substate + 2300 < gas) :
    Logic.HoareG fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (At CODE message 3086 (tacCallStack message sel (710 : U256)) (tacMem message)
        (gas - tacCallGas fork message state substate) (tacCallSt message state)
        (tacCallSs fork message state substate)) :=
  tac_call hfork hstatic hacc hN hcode h1 h2 h3 h4 h5 hg

/-- SUB at 3087, for every gas from 3 on. -/
theorem tac_sub {a b : U256} {rest : List U256} {mem : ByteArray} {st : State.TransactionState}
    {ss : Substate} {g : Nat} (hg : 3 ≤ g) :
    Logic.HoareG fork (At CODE message 3087 (a :: b :: rest) mem g st ss)
      (At CODE message 3088 (sub a b :: rest) mem (g - 3) st ss) := by
  step binR 0x03 instruction_sub
  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)

/-- B7. The recipient has code: the frame at the CALL, with the gas it asks for
(`tacAsked`). GAS reads the gas left, so this triple is at one gas, not for every gas above. -/
theorem tac_at_call (hfork : .berlin ≤ fork) (hstatic : message.isStatic = false)
    (hacc : hasAccount state message.currentTarget) (hN : tacN message < 2 ^ 64)
    {c : ByteArray} (hcode : TacCode message state c)
    (h1 : TacToSet message) (h2 : TacToOther message) (h3 : TacFunded message state)
    (h4 : TacFits message state) (h5 : TacHasCode c) {gas : Nat}
    (hg : tacCallGas fork message state substate + 2300 < gas) :
    Logic.Hoare fork
      (At CODE message 530 [sel] (memW [(0 : U256), (0 : U256), (96 : U256)]) gas state substate)
      (At CODE message 3088
        (tacCallStack message sel (tacAsked fork message state substate gas)) (tacMem message)
        (gas - (tacCallGas fork message state substate + 5)) (tacCallSt message state)
        (tacCallSs fork message state substate)) := by
  refine Triple.seq (tac_to_gas hfork hstatic hacc hN hcode h1 h2 h3 h4 h5 hg).toHoare ?_
  refine Triple.seq (At.gas_rule (by code_fact) (by code_fact) (by omega)
    (by simp [tacCallStack, tacRest, STACK_LIMIT])) ?_
  have e : gas - (tacCallGas fork message state substate + 5) =
      gas - tacCallGas fork message state substate - 2 - 3 := by omega
  rw [e]
  exact (tac_sub (by omega)).toHoare

/-- B7, the call data. The range of the call data is inside the memory at the CALL, it is
`tacCallData message`, and it has `tacW message + 132` bytes: the selector and four words, then
the data in whole words. -/
theorem tac_call_range (hN : tacN message < 2 ^ 64) :
    (tacFpw (tacLen message)).toNat + (BitVec.ofNat 256 (tacW message + 132)).toNat ≤
      (tacMem message).size ∧
    memoryReadBytes (tacMem message) (tacFpw (tacLen message)).toNat
      (BitVec.ofNat 256 (tacW message + 132)).toNat = tacCallData message ∧
    (tacCallData message).size = tacW message + 132 := by
  obtain ⟨hsz, -, -⟩ := tac_call_mem hN
  have hW : tacW message = (tacN message + 31) / 32 * 32 := rfl
  have hF : (tacFpw (tacLen message)).toNat = tacF message := tacFpw_toNat rfl hN
  have hS : (BitVec.ofNat 256 (tacW message + 132)).toNat = tacW message + 132 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hsz' : (tacMem message).size = tacF message + tacW message + 160 := hsz
  rw [hF, hS]
  exact ⟨by omega, rfl, size_memoryReadBytes (by omega)⟩

/-! ## After the CALL -/

/-- C. After the CALL, the flag is not zero: RETURN of true, from any state and substate. -/
theorem tac_after_ok (hN : tacN message < 2 ^ 64) {flag : U256} (hflag : flag ≠ 0)
    {st : State.TransactionState} {ss : Substate} {g : Nat} (hg : af_okCost ≤ g) :
    Logic.SpecG fork (At CODE message 3089 (flag :: tacRest message sel) (tacMem message) g st ss)
      (Halted false (wordBytes (1 : U256)) (g - af_okCost) st ss) := by
  obtain ⟨hsz, h64, -⟩ := tac_call_mem hN
  have hW : tacW message = (tacN message + 31) / 32 * 32 := rfl
  have hF : tacF message = tacW message + 128 := rfl
  exact af_ok (F := tacF message) (W := tacW message) (tacFpw_toNat rfl hN) (by omega) (by omega)
    (by omega) hsz (by omega) (by omega) h64
    (isZero_ne_zero_iff.mpr (isZero_eq_zero_iff.mpr hflag)) hg

/-- C. After the CALL, the flag is zero: REVERT with no data, from any state and substate. -/
theorem tac_after_fail (hfork : .berlin ≤ fork) {flag : U256} (hflag : flag = 0)
    {st : State.TransactionState} {ss : Substate} {g : Nat} (hg : af_failCost ≤ g) :
    Logic.SpecG fork (At CODE message 3089 (flag :: tacRest message sel) (tacMem message) g st ss)
      (Halted true ByteArray.empty (g - af_failCost) st ss) :=
  af_fail (F := tacF message) (W := tacW message) hfork
    (isZero_eq_zero_iff.mpr (isZero_ne_zero_iff.mpr hflag)) hg

end LinkVerify.Tac

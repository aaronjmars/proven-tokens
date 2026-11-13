import BnbVerify.Bnb.Invariant
import TokenKit.Evm.Readable2

/-!
# What each function of BNB does, in plain terms

Written by `scripts/bnb_readable.py` (statements by hand, the simp lists repeated by the script).
Lean checks every statement against `CODE`.

For each function `<fn>`, `<fn>_readable`: from Berlin, a fresh frame of `CODE` at pc 0 with the
selector of `<fn>`, any gas, any value: if a loop of steps from it ends with no error (`Ends`),
then the conditions of success held at the start (first group), and the end is as stated (second
group): the return data, the new words of the slots it writes, every other slot of the contract
unchanged, and the logs. The exact gas is in `Paths.ok_<fn>` (Bnb/Gen).

The write functions take `Sep (callKeys message)` (Bnb/Sep.lean, the hypothesis on keccak, not
proved): it says which of the slots of the call are the same slot. The read functions do not.

Quirks of this contract that the statements show:
- no function checks the size of the call data: a missing argument is read as zeros;
- `transfer` returns no data (`s.output = ByteArray.empty`), where ERC-20 says a bool;
- `approve` logs nothing (no Approval event) and fails for the amount 0;
- `transfer`, `transferFrom`, `burn`, `freeze`, `unfreeze` fail for the amount 0;
- `transfer` and `transferFrom` fail for the recipient 0 (burn is the only way to lower
  `totalSupply`); a transfer to oneself changes no balance;
- `burn` lowers `totalSupply`; `freeze` and `unfreeze` move an amount between `balanceOf` and
  `freezeOf` of the caller and keep `totalSupply`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace BnbVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Readable
open BnbVerify BnbVerify.Paths BnbVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}

/-- `balanceOf[a]` of the called contract in the state `S`. -/
abbrev balanceOf (m : Message fork) (S : State.TransactionState) (a : U256) : U256 :=
  storageAt S m.currentTarget (mapSlot a 5)

/-- `freezeOf[a]` of the called contract in the state `S`. -/
abbrev freezeOf (m : Message fork) (S : State.TransactionState) (a : U256) : U256 :=
  storageAt S m.currentTarget (mapSlot a 6)

/-- `allowance[o][sp]` of the called contract in the state `S`. -/
abbrev allowance (m : Message fork) (S : State.TransactionState) (o sp : U256) : U256 :=
  storageAt S m.currentTarget (mapSlot sp (mapSlot o 7))

/-- `totalSupply` of the called contract in the state `S`. -/
abbrev totalSupply (m : Message fork) (S : State.TransactionState) : U256 :=
  storageAt S m.currentTarget 3

/-- The caller, as a word of 160 bits. -/
abbrev sender (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) m.caller.toU256

/-- The first argument word, masked to an address. -/
abbrev addrArg1 (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 4 32)

/-- The second argument word, masked to an address. -/
abbrev addrArg2 (m : Message fork) : U256 := bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord m.data 36 32)

/-- The argument words (zeros past the end of the call data). -/
abbrev arg1 (m : Message fork) : U256 := loadWord m.data 4 32
abbrev arg2 (m : Message fork) : U256 := loadWord m.data 36 32
abbrev arg3 (m : Message fork) : U256 := loadWord m.data 68 32

/-- keccak256("Transfer(address,address,uint256)"). -/
abbrev TRANSFER : U256 := (100389287136786176327247604509743168900146139575972864366142685224231313322991 : U256)

/-- keccak256("Burn(address,uint256)"). -/
abbrev BURN : U256 := (92312388597506580910220011357950614650372135269746937547546302273167149333669 : U256)

/-- keccak256("Freeze(address,uint256)"). -/
abbrev FREEZE : U256 := (112841725955285758919317737494780279943705905063922702930574325072310765461984 : U256)

/-- keccak256("Unfreeze(address,uint256)"). -/
abbrev UNFREEZE : U256 := (20348589114328558577173385677555850749120279790551619352293498188431687354431 : U256)

/-- totalSupply(): no value; returns the word of slot 3; writes nothing and logs nothing. -/
theorem totalSupply_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x18160ddd)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (totalSupply message state)) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_totalSupply hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- decimals(): no value; returns the low byte of slot 2; writes nothing and logs nothing. -/
theorem decimals_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x313ce567)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (BitVec.ofNat 256 ((storageAt state message.currentTarget 2).toNat % 256))) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_decimals hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- owner(): no value; returns the low 160 bits of slot 4; writes nothing and logs nothing. -/
theorem owner_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x8da5cb5b)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (storageAt state message.currentTarget 4))) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_owner hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- balanceOf(a): no value; returns `balanceOf[a]` (`a` masked to 160 bits; zeros when the call data is short); writes nothing and logs nothing. -/
theorem balanceOf_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x70a08231)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (balanceOf message state (addrArg1 message))) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_balanceOf hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- freezeOf(a): no value; returns `freezeOf[a]`; writes nothing and logs nothing. -/
theorem freezeOf_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xcd4217c1)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (freezeOf message state (addrArg1 message))) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_freezeOf hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- allowance(o, sp): no value; returns `allowance[o][sp]`; writes nothing and logs nothing. -/
theorem allowance_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xdd62ed3e)
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0)) ∧
    ((s.output = wordBytes (allowance message state (addrArg1 message) (addrArg2 message))) ∧
      (∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hgas, hout, hg, hst, hsub⟩ :=
    ok_allowance hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1
  have v1 := Readable.value_of_cond hc1
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- approve(spender, value) from the caller. Success needs: no value, a frame that may write, `value > 0`. It sets `allowance[caller][spender]` to `value`, returns 1, changes no other slot and logs NOTHING (no Approval event). -/
theorem approve_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x095ea7b3)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      (0 < (arg2 message).toNat)) ∧
    ((s.output = wordBytes 1) ∧
      (allowance message s.state (sender message) (addrArg1 message) = arg2 message) ∧
      (∀ k, k ≠ mapSlot (addrArg1 message) (mapSlot (sender message) 7) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs)) := by
  obtain ⟨hc1, hc2, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_approve hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2
  have v1 := Readable.value_of_cond hc1
  have p2 := Readable.pos_of_cond hc2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- transfer(to, value) from the caller. Success needs: no value, a frame that may write, `to` not 0, `value > 0`, `value <= balanceOf[caller]`, no overflow of `balanceOf[to] + value`. It returns NO data, moves `value` (to oneself: no change), keeps `totalSupply` and every other slot, and logs Transfer(caller, to, value). -/
theorem transfer_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xa9059cbb)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      ((addrArg1 message) ≠ 0) ∧
      (0 < (arg2 message).toNat) ∧
      ((arg2 message).toNat ≤ (balanceOf message state (sender message)).toNat) ∧
      ((balanceOf message state (addrArg1 message)).toNat + (arg2 message).toNat < 2 ^ 256)) ∧
    ((s.output = ByteArray.empty) ∧
      ((addrArg1 message) ≠ (sender message) → (balanceOf message s.state (sender message)).toNat = (balanceOf message state (sender message)).toNat - (arg2 message).toNat ∧ (balanceOf message s.state (addrArg1 message)).toNat = (balanceOf message state (addrArg1 message)).toNat + (arg2 message).toNat) ∧
      ((addrArg1 message) = (sender message) → balanceOf message s.state (sender message) = balanceOf message state (sender message)) ∧
      (totalSupply message s.state = totalSupply message state) ∧
      (∀ k, k ≠ mapSlot (sender message) 5 → k ≠ mapSlot (addrArg1 message) 5 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER (sender message) (addrArg1 message) (wordBytes (arg2 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_transfer hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  have hd2 : (isZero (isZero (lessThan (add (storageAt (writeSlot (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256)) (sub (storageAt (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) (loadWord message.data 36 32))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) (loadWord message.data 36 32)) (storageAt (writeSlot (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256)) (sub (storageAt (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (5 : U256))) (loadWord message.data 36 32))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256)))))) = 0 := by dead_credit hc4 hc5
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  by_cases hd1 : (addrArg1 message) = (sender message)
  · simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE] at hd1
    try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4 hc5 hd2
    have v1 := Readable.value_of_cond hc1
    have n2 := Readable.ne_of_cond1 hc2
    have p3 := Readable.pos_of_cond hc3
    have l4 := Supply.le_of_cond_lt1 hc4
    have f4 := Supply.sub_fact_lt1 hc4
    have b5 := Readable.add_bound_lt hc5
    have f5 := Supply.add_fact_lt hc5
    have g2 := Supply.add_fact2 hd2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)
  · have hd1' : ¬((sender message) = (addrArg1 message)) := fun e => hd1 e.symm
    simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE] at hd1 hd1'
    try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4 hc5 hd2
    have v1 := Readable.value_of_cond hc1
    have n2 := Readable.ne_of_cond1 hc2
    have p3 := Readable.pos_of_cond hc3
    have l4 := Supply.le_of_cond_lt1 hc4
    have f4 := Supply.sub_fact_lt1 hc4
    have b5 := Readable.add_bound_lt hc5
    have f5 := Supply.add_fact_lt hc5
    have g2 := Supply.add_fact2 hd2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- transferFrom(from, to, value) by the caller. Success needs: no value, a frame that may write, `to` not 0, `value > 0`, `value <= balanceOf[from]`, no overflow of `balanceOf[to] + value`, `value <= allowance[from][caller]`. It returns 1, moves `value` (from = to: no change), lowers the allowance by `value`, keeps `totalSupply` and every other slot, and logs Transfer(from, to, value). -/
theorem transferFrom_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x23b872dd)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      ((addrArg2 message) ≠ 0) ∧
      (0 < (arg3 message).toNat) ∧
      ((arg3 message).toNat ≤ (balanceOf message state (addrArg1 message)).toNat) ∧
      ((balanceOf message state (addrArg2 message)).toNat + (arg3 message).toNat < 2 ^ 256) ∧
      ((arg3 message).toNat ≤ (allowance message state (addrArg1 message) (sender message)).toNat)) ∧
    ((s.output = wordBytes 1) ∧
      ((addrArg2 message) ≠ (addrArg1 message) → (balanceOf message s.state (addrArg1 message)).toNat = (balanceOf message state (addrArg1 message)).toNat - (arg3 message).toNat ∧ (balanceOf message s.state (addrArg2 message)).toNat = (balanceOf message state (addrArg2 message)).toNat + (arg3 message).toNat) ∧
      ((addrArg2 message) = (addrArg1 message) → balanceOf message s.state (addrArg1 message) = balanceOf message state (addrArg1 message)) ∧
      ((allowance message s.state (addrArg1 message) (sender message)).toNat = (allowance message state (addrArg1 message) (sender message)).toNat - (arg3 message).toNat) ∧
      (totalSupply message s.state = totalSupply message state) ∧
      (∀ k, k ≠ mapSlot (addrArg1 message) 5 → k ≠ mapSlot (addrArg2 message) 5 → k ≠ mapSlot (sender message) (mapSlot (addrArg1 message) 7) → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER (addrArg1 message) (addrArg2 message) (wordBytes (arg3 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_transferFrom hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  have hd2 : (isZero (isZero (lessThan (add (storageAt (writeSlot (readSlot (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (7 : U256)))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256)) (sub (storageAt (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (7 : U256)))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) (loadWord message.data 68 32))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) (loadWord message.data 68 32)) (storageAt (writeSlot (readSlot (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (7 : U256)))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256)) (sub (storageAt (readSlot (readSlot (readSlot (readSlot state message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256)) (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (7 : U256)))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32)))) (5 : U256))) (loadWord message.data 68 32))) message.currentTarget (mapSlot (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32)))) (5 : U256)))))) = 0 := by dead_credit hc4 hc5
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  by_cases hd1 : (addrArg2 message) = (addrArg1 message)
  · simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE] at hd1
    try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4 hc5 hc6 hc7 hd2
    have v1 := Readable.value_of_cond hc1
    have n2 := Readable.ne_of_cond1 hc2
    have p3 := Readable.pos_of_cond hc3
    have l4 := Supply.le_of_cond_lt1 hc4
    have f4 := Supply.sub_fact_lt1 hc4
    have b5 := Readable.add_bound_lt hc5
    have f5 := Supply.add_fact_lt hc5
    have l6 := Readable.le_of_cond_gt1 hc6
    have f7 := Supply.sub_fact hc7
    have g2 := Supply.add_fact2 hd2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)
  · have hd1' : ¬((addrArg1 message) = (addrArg2 message)) := fun e => hd1 e.symm
    simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE] at hd1 hd1'
    try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4 hc5 hc6 hc7 hd2
    have v1 := Readable.value_of_cond hc1
    have n2 := Readable.ne_of_cond1 hc2
    have p3 := Readable.pos_of_cond hc3
    have l4 := Supply.le_of_cond_lt1 hc4
    have f4 := Supply.sub_fact_lt1 hc4
    have b5 := Readable.add_bound_lt hc5
    have f5 := Supply.add_fact_lt hc5
    have l6 := Readable.le_of_cond_gt1 hc6
    have f7 := Supply.sub_fact hc7
    have g2 := Supply.add_fact2 hd2
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
      | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, hd1, hd1', eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- burn(value) by the caller. Success needs: no value, a frame that may write, `value > 0`, `value <= balanceOf[caller]`, `value <= totalSupply`. It returns 1, lowers `balanceOf[caller]` and `totalSupply` by `value`, keeps every other slot, and logs Burn(caller, value). -/
theorem burn_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x42966c68)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      (0 < (arg1 message).toNat) ∧
      ((arg1 message).toNat ≤ (balanceOf message state (sender message)).toNat) ∧
      ((arg1 message).toNat ≤ (totalSupply message state).toNat)) ∧
    ((s.output = wordBytes 1) ∧
      ((balanceOf message s.state (sender message)).toNat = (balanceOf message state (sender message)).toNat - (arg1 message).toNat) ∧
      ((totalSupply message s.state).toNat = (totalSupply message state).toNat - (arg1 message).toNat) ∧
      (∀ k, k ≠ mapSlot (sender message) 5 → k ≠ 3 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs.push (log2 message.currentTarget BURN (sender message) (wordBytes (arg1 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_burn hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4
  have v1 := Readable.value_of_cond hc1
  have l2 := Supply.le_of_cond_lt1 hc2
  have f2 := Supply.sub_fact_lt1 hc2
  have p3 := Readable.pos_of_cond hc3
  have l4 := Supply.le_of_cond_gt hc4
  have f4 := Supply.sub_fact hc4
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- freeze(value) by the caller. Success needs: no value, a frame that may write, `value > 0`, `value <= balanceOf[caller]`, no overflow of `freezeOf[caller] + value`. It returns 1, moves `value` from `balanceOf[caller]` to `freezeOf[caller]`, keeps `totalSupply` and every other slot, and logs Freeze(caller, value). -/
theorem freeze_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0xd7a78db8)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      (0 < (arg1 message).toNat) ∧
      ((arg1 message).toNat ≤ (balanceOf message state (sender message)).toNat) ∧
      ((freezeOf message state (sender message)).toNat + (arg1 message).toNat < 2 ^ 256)) ∧
    ((s.output = wordBytes 1) ∧
      ((balanceOf message s.state (sender message)).toNat = (balanceOf message state (sender message)).toNat - (arg1 message).toNat) ∧
      ((freezeOf message s.state (sender message)).toNat = (freezeOf message state (sender message)).toNat + (arg1 message).toNat) ∧
      (totalSupply message s.state = totalSupply message state) ∧
      (∀ k, k ≠ mapSlot (sender message) 5 → k ≠ mapSlot (sender message) 6 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs.push (log2 message.currentTarget FREEZE (sender message) (wordBytes (arg1 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_freeze hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4
  have v1 := Readable.value_of_cond hc1
  have l2 := Supply.le_of_cond_lt1 hc2
  have f2 := Supply.sub_fact_lt1 hc2
  have p3 := Readable.pos_of_cond hc3
  have f4 := Supply.add_fact2 hc4
  have b4 := Supply.add_bound2 hc4
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

/-- unfreeze(value) by the caller. Success needs: no value, a frame that may write, `value > 0`, `value <= freezeOf[caller]`, no overflow of `balanceOf[caller] + value`. It returns 1, moves `value` from `freezeOf[caller]` to `balanceOf[caller]`, keeps `totalSupply` and every other slot, and logs Unfreeze(caller, value). -/
theorem unfreeze_readable (hfork : .berlin ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x6623fc46)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : Ends fork evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      (0 < (arg1 message).toNat) ∧
      ((arg1 message).toNat ≤ (freezeOf message state (sender message)).toNat) ∧
      ((balanceOf message state (sender message)).toNat + (arg1 message).toNat < 2 ^ 256)) ∧
    ((s.output = wordBytes 1) ∧
      ((freezeOf message s.state (sender message)).toNat = (freezeOf message state (sender message)).toNat - (arg1 message).toNat) ∧
      ((balanceOf message s.state (sender message)).toNat = (balanceOf message state (sender message)).toNat + (arg1 message).toNat) ∧
      (totalSupply message s.state = totalSupply message state) ∧
      (∀ k, k ≠ mapSlot (sender message) 5 → k ≠ mapSlot (sender message) 6 → storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs = substate.logs.push (log2 message.currentTarget UNFREEZE (sender message) (wordBytes (arg1 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_unfreeze hfork hsize' hsel start hrun hok
  clear hgas hg start hrun hok
  try simp only [balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm1 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) message.caller.toU256 ∈ callKeys message := by simp [callKeys]
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  have hm3 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 36 32) ∈ callKeys message := by simp [callKeys]
  try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hc1 hc2 hc3 hc4
  have v1 := Readable.value_of_cond hc1
  have l2 := Supply.le_of_cond_lt1 hc2
  have f2 := Supply.sub_fact_lt1 hc2
  have p3 := Readable.pos_of_cond hc3
  have f4 := Supply.add_fact2 hc4
  have b4 := Supply.add_bound2 hc4
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]; done)
    | ((try simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte3, Readable.div_one, slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep, eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte]); readable_close)

end BnbVerify.Readable

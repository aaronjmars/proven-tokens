import EnaVerify.Ena.Readable

/-!
# Readable corollary of `mint`, written by hand

`mint_readable`: who may mint, the wait between two mints and the cap on the amount, as the
bytecode checks them, and the exact effect of a successful mint.

Read from the bytes (function at pc 0x556):

- only the owner: the caller must be the address in the low 160 bits of slot 0;
- the wait: `block.timestamp - lastMintTimestamp` is computed with a check (it reverts when the
  block time is below the last mint time) and must be at least 31536000 seconds (365 days);
  `lastMintTimestamp` is the 40 low bits of slot 11;
- the cap: `amount <= (10 * totalSupply) / 100`, with a checked product, so one mint adds at most
  10 percent of the total supply before the mint, rounded down;
- then slot 11 gets the 40 low bits of the block time (its 216 high bits are kept), the total
  supply and the balance of `to` grow by `amount`, and two logs are added:
  Transfer(0, to, amount) and Mint(to, amount).

The theorem takes `Sep (callKeys message)` (the hypothesis on keccak of Sep.lean, not proved):
without it the balance slot of `to` could be slot 4 or slot 11.

The balance of `to` is stated as a 256-bit sum, because the bytecode adds it with no check;
`mint_no_wrap` of ReadableLib.lean shows that the sum does not wrap under the supply invariant.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace EnaVerify.Readable

open UsdtVerify
open TokenKit TokenKit.Complete TokenKit.Readable
open EnaVerify EnaVerify.Paths EnaVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

variable {fork : Fork} {message : Message fork}
variable {state : State.TransactionState} {substate : Substate}
variable {bound : Nat} {runChild : MessageRunner fork Nat bound}

/-- Slot 11 (`lastMintTimestamp`) is the balance slot of no address. -/
theorem slot_last_bal {A : List U256} (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    ((11 : U256) = mapSlot x 2) = False :=
  eq_false (hsep.fixed.2.2 x hx)

theorem slot_bal_last {A : List U256} (hsep : Sep A) {x : U256} (hx : x.toNat < 2 ^ 160) :
    (mapSlot x 2 = (11 : U256)) = False :=
  eq_false (fun e => hsep.fixed.2.2 x hx e.symm)

/-- The rewriting of the end state of `mint`: reads of the written slots, and the logs. -/
macro "mint_simp" h:ident loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot,
      mask_idem, Readable.logs_logSub, Readable.logs_logSub2, Readable.logs_storeSub,
      Readable.logs_accessSlot, Readable.log3, Readable.log2, Readable.low_byte,
      slot_bal_bal $h, slot_tot_bal $h, slot_bal_tot $h, slot_last_bal $h, slot_bal_last $h,
      and_mask_comm, mask_toU256', m40_or_high,
      eq_false (by decide : (4 : U256) ≠ 11), eq_false (by decide : (11 : U256) ≠ 4),
      eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte] $[$loc]?)

set_option maxHeartbeats 4000000 in
/-- mint(to, amount). Success needs: no value, 68 bytes of call data, a clean address word, a
frame that may write, the caller is the owner (the address in slot 0), the block time is at least
`lastMintTimestamp` plus 31536000 seconds (365 days), `amount` is at most 10 percent of the total
supply rounded down (`10 * _totalSupply / 100`, and `10 * _totalSupply` fits in a word), `to` is
not 0, and `_totalSupply + amount` fits in a word. Then: returns nothing; slot 11 is the 40 low
bits of the block time with the 216 high bits of the old word, so `lastMintTimestamp` is the 40
low bits of the block time; `_totalSupply` is the old word plus `amount`; `_balances[to]` is the
old word plus `amount` as a 256-bit word (the bytecode does not check this addition:
`mint_no_wrap` shows that it does not wrap under the supply invariant); every other slot keeps
its word; exactly two logs, Transfer(0, to, amount) then Mint(to, amount). -/
theorem mint_readable (hfork : .shapella ≤ fork)
    (hsize' : message.data.size < 2 ^ 256)
    (hsel : selector message.data = 0x40c10f19)
    (hsep : Sep (callKeys message))
    {gas : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
    (hrun : EndsL runChild evm s) (hok : s.error = none) :
    ((message.value = 0) ∧
      (4 + 64 ≤ message.data.size) ∧
      (arg1 message = addrArg1 message) ∧
      (message.isStatic = false) ∧
      (hasAccount state message.currentTarget) ∧
      (callerW message = ownerOf message state) ∧
      ((lastMintOf message state).toNat + 31536000 ≤ message.blockEnv.timestamp.toNat) ∧
      (10 * (totalSupply message state).toNat < 2 ^ 256) ∧
      ((arg2 message).toNat ≤ 10 * (totalSupply message state).toNat / 100) ∧
      (addrArg1 message ≠ 0) ∧
      ((arg2 message).toNat + (totalSupply message state).toNat < 2 ^ 256)) ∧
    ((s.output = ByteArray.empty) ∧
      (storageAt s.state message.currentTarget 11 =
        bitwiseOr (bitwiseAnd (1099511627775 : U256) message.blockEnv.timestamp)
          (bitwiseAnd (115792089237316195423570985008687907853269984665640564039457584006813618012160 : U256)
            (storageAt state message.currentTarget 11))) ∧
      (lastMintOf message s.state = bitwiseAnd (1099511627775 : U256) message.blockEnv.timestamp) ∧
      ((totalSupply message s.state).toNat =
        (arg2 message).toNat + (totalSupply message state).toNat) ∧
      (balance message s.state (addrArg1 message) =
        add (arg2 message) (balance message state (addrArg1 message))) ∧
      (∀ k, k ≠ 11 → k ≠ 4 → k ≠ mapSlot (addrArg1 message) 2 →
        storageAt s.state message.currentTarget k = storageAt state message.currentTarget k) ∧
      (s.substate.logs =
        (substate.logs.push (log3 message.currentTarget TRANSFER 0 (addrArg1 message)
          (wordBytes (arg2 message)))).push
          (log2 message.currentTarget MINT (addrArg1 message) (wordBytes (arg2 message))))) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hstatic, hacc, hgas, hout, hg, hst, hsub⟩ :=
    ok_mint hfork hsize' hsel start hrun hok
  obtain ⟨hsize, -, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok
  clear hgas hg start hrun hok
  simp only [balance, totalSupply, addrArg1, arg1, arg2, callerW, ownerOf, lastMintOf, TRANSFER, MINT]
  rw [hst, hout, hsub]
  clear hst hout hsub
  have hm2 : bitwiseAnd (1461501637330902918203684832716283019655932542975 : U256) (loadWord message.data 4 32) ∈ callKeys message := by simp [callKeys]
  mint_simp hsep at hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10
  refine ⟨⟨Readable.value_of_cond hc1, Readable.size_of_slt hsize hsize' (by decide) hc2,
    Readable.eq_of_equal hc3, hstatic, hacc, Readable.eq_of_equal hc4, mint_wait_nat hc5 hc6,
    mul10_bound hc7, mint_cap_nat hc7 hc8, hc9, Supply.add_bound_gtc hc10⟩,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · first
      | (mint_simp hsep; done)
      | rfl
  · first
      | (mint_simp hsep; done)
      | rfl
  · first
      | (mint_simp hsep; done)
      | (mint_simp hsep; exact Supply.add_nat_gtc hc10)
  · first
      | (mint_simp hsep; done)
      | rfl
  · intro k h1 h2 h3
    simp (disch := slot_side) only [Readable.storageAt_writeSlot_ite, storageAt_readSlot, and_mask_comm, h1, h2, h3,
      ↓reduceIte]
  · first
      | (mint_simp hsep; done)
      | rfl
      | (mint_simp hsep; rfl)

end EnaVerify.Readable

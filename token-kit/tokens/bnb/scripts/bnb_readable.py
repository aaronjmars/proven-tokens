#!/usr/bin/env python3
"""Write BnbVerify/Bnb/Readable.lean: the readable corollaries of BNB. The statements are written
here by hand (one per function); the script only repeats the long simp lists of the proofs.
Specific to BNB: a new token writes its own statements (see scripts/gen_readable.py for the
ERC-20 shape of SHIB, in the kit). Run by the regen.sh of the kit (config key
`token_generators`). Usage: bnb_readable.py [config/bnb.json]"""
import os

M = '(1461501637330902918203684832716283019655932542975 : U256)'
ABB = 'balanceOf, freezeOf, allowance, totalSupply, sender, addrArg1, addrArg2, arg1, arg2, arg3, TRANSFER, BURN, FREEZE, UNFREEZE'
BASE = ('Readable.storageAt_writeSlot_ite, storageAt_readSlot, mask_idem, Readable.logs_logSub, '
        'Readable.logs_logSub2, Readable.logs_storeSub, Readable.logs_accessSlot, Readable.log3, '
        'Readable.log2, Readable.low_byte3, Readable.div_one')
SLOTS = ('slot_bal_bal hsep, slot_bal_frz hsep, slot_frz_bal hsep, slot_tot_bal hsep, '
         'slot_bal_tot hsep, slot_tot_frz hsep, slot_frz_tot hsep, slot_allow_bal hsep, '
         'slot_bal_allow hsep, slot_allow_tot hsep, slot_tot_allow hsep')
END = 'eq_self, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte'


def simp(extra, sep):
    parts = [BASE] + ([SLOTS] if sep else []) + ([extra] if extra else []) + [END]
    return 'simp (disch := slot_side) only [' + ', '.join(parts) + ']'


HEAD = '''import BnbVerify.Bnb.Invariant
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
open TokenKit
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
abbrev sender (m : Message fork) : U256 := bitwiseAnd MASK_ m.caller.toU256

/-- The first argument word, masked to an address. -/
abbrev addrArg1 (m : Message fork) : U256 := bitwiseAnd MASK_ (loadWord m.data 4 32)

/-- The second argument word, masked to an address. -/
abbrev addrArg2 (m : Message fork) : U256 := bitwiseAnd MASK_ (loadWord m.data 36 32)

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

'''.replace('MASK_', M)

T = 'message.currentTarget'


def thm(name, sel, doc, sep, nconds, wrote, pre, post, facts, split=None, derived=None):
    """pre/post: lists of conjunct strings. facts: lines after the simp of the hypotheses.
    split: (prop, symm) for a by_cases. derived: (name, tactic, text) haves stated first."""
    hcs = [f'hc{i}' for i in range(1, nconds + 1)]
    pat = hcs + (['hstatic', 'hacc'] if wrote else []) + ['hgas', 'hout', 'hg', 'hst', 'hsub']
    o = [f'/-- {doc} -/', f'theorem {name}_readable (hfork : .berlin ≤ fork)',
         "    (hsize' : message.data.size < 2 ^ 256)",
         f'    (hsel : selector message.data = 0x{sel:08x})']
    if sep:
        o.append('    (hsep : Sep (callKeys message))')
    o += ['    {gas : Nat} {evm s : Evm fork Nat}',
          '    (start : At CODE message 0 [] .empty gas state substate evm)',
          '    (hrun : Ends fork evm s) (hok : s.error = none) :',
          '    (' + ' ∧\n      '.join(f'({c})' for c in pre) + ') ∧',
          '    (' + ' ∧\n      '.join(f'({c})' for c in post) + ') := by',
          f"  obtain ⟨{', '.join(pat)}⟩ :=",
          f"    ok_{name} hfork hsize' hsel start hrun hok",
          '  clear hgas hg start hrun hok']
    for (hn, text, tac) in (derived or []):
        o.append(f'  have {hn} : {text} = 0 := by {tac}')
    hyps = hcs + [d[0] for d in (derived or [])]
    o += [f'  try simp only [{ABB}]', '  rw [hst, hout, hsub]', '  clear hst hout hsub']
    for i, key in enumerate(['message.caller.toU256', '(loadWord message.data 4 32)',
                             '(loadWord message.data 36 32)']):
        o.append(f'  have hm{i + 1} : bitwiseAnd {M} {key} ∈ callKeys message := by simp [callKeys]')
    npre, npost = len(pre), len(post)
    ref = ('⟨' + ('⟨' + ', '.join(['?_'] * npre) + '⟩' if npre > 1 else '?_') + ', '
           + ', '.join(['?_'] * npost) + '⟩')

    def body(pad, extra):
        s1 = simp(extra, sep)
        b = [f'{pad}try {s1} at {" ".join(hyps)}']
        b += [pad + f for f in facts]
        b += [f'{pad}refine {ref}', f'{pad}all_goals first',
              f'{pad}  | ({s1}; done)', f'{pad}  | ((try {s1}); readable_close)']
        return b
    if split:
        prop, symm = split
        o.append(f'  by_cases hd1 : {prop}')
        o.append(f'  · simp only [{ABB}] at hd1')
        o += body('    ', 'hd1')
        o.append(f"  · have hd1' : ¬({symm}) := fun e => hd1 e.symm")
        o.append(f"    simp only [{ABB}] at hd1 hd1'")
        o += body('    ', "hd1, hd1'")
    else:
        o += body('  ', '')
    return '\n'.join(o) + '\n\n'


def getter(name, sel, doc, out):
    return thm(name, sel, doc, False, 1, False, ['message.value = 0'],
               [f's.output = {out}',
                f'∀ k, storageAt s.state {T} k = storageAt state {T} k',
                's.substate.logs = substate.logs'],
               ['have v1 := Readable.value_of_cond hc1'])


def derived_of(fn):
    import json
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    d = json.load(open(os.path.join(root, 'work', 'bnb.paths.json')))
    p = [p for p in d[fn]['paths'] if p['kind'] == 'ok'][0]
    return [(hd, c, tac) for (hd, c, taken, tac) in p.get('derived', [])
            if not taken and c.startswith('(isZero (isZero (lessThan (add ')]


def main():
    o = [HEAD]
    B = lambda S, a: f'(balanceOf message {S} ({a} message)).toNat'
    F = lambda S, a: f'(freezeOf message {S} ({a} message)).toNat'
    o.append(getter('totalSupply', 0x18160ddd, 'totalSupply(): no value; returns the word of slot 3; writes nothing and logs nothing.',
                    'wordBytes (totalSupply message state)'))
    o.append(getter('decimals', 0x313ce567, 'decimals(): no value; returns the low byte of slot 2; writes nothing and logs nothing.',
                    f'wordBytes (BitVec.ofNat 256 ((storageAt state {T} 2).toNat % 256))'))
    o.append(getter('owner', 0x8da5cb5b, 'owner(): no value; returns the low 160 bits of slot 4; writes nothing and logs nothing.',
                    f'wordBytes (bitwiseAnd {M} (storageAt state {T} 4))'))
    o.append(getter('balanceOf', 0x70a08231, 'balanceOf(a): no value; returns `balanceOf[a]` (`a` masked to 160 bits; zeros when the call data is short); writes nothing and logs nothing.',
                    'wordBytes (balanceOf message state (addrArg1 message))'))
    o.append(getter('freezeOf', 0xcd4217c1, 'freezeOf(a): no value; returns `freezeOf[a]`; writes nothing and logs nothing.',
                    'wordBytes (freezeOf message state (addrArg1 message))'))
    o.append(getter('allowance', 0xdd62ed3e, 'allowance(o, sp): no value; returns `allowance[o][sp]`; writes nothing and logs nothing.',
                    'wordBytes (allowance message state (addrArg1 message) (addrArg2 message))'))
    W = ['message.value = 0', 'message.isStatic = false', f'hasAccount state {T}']
    o.append(thm('approve', 0x095ea7b3,
                 'approve(spender, value) from the caller. Success needs: no value, a frame that may write, `value > 0`. It sets `allowance[caller][spender]` to `value`, returns 1, changes no other slot and logs NOTHING (no Approval event).',
                 True, 2, True, W + ['0 < (arg2 message).toNat'],
                 ['s.output = wordBytes 1',
                  'allowance message s.state (sender message) (addrArg1 message) = arg2 message',
                  f'∀ k, k ≠ mapSlot (addrArg1 message) (mapSlot (sender message) 7) → storageAt s.state {T} k = storageAt state {T} k',
                  's.substate.logs = substate.logs'],
                 ['have v1 := Readable.value_of_cond hc1', 'have p2 := Readable.pos_of_cond hc2']))
    o.append(thm('transfer', 0xa9059cbb,
                 'transfer(to, value) from the caller. Success needs: no value, a frame that may write, `to` not 0, `value > 0`, `value <= balanceOf[caller]`, no overflow of `balanceOf[to] + value`. It returns NO data, moves `value` (to oneself: no change), keeps `totalSupply` and every other slot, and logs Transfer(caller, to, value).',
                 True, 5, True,
                 W + ['(addrArg1 message) ≠ 0', '0 < (arg2 message).toNat',
                      f'(arg2 message).toNat ≤ {B("state", "sender")}',
                      f'{B("state", "addrArg1")} + (arg2 message).toNat < 2 ^ 256'],
                 ['s.output = ByteArray.empty',
                  f'(addrArg1 message) ≠ (sender message) → {B("s.state", "sender")} = {B("state", "sender")} - (arg2 message).toNat ∧ {B("s.state", "addrArg1")} = {B("state", "addrArg1")} + (arg2 message).toNat',
                  '(addrArg1 message) = (sender message) → balanceOf message s.state (sender message) = balanceOf message state (sender message)',
                  'totalSupply message s.state = totalSupply message state',
                  f'∀ k, k ≠ mapSlot (sender message) 5 → k ≠ mapSlot (addrArg1 message) 5 → storageAt s.state {T} k = storageAt state {T} k',
                  's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER (sender message) (addrArg1 message) (wordBytes (arg2 message)))'],
                 ['have v1 := Readable.value_of_cond hc1', 'have n2 := Readable.ne_of_cond1 hc2',
                  'have p3 := Readable.pos_of_cond hc3', 'have l4 := Supply.le_of_cond_lt1 hc4',
                  'have f4 := Supply.sub_fact_lt1 hc4', 'have b5 := Readable.add_bound_lt hc5',
                  'have f5 := Supply.add_fact_lt hc5', 'have g2 := Supply.add_fact2 hd2'],
                 split=('(addrArg1 message) = (sender message)', '(sender message) = (addrArg1 message)'),
                 derived=derived_of('transfer')))
    o.append(thm('transferFrom', 0x23b872dd,
                 'transferFrom(from, to, value) by the caller. Success needs: no value, a frame that may write, `to` not 0, `value > 0`, `value <= balanceOf[from]`, no overflow of `balanceOf[to] + value`, `value <= allowance[from][caller]`. It returns 1, moves `value` (from = to: no change), lowers the allowance by `value`, keeps `totalSupply` and every other slot, and logs Transfer(from, to, value).',
                 True, 7, True,
                 W + ['(addrArg2 message) ≠ 0', '0 < (arg3 message).toNat',
                      f'(arg3 message).toNat ≤ {B("state", "addrArg1")}',
                      f'{B("state", "addrArg2")} + (arg3 message).toNat < 2 ^ 256',
                      '(arg3 message).toNat ≤ (allowance message state (addrArg1 message) (sender message)).toNat'],
                 ['s.output = wordBytes 1',
                  f'(addrArg2 message) ≠ (addrArg1 message) → {B("s.state", "addrArg1")} = {B("state", "addrArg1")} - (arg3 message).toNat ∧ {B("s.state", "addrArg2")} = {B("state", "addrArg2")} + (arg3 message).toNat',
                  '(addrArg2 message) = (addrArg1 message) → balanceOf message s.state (addrArg1 message) = balanceOf message state (addrArg1 message)',
                  '(allowance message s.state (addrArg1 message) (sender message)).toNat = (allowance message state (addrArg1 message) (sender message)).toNat - (arg3 message).toNat',
                  'totalSupply message s.state = totalSupply message state',
                  f'∀ k, k ≠ mapSlot (addrArg1 message) 5 → k ≠ mapSlot (addrArg2 message) 5 → k ≠ mapSlot (sender message) (mapSlot (addrArg1 message) 7) → storageAt s.state {T} k = storageAt state {T} k',
                  's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER (addrArg1 message) (addrArg2 message) (wordBytes (arg3 message)))'],
                 ['have v1 := Readable.value_of_cond hc1', 'have n2 := Readable.ne_of_cond1 hc2',
                  'have p3 := Readable.pos_of_cond hc3', 'have l4 := Supply.le_of_cond_lt1 hc4',
                  'have f4 := Supply.sub_fact_lt1 hc4', 'have b5 := Readable.add_bound_lt hc5',
                  'have f5 := Supply.add_fact_lt hc5', 'have l6 := Readable.le_of_cond_gt1 hc6',
                  'have f7 := Supply.sub_fact hc7', 'have g2 := Supply.add_fact2 hd2'],
                 split=('(addrArg2 message) = (addrArg1 message)', '(addrArg1 message) = (addrArg2 message)'),
                 derived=derived_of('transferFrom')))
    o.append(thm('burn', 0x42966c68,
                 'burn(value) by the caller. Success needs: no value, a frame that may write, `value > 0`, `value <= balanceOf[caller]`, `value <= totalSupply`. It returns 1, lowers `balanceOf[caller]` and `totalSupply` by `value`, keeps every other slot, and logs Burn(caller, value).',
                 True, 4, True,
                 W + ['0 < (arg1 message).toNat', f'(arg1 message).toNat ≤ {B("state", "sender")}',
                      '(arg1 message).toNat ≤ (totalSupply message state).toNat'],
                 ['s.output = wordBytes 1',
                  f'{B("s.state", "sender")} = {B("state", "sender")} - (arg1 message).toNat',
                  '(totalSupply message s.state).toNat = (totalSupply message state).toNat - (arg1 message).toNat',
                  f'∀ k, k ≠ mapSlot (sender message) 5 → k ≠ 3 → storageAt s.state {T} k = storageAt state {T} k',
                  's.substate.logs = substate.logs.push (log2 message.currentTarget BURN (sender message) (wordBytes (arg1 message)))'],
                 ['have v1 := Readable.value_of_cond hc1', 'have l2 := Supply.le_of_cond_lt1 hc2',
                  'have f2 := Supply.sub_fact_lt1 hc2', 'have p3 := Readable.pos_of_cond hc3',
                  'have l4 := Supply.le_of_cond_gt hc4', 'have f4 := Supply.sub_fact hc4']))
    for (fn, sel, a, b, A, Bn, ev, Ev) in [
            ('freeze', 0xd7a78db8, B, F, 'balanceOf', 'freezeOf', 'FREEZE', 'Freeze'),
            ('unfreeze', 0x6623fc46, F, B, 'freezeOf', 'balanceOf', 'UNFREEZE', 'Unfreeze')]:
        o.append(thm(fn, sel,
                     f'{fn}(value) by the caller. Success needs: no value, a frame that may write, `value > 0`, `value <= {A}[caller]`, no overflow of `{Bn}[caller] + value`. It returns 1, moves `value` from `{A}[caller]` to `{Bn}[caller]`, keeps `totalSupply` and every other slot, and logs {Ev}(caller, value).',
                     True, 4, True,
                     W + ['0 < (arg1 message).toNat', f'(arg1 message).toNat ≤ {a("state", "sender")}',
                          f'{b("state", "sender")} + (arg1 message).toNat < 2 ^ 256'],
                     ['s.output = wordBytes 1',
                      f'{a("s.state", "sender")} = {a("state", "sender")} - (arg1 message).toNat',
                      f'{b("s.state", "sender")} = {b("state", "sender")} + (arg1 message).toNat',
                      'totalSupply message s.state = totalSupply message state',
                      f'∀ k, k ≠ mapSlot (sender message) 5 → k ≠ mapSlot (sender message) 6 → storageAt s.state {T} k = storageAt state {T} k',
                      f's.substate.logs = substate.logs.push (log2 message.currentTarget {ev} (sender message) (wordBytes (arg1 message)))'],
                     ['have v1 := Readable.value_of_cond hc1', 'have l2 := Supply.le_of_cond_lt1 hc2',
                      'have f2 := Supply.sub_fact_lt1 hc2', 'have p3 := Readable.pos_of_cond hc3',
                      'have f4 := Supply.add_fact2 hc4', 'have b4 := Supply.add_bound2 hc4']))
    o.append('end BnbVerify.Readable\n')
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
    open(os.path.join(root, 'BnbVerify', 'Bnb', 'Readable.lean'), 'w').write(''.join(o))


if __name__ == '__main__':
    main()

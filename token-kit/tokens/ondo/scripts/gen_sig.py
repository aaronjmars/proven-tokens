#!/usr/bin/env python3
"""Write OndoVerify/Ondo/Sig.lean: `delegateBySig` under EthLib's real runner (the copy of
tokens/uni/scripts/gen_sig.py for ONDO: no `permit`).

The generated paths of the function stop at the frame before `GAS STATICCALL` to the
precompile at address 1 (ECRECOVER) and start again after it (the segment of the
configuration). This script joins them across the call with `TokenKit.ecrecover_call_ok`,
with no assumption on what the precompile returns. The words that the code hashes (domain
separator, struct hash, digest) are taken from work/paths.json, as the code builds them.

Usage: python3 scripts/gen_sig.py config/ondo.json   (in tokens/ondo, after gen_paths.py)"""
import json
import os
import re
import sys

cfg = json.load(open(sys.argv[1]))
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(sys.argv[1])))
paths = json.load(open(os.path.join(ROOT, cfg['paths_json'])))
NS = cfg['lean_root']
D = cfg['lean_dir']
SEG = {s['name']: s for s in cfg['segments']}


def fn_of(t, with_state):
    """A term of a path as a term of the parameters `m` (the message) and `S` (the state)."""
    t = re.sub(r'\bmessage\b', 'm', t)
    if with_state:
        t = re.sub(r'\bstate\b', 'S', t)
        t = re.sub(r'\bsubstate\b', 'ss', t)
    return t


def at_path(fn, name):
    return [p for p in paths[fn]['paths'] if p['name'] == name][0]


def mem_index(fn, pname, off, value):
    """The number (from 1) of the conjunct of `<path>_mem` about the word at `off`."""
    src = open(os.path.join(ROOT, NS, D, 'Gen', 'P' + fn[0].upper() + fn[1:] + '.lean')).read()
    L = src.split('\n')
    i = [k for k, l in enumerate(L) if l.startswith('theorem %s_mem' % pname)][0]
    n = 0
    hit = None
    k = i + 1
    while not L[k].startswith('  ⟨'):
        n += 1
        ms = re.findall(r'\) (\d+) 32\) 0 32 = ', L[k])
        if ms and int(ms[-1]) == off and hit is None:
            if value is None or L[k].rstrip().endswith('= %s) ∧' % value):
                hit = n
        k += 1
    assert hit is not None, (pname, off)
    return hit, n


HDEL = ('(hdel : ∀ c, %s.getCode (%s.getAccount (toAddressMasked 1)).codeHash = .ok c →\n'
        '      .pectra ≤ fork → delegatedAddress c = none)')
RUN = ('''    (within : GasMeter.gasHeld %s.gas ≤ bound)
    (hrun : Evm.runFrame (step fork) (step_decreases fork) bound (processRunner fork bound) %s
      within = .ok s)
    (hok : s.error = none) :''')


def after(st, ss, gas):
    """The state, the substate and the gas after the call, from those before it."""
    return ('((%s.recordAccountRead (toAddressMasked 1)).recordAccountRead message.currentTarget)\n'
            '      { %s with accessedAddresses := (%s).accessedAddresses.insert (toAddressMasked 1) }\n'
            '      (%s - 2 - ((sigCall fork (%s) (%s)).cost + 0) +\n'
            '        ((sigCall fork (%s) (%s)).subCall - 3000))' % (st, ss, ss, gas, ss, gas, ss, gas))


def crossing(name, seg, pc, doc):
    """The theorem across the call for one memory layout."""
    s = SEG[seg]
    size = s['raw_mem']['size']
    inn = s['raw_mem']['fp']
    out = int(list(s['raw_mem']['words'])[0])
    tail = s['stack']
    vs = [x for x in tail if isinstance(x, str)]
    rest = ', '.join(('(%d : U256)' % x) if isinstance(x, int) else x for x in tail[1:])
    o = ['/-- %s -/' % doc,
         'theorem %s (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)' % name,
         '    {%s v : U256} {M : ByteArray} {gas : Nat}' % ' '.join(vs),
         '    (hsz : M.size = %d) (hfp : loadWord (memoryReadBytes M 64 32) 0 32 = (%d : U256))' % (size, inn),
         '    (hout : loadWord (memoryReadBytes M %d 32) 0 32 = (0 : U256))' % out,
         '    (h0 : loadWord (memoryReadBytes M %d 32) 0 32 = dg)' % inn,
         '    (h1 : loadWord (memoryReadBytes M %d 32) 0 32 = v)' % (inn + 32),
         '    (h2 : loadWord (memoryReadBytes M %d 32) 0 32 = sigR)' % (inn + 64),
         '    (h3 : loadWord (memoryReadBytes M %d 32) 0 32 = sigS)' % (inn + 96),
         '    ' + HDEL % ('state', 'state'),
         '    {bound : Nat} {z s : Evm fork Nat}',
         '    (start : At CODE message %d [(1 : U256), (%d : U256), (128 : U256), (%d : U256), (32 : U256), %s]'
         % (pc, inn, out, rest),
         '      M gas state substate z)',
         RUN % ('z', 'z'),
         '    3000 ≤ (sigCall fork substate gas).subCall ∧',
         '    Paths.%s_ends fork message' % seg,
         '      ' + after('state', 'substate', 'gas'),
         '      s %s (recoveredWord (sigInput dg v sigR sigS)) := by' % ' '.join(vs),
         '  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis',
         '  have tin : (%d : U256).toNat = %d := by decide' % (inn, inn),
         '  have t128 : (128 : U256).toNat = 128 := by decide',
         '  have tout : (%d : U256).toNat = %d := by decide' % (out, out),
         '  have t32 : (32 : U256).toNat = 32 := by decide',
         '  have hE : extendMemory M.size [((%d : U256), (128 : U256)), ((%d : U256), (32 : U256))] =' % (inn, out),
         '      ⟨0, 0⟩ := extendMemory_two (by rw [hsz]; decide) (by rw [hsz]; decide)',
         '  obtain ⟨hg, after, hat, w, hr⟩ := ecrecover_call_ok hparis hglam (q := %d) rfl' % (pc + 2),
         '    (by code_fact) (by code_fact) (by code_fact) (by code_fact) (by code_fact)',
         '    (by code_fact) (by code_fact) (by code_fact) (by code_fact)',
         '    (by code_fact) (by code_fact) (by code_fact) (by code_fact)',
         '    (by code_fact) (by code_fact) (by code_fact) (by code_fact)',
         '    (by simp [STACK_LIMIT]) hdel start within hrun hok',
         '  rw [hE] at hg hat',
         '  simp only [memoryExtend_zero, tin, t128, tout, t32] at hat',
         '  have hdata : memoryReadBytes M %d 128 = sigInput dg v sigR sigS :=' % inn,
         '    read4_raw h0 h1 h2 h3 hsz (by decide)',
         '  rw [hdata] at hat',
         '  have hfit : %d + 32 ≤ M.size := by rw [hsz]; decide' % out,
         '  refine ⟨hg, ?_⟩',
         '  exact Paths.ok_%s_ends hberlin' % seg,
         '    ((size_ecrecover_write _ hfit).trans hsz)',
         '    ((congrArg (loadWord · 0 32) (read_ecrecover_other _ hfit (.inl (by decide)))).trans hfp)',
         '    (load_ecrecover _ hfit hout) hat ⟨w, hr⟩ hok', '']
    return '\n'.join(o) + '\n'


def main():
    dp = at_path('delegateBySig', 'delegateBySig_p4')
    P1901 = '11309588061646438093662687302255421419811724423900836950936401294474059186176'

    def parts(p):
        dg, sh, ds = p['stack'][8], p['stack'][9], p['stack'][10]
        assert dg == '(keccak (topBytes 2 (%s : U256) (memW [%s, %s])))' % (P1901, ds, sh), p['name']
        return dg, sh, ds

    ddg, dsh, dds = parts(dp)
    assert dp['state'] == 'state' and dp['sub'] == 'substate'
    for t in (dds, dsh):
        assert not re.search(r'\bstate\b', t)

    o = ['''import %(NS)s.%(D)s.Gen
import TokenKit.Evm.Precompile
import TokenKit.Evm.Call

/-!
# `delegateBySig` under EthLib's real runner

Generated by tokens/ondo/scripts/gen_sig.py from work/paths.json.

`delegateBySig(delegatee, nonce, expiry, v, r, s)` (selector `0xc3cda520`) builds an EIP-712
digest in memory and calls the precompile at address 1 (ECRECOVER) with STATICCALL. The
generated paths stop at the frame before `GAS STATICCALL` (pc 5175, `Paths.ok_delegateBySig`)
and start again after it (`Paths.ok_delegateBySigTail_ends`). This file joins them across the
call, for `processRunner`, with no assumption on what the precompile returns: the output is
EthLib's own `Precompiles.Ecrecover.compute` (through `TokenKit.recoveredWord`).

- `sigInput`: the 128 bytes given to ECRECOVER (digest, `v`, `r`, `s`).
- `domainSepName`: the domain separator as the code builds it (keccak of the domain type hash,
  the hash of the name, the chain id and the address of the contract).
- `delegStruct`, `delegDigest`: the struct hash and the digest, as the code builds them (keccak
  of memory bytes: they are not reduced to the Solidity encoding).
- `deleg_call`: across the call, for a memory that holds the four input words.
- `ok_delegateBySig_real`: completeness under the real runner.

Scope: from Paris and before Glamsterdam (EthLib's rules of STATICCALL). `hdel`: the account
at address 1 holds no EIP-7702 delegation code (a fact of the state, true on chain).

A fact about the real contract that these statements show: `delegateBySig` reads
`nonces[signatory]` after the call, for the recovered address.
-/

set_option maxRecDepth 4096

namespace %(NS)s

open UsdtVerify
open TokenKit TokenKit.Complete
open %(NS)s.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

/-- The 128 bytes given to ECRECOVER: the digest, `v`, `r` and `s`. -/
def sigInput (digest v r s : U256) : ByteArray :=
  wordBytes digest ++ wordBytes v ++ wordBytes r ++ wordBytes s

/-- The gas of the call of ECRECOVER from a frame with `gas` at GAS, and what the caller pays:
EthLib's `messageCallGas` for the gas that GAS pushed, no memory growth, and the access of
address 1. -/
abbrev sigCall (fork : Fork) (substate : Substate) (gas : Nat) :=
  messageCallGas fork 0 (BitVec.ofNat 256 (gas - 2)).toNat (gas - 2) 0
    (callBaseCost fork (decide (toAddressMasked 1 ∉ substate.accessedAddresses)) +
      routeCost fork (substate.accessedAddresses.insert (toAddressMasked 1)) none)

variable {fork : Fork} {message : Message fork} {state : State.TransactionState}
  {substate : Substate}
''' % {'NS': NS, 'D': D}]

    def d(name, params, doc, body, kind='def', ty='U256'):
        o.append('/-- %s -/\n%s %s %s : %s :=\n  %s\n' % (doc, kind, name, params, ty, body))

    M_ = '(m : Message fork)'
    MS = '(m : Message fork) (S : State.TransactionState)'
    d('domainSepName', M_, 'The domain separator as `delegateBySig` builds it.', fn_of(dds, False))
    d('delegStruct', M_, 'The struct hash of a `delegateBySig` message.', fn_of(dsh, False))
    d('delegDigest', M_, 'The digest of a `delegateBySig` message.',
      'keccak (topBytes 2 (%s : U256) (memW [domainSepName m, delegStruct m]))' % P1901)
    o.append(crossing('deleg_call', 'delegateBySigTail', 5175,
                      'From Paris and before Glamsterdam, under the real runner: a run from the '
                      'frame of `delegateBySig` before `GAS STATICCALL` (pc 5175) that ends with no '
                      'error. The call of ECRECOVER got at least 3000 gas, and the run ended as '
                      '`Paths.delegateBySigTail_ends` says from the frame after the call, with the '
                      'recovered word `recoveredWord (sigInput digest v r s)`.'))
    def conds(p):
        return ['%s %s 0' % (c[1], '≠' if c[2] else '=') for c in p['conds']]

    def done(seg, p, dgt, sht, dst, st, ss, gas):
        tail = SEG[seg]['stack']
        vals = []
        for i, x in enumerate(tail):
            if not isinstance(x, str):
                continue
            v = p['stack'][4 + i]
            vals.append({'dg': dgt, 'sh': sht, 'ds': dst}.get(x, v))
        inn = SEG[seg]['raw_mem']['fp']
        vterm = '(bitwiseAnd %s (255 : U256))' % vals[[x for x in tail if isinstance(x, str)].index('sigV')]
        rec = '(recoveredWord (sigInput %s %s %s %s))' % (
            dgt, vterm, vals[[x for x in tail if isinstance(x, str)].index('sigR')],
            vals[[x for x in tail if isinstance(x, str)].index('sigS')])
        return ['3000 ≤ (sigCall fork (%s) (%s)).subCall' % (ss, gas),
                'Paths.%s_ends fork message\n      %s\n      s %s\n      %s'
                % (seg, after(st, ss, gas), ' '.join(vals), rec)]

    def mem_pat(fn, p, seg):
        s = SEG[seg]
        inn = s['raw_mem']['fp']
        out = int(list(s['raw_mem']['words'])[0])
        want = {1: 'msz', 2: 'm64'}
        idx, total = mem_index(fn, p['name'], out, '(0 : U256)')
        want[idx] = 'mout'
        idx, _ = mem_index(fn, p['name'], inn, p['stack'][8])
        want[idx] = 'm0'
        for j, nm in ((32, 'm1'), (64, 'm2'), (96, 'm3')):
            idx, _ = mem_index(fn, p['name'], inn + j, None)
            want[idx] = nm
        return '⟨' + ', '.join(want.get(i, '-') for i in range(1, total + 1)) + '⟩'

    # delegateBySig
    cs = conds(dp)
    dn = done('delegateBySigTail', dp, '(delegDigest message)', '(delegStruct message)',
              '(domainSepName message)', 'state', 'substate', '(gas - %s)' % dp['cost'])
    hs = ['hc%d' % (i + 1) for i in range(len(cs))]
    o.append('''/-- Completeness for `delegateBySig`, under EthLib's real runner, from Paris and before
Glamsterdam.

A run of a fresh frame of `CODE` on a message with the selector of `delegateBySig` that ends
with no error: the message carries no value, its call data holds the six arguments,
`delegatee` is a clean address word and `v` is one byte, the gas covered the code before the
call and 3000 for ECRECOVER, and the run ended as `Paths.delegateBySigTail_ends` says
(generated, `Gen/PDelegateBySigTail.lean`) from the state with the reads of the call recorded:
the recovered word is not 0 as an address, `nonce` is `nonces[signatory]`, the time stamp is
not after `expiry`, the nonce is incremented, `delegates[signatory]` is written, the
DelegateChanged log, and then the moves of the votes (a `Paths.mvSrc<n>_ends`).

The recovered word is `recoveredWord (sigInput digest v r s)`: `recoveredWord` is EthLib's
`Precompiles.Ecrecover.compute` read as a word, and nothing is assumed about it. -/
theorem ok_delegateBySig_real (hparis : .paris ≤ fork) (hglam : fork < .glamsterdam)
    (hsize' : message.data.size < 2 ^ 256) (hsel : selector message.data = 0xc3cda520)
    %s
    {gas bound : Nat} {evm s : Evm fork Nat}
    (start : At CODE message 0 [] .empty gas state substate evm)
%s
    %s := by
  have hberlin : Fork.berlin ≤ fork := Nat.le_trans (by decide) hparis
  obtain ⟨%s, hcg, z, hz, w, hzr⟩ :=
    Paths.ok_delegateBySig hberlin hsize' hsel start ⟨within, hrun⟩ hok
  obtain %s :=
    Paths.delegateBySig_p4_mem (message := message)
  have core := deleg_call hparis hglam msz m64 mout m0 m1 m2 m3 hdel hz w hzr hok
  exact ⟨%s, hcg, core.1, core.2⟩
''' % (HDEL % ('state', 'state'), RUN % ('evm', 'evm'),
       ' ∧\n    '.join(cs + ['%s ≤ gas' % dp['cost']] + dn), ', '.join(hs),
       mem_pat('delegateBySig', dp, 'delegateBySigTail'), ', '.join(hs)))

    o.append('end %s\n' % NS)
    out = os.path.join(ROOT, NS, D, 'Sig.lean')
    open(out, 'w').write('\n'.join(o))
    print('Sig.lean written (%d bytes)' % os.path.getsize(out))


main()

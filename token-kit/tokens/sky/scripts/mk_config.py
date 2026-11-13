#!/usr/bin/env python3
"""Write config/sky.json from the USDD configuration (same family: wards, mint, burn, permit).

Usage: python3 scripts/mk_config.py   (run in tokens/sky)
"""
import json
import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
u = json.load(open(os.path.join(HERE, '..', 'usdd', 'config', 'usdd.json')))

c = {}
c['token'] = 'SKY'
c['address'] = '0x56072c95faa701256059aa122697b133aded9279'
c['compiler'] = 'solc 0.8.21, optimizer on (200 runs), EVM paris'
c['lean_root'] = 'SkyVerify'
c['lean_dir'] = 'Sky'
c['hex'] = 'data/sky.runtime.hex'
c['paths_json'] = 'work/paths.json'
c['dispatch'] = {
    'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 128],
    'layout_doc': [
        'Storage layout, read off the bytecode:', '',
        '- `wards[a]` at `mapSlot a 0` (1 = may mint, rely and deny).',
        '- `totalSupply` at slot 1.',
        '- `balanceOf[a]` at `mapSlot a 2`.',
        '- `allowance[owner][spender]` at `mapSlot spender (mapSlot owner 3)`.',
        '- `nonces[a]` at `mapSlot a 4`.',
        '- name, symbol, version, `PERMIT_TYPEHASH`, `deploymentChainId` (1) and the domain',
        '  separator of chain 1 are constants of the code; decimals is 18.']}
c['paths'] = {'raw_memory': 'across_blocks', 'raw_words': True, 'env08': True, 'top_bytes': True,
              'heartbeats': 4000000,
              'block_imports': ['SkyVerify.Sky.Lib']}
c['prune'] = 'normalized'
c['slots'] = {'wards': 0, 'totalSupply': 1, 'balances': 2, 'allowances': 3, 'nonces': 4}
c['functions'] = [
    {'name': 'totalSupply', 'sig': 'totalSupply()'},
    {'name': 'balanceOf', 'sig': 'balanceOf(address)'},
    {'name': 'allowance', 'sig': 'allowance(address,address)'},
    {'name': 'wards', 'sig': 'wards(address)'},
    {'name': 'nonces', 'sig': 'nonces(address)'},
    {'name': 'decimals', 'sig': 'decimals()'},
    {'name': 'domainSeparator', 'sig': 'DOMAIN_SEPARATOR()'},
    {'name': 'permitTypehash', 'sig': 'PERMIT_TYPEHASH()'},
    {'name': 'deploymentChainId', 'sig': 'deploymentChainId()'},
    {'name': 'rely', 'sig': 'rely(address)'},
    {'name': 'deny', 'sig': 'deny(address)'},
    {'name': 'approve', 'sig': 'approve(address,uint256)'},
    {'name': 'transfer', 'sig': 'transfer(address,uint256)'},
    {'name': 'transferFrom', 'sig': 'transferFrom(address,address,uint256)'},
    {'name': 'mint', 'sig': 'mint(address,uint256)'},
    {'name': 'burn', 'sig': 'burn(address,uint256)'},
]
c['fallbacks'] = u['fallbacks']
# ---- permit (hand-written Sky/Permit*.lean join these pieces across the calls) ----
# stops: 3501 GAS before the STATICCALL of ECRECOVER; 3580 EXTCODESIZE of the owner.
# 4202: CALLDATALOAD of the length word of the `bytes` argument of permit(...,bytes), at an
# offset that the call data gives (hand-written Sky/PermitBytes.lean goes on from there).
# 4293: CALLDATACOPY of the bytes, from an offset that the call data gives.
c['stops'] = [3501, 3580, 3660, 3681, 4202, 4293]
c['prefix_functions'] = [
    {'name': 'permit', 'sig': 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)'},
    {'name': 'permitBytes', 'sig': 'permit(address,address,uint256,uint256,bytes)'}]
# The memory has two layouts: the chain id is 1 (the domain separator is a constant of the code,
# free memory pointer 579 at the call) or not (the code builds it, free memory pointer 899).
LAYOUTS = {'A': 579, 'B': 899}
# permit(...,bytes) with a signature of 65 bytes reaches the same code with another end of the
# stack (it returns to 558, not to 3182) and a free memory pointer 31 bytes higher (the bytes
# are copied from the call data and the allocation is rounded up to a word): layouts C (chain
# id 1, free memory pointer 610 at the call) and D (930).
TAIL_V = ['owner', 3182, 'sS', 'sR', 'sv', 'deadline', 'value', 'spender', 'owner', 558, 'sel']
TAIL_B = ['owner', 558, 'sel']
LAYOUTS_B = {'C': 610, 'D': 930}
def ends(tag):
    return TAIL_B if tag in LAYOUTS_B else TAIL_V
def msize(tag, fp, used):
    """The size of the memory when the highest byte used is `fp + used`."""
    return (fp + used + 31) // 32 * 32
def rec_segment(tag, fp):
    """The code after the call of ECRECOVER (pc 3503), to the end or to EXTCODESIZE."""
    return {'name': f'permitRec{tag}', 'pc': 3503,
            'stack': [1, fp + 128, 1, 'vb', 'sS', 'sR', 0, 128, 'dg', 'owner', 2739, 'dg',
                      'nonce', 128, 'deadline', 'value', 'spender'] + ends(tag),
            'raw_mem': {'size': msize(tag, fp, 128), 'fp': fp,
                        'words': {str(fp - 32): 'rec', '96': 0, '128': 65, '160': 'sR',
                                  '192': 'sS'},
                        'tops': {'224': 'vw'}},
            'post_def': True}
# The ERC-1271 branch, from the word that EXTCODESIZE pushed (pc 3581): the owner holds no code
# (revert), or the code encodes isValidSignature(digest, signature) up to pc 3660.
def code_segment(tag, fp):
    return {'name': f'permitCode{tag}', 'pc': 3581,
            'stack': ['cs', 0, 128, 'dg', 'owner', 2739, 'dg',
                      'nonce', 128, 'deadline', 'value', 'spender'] + ends(tag),
            'raw_mem': {'size': msize(tag, fp, 128), 'fp': fp,
                        'words': {'96': 0, '128': 65, '160': 'sR', '192': 'sS'},
                        'tops': {'224': 'vw'}},
            'post_def': True}
# From pc 3660: the copy of the 196 bytes of the call data of isValidSignature to the free
# memory, up to GAS before the STATICCALL to the owner (pc 3681).
def tail(tag):
    return ['dg', 'owner', 2739, 'dg', 'nonce', 128, 'deadline', 'value', 'spender'] + ends(tag)
def copy_segment(tag, fp):
    return {'name': f'permitCopy{tag}', 'pc': 3660,
            'stack': [64, fp, 'ow', 0, 0, 0, 128] + tail(tag),
            'raw_mem': {'size': msize(tag, fp, 228), 'fp': fp + 228,
                        'words': {'96': 0, str(fp): 196}},
            'post_def': True}
# From pc 3725, after the STATICCALL to the owner returned 32 bytes and the code copied them to
# the memory (the word `rw` at fp + 260): the flag and the answer are checked, then the allowance
# is written.
def answer_segment(tag, fp):
    x = fp + 228
    return {'name': f'permitAnswer{tag}', 'pc': 3725,
            'stack': [32, x, 'flag', 0, 0, 0, 128] + tail(tag),
            'raw_mem': {'size': msize(tag, fp, 452), 'fp': x + 64,
                        'words': {'96': 0, str(x): 32, str(x + 32): 'rw'}},
            'post_def': True}
# From pc 3729, after the STATICCALL to the owner returned no byte: every path fails.
def empty_segment(tag, fp):
    return {'name': f'permitEmpty{tag}', 'pc': 3729,
            'stack': [0, 0, 'flag', 0, 0, 0, 128] + tail(tag),
            'raw_mem': {'size': msize(tag, fp, 452), 'fp': fp + 228, 'words': {'96': 0}},
            'post_def': True}
# The body that both functions share (pc 2287), entered by permit(...,bytes) with a signature
# of 65 bytes at 128 (the length, `sR`, `sS` and the first byte of `vw`), to the GAS before the
# STATICCALL of ECRECOVER.
body_segment = {'name': 'permitBody', 'pc': 2287,
                'stack': [128, 'deadline', 'value', 'spender', 'owner', 558, 'sel'],
                'raw_mem': {'size': 288, 'fp': 256,
                            'words': {'96': 0, '128': 65, '160': 'sR', '192': 'sS'},
                            'tops': {'224': 'vw'}},
                'post_def': True}
# The decoder of the `bytes` argument after the CALLDATALOAD of its length `len` at `p` (pc
# 4203): the allocation of the memory for any length, up to the CALLDATACOPY (pc 4293).
decode_segment = {'name': 'permitDecode', 'pc': 4203,
                  'stack': ['len', 18446744073709551615, 'p', 0, 'deadline', 'value', 'spender',
                            'owner', 4, 'size', 761, 558, 'sel']}
ALL = list(LAYOUTS.items()) + list(LAYOUTS_B.items())
c['segments'] = [rec_segment(t, fp) for t, fp in ALL] + \
    [code_segment(t, fp) for t, fp in ALL] + \
    [copy_segment(t, fp) for t, fp in ALL] + \
    [answer_segment(t, fp) for t, fp in ALL] + \
    [empty_segment(t, fp) for t, fp in ALL] + [body_segment, decode_segment]
c['readonly_loops'] = u['readonly_loops']
c['generators'] = ['code', 'dispatch', 'paths', 'loops', 'supply', 'readable', 'sanity', 'axioms']
# Sky/BytesGen.lean: the segments of permit(bytes) at memory offsets that depend on the length
# of the signature (a generator of this token, see its head).
c['token_generators'] = ['scripts/symgen.py']
RULES = ('Supply.D_read, D_bal hsep, D_tot hsep, D_allow hsep, D_ward hsep, D_nonce hsep, '
         'storageAt_readSlot, tot_bal hsep, tot_allow hsep, bal_allow hsep')
c['supply'] = {
    'comment': 'checked08 with the switches for unchecked arithmetic (scripts/gen_supply.py): '
               'caller_key raw: the caller is a key with no mask; norm with norm_disch: every key '
               'to one form and every read of totalSupply after a write of a balance or of an '
               'allowance resolved; unchecked: the facts that a balance is at most the sum of '
               'all balances and of the checked addition ISZERO (GT a (ADD v a)); rules with add_bal '
               'and sub_tot: the unchecked sums, whose bounds sky_side proves from the invariant.',
    'checked08': True,
    'caller_key': 'raw',
    'unchecked': True, 'bal_slot': 2, 'tot_slot': 1,
    'what': 'the sum of all balances is `totalSupply`',
    'what_kept': 'if the sum of all balances was `totalSupply` before, it is after.',
    'norm': "and_mask_comm, mask_idem, mask_toU256', storageAt_readSlot, tot_bal hsep, tot_allow hsep, bal_allow hsep",
    'norm_disch': 'slot_side',
    'disch': 'sky_side hsep',
    'rules': RULES + ', add_bal, sub_tot',
}
c['events'] = {'TRANSFER': 'Transfer(address,address,uint256)',
               'APPROVAL': 'Approval(address,address,uint256)',
               'RELY': 'Rely(address)', 'DENY': 'Deny(address)'}

# ---- readable corollaries (scripts/gen_readable.py) ----
MAXW = '(115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256)'
KEEP = '∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
NOLOG = 's.substate.logs = substate.logs'
c['readable_opts'] = {
    'comment': 'facts checked08 with symm (an equation in both directions) and add_gt (the checked '
               'addition of mint); caller_key raw; several_paths same_claims; simp: more rewrite '
               'rules (the log of two topics of rely and deny; v + (a - v) = a for a transfer to '
               'oneself); header/unfold: more abbreviations of the token.',
    'facts': 'checked08', 'symm': True, 'add_gt': True,
    'caller_key': 'raw',
    'close': 'readable_close08',
    'several_paths': 'same_claims',
    'imports': ['TokenKit.Evm.ReadableOpt', 'TokenKit.Evm.SupplyUnchecked'],
    'simp': ['and_mask_comm', "mask_toU256'", 'Readable.logs_logSub2', 'Readable.log2',
             'Supply.add_sub_self'],
    'unfold': ['callerW', 'thisW', 'chainIdW', 'wardOf', 'nonceOf', 'PERMIT_TYPEHASH',
               'DOMAIN_SEPARATOR_MAINNET', 'domainSeparatorOf'],
    'header': [
        '/-- The caller, as a word (an address word: below 2^160). -/\n'
        'abbrev callerW (m : Message fork) : U256 := m.caller.toU256',
        '/-- The address of the called contract, as a word. -/\n'
        'abbrev thisW (m : Message fork) : U256 := m.currentTarget.toU256',
        '/-- The chain id of the block, as a word (what CHAINID pushes). -/\n'
        'abbrev chainIdW (m : Message fork) : U256 := BitVec.ofNat 256 m.blockEnv.chainId.toNat',
        '/-- `wards[a]` of the called contract in the state `S` (1: `a` may call rely, deny and '
        'mint). -/\nabbrev wardOf (m : Message fork) (S : State.TransactionState) (a : U256) : U256 :=\n'
        '  storageAt S m.currentTarget (mapSlot a 0)',
        '/-- `nonces[a]` of the called contract in the state `S`. -/\n'
        'abbrev nonceOf (m : Message fork) (S : State.TransactionState) (a : U256) : U256 :=\n'
        '  storageAt S m.currentTarget (mapSlot a 4)',
        '/-- `PERMIT_TYPEHASH`, a constant of the code. -/\nabbrev PERMIT_TYPEHASH : U256 :=\n'
        '  (49955707469362902507454157297736832118868343942642399513960811609542965143241 : U256)',
        '/-- The domain separator that the code holds as a constant and returns when the chain id '
        'is 1. -/\nabbrev DOMAIN_SEPARATOR_MAINNET : U256 :=\n'
        '  (88021402408547776102591478376141464261910208107393209539845231887077057693780 : U256)',
        '/-- The domain separator that the code computes when the chain id is not 1: the keccak of '
        'five words (the EIP-712 domain type hash, the hash of the name, the hash of the version, '
        'the chain id, the address of the contract). -/\n'
        'abbrev domainSeparatorOf (m : Message fork) : U256 :=\n'
        '  keccak (memW [(63076024560530113402979550242307453568063438748328787417531900361828837441551 : U256), '
        '(42607552171995751425823498296870486043198744678280595602348571221231826827713 : U256), '
        '(90743482286830539503240959006302832933333810038750515972785732718729991261126 : U256), '
        '(BitVec.ofNat 256 m.blockEnv.chainId.toNat), m.currentTarget.toU256])',
    ],
    'heartbeats': 4000000,
}
def view0(doc, out):
    return {'doc': doc, 'requires': ['message.value = 0'],
            'ensures': ['s.output = wordBytes ' + out, KEEP, NOLOG]}
def view1(doc, out):
    return {'doc': doc, 'let': {'a': 'arg1 message'},
            'requires': ['message.value = 0', '4 + 32 ≤ message.data.size',
                         '{a} = addrArg1 message'],
            'ensures': ['s.output = wordBytes ' + out, KEEP, NOLOG]}
CLEAN = ' the address argument must be a clean address word (dirty high bits revert);'
def ward(fn, v, EV):
    return {
        'doc': f'{fn}(usr). Success needs: no value, 36 bytes of call data,{CLEAN} a frame that '
               f'may write, and `wards[caller] = 1`. Then: returns nothing; `wards[usr]` is {v}; '
               f'every other slot keeps its word; exactly one log, {fn.capitalize()}(usr) '
               '(two topics, no data).',
        'let': {'usr': 'addrArg1 message', 'caller': 'callerW message'},
        'sep': False,
        'requires': ['message.value = 0', '4 + 32 ≤ message.data.size',
                     'arg1 message = {usr}', 'message.isStatic = false',
                     'hasAccount state message.currentTarget', 'wardOf message state {caller} = 1'],
        'ensures': ['s.output = ByteArray.empty', f'wardOf message s.state {{usr}} = {v}',
                    '∀ k, k ≠ mapSlot {usr} 0 → storageAt s.state message.currentTarget k = '
                    'storageAt state message.currentTarget k',
                    f's.substate.logs = substate.logs.push (log2 message.currentTarget {EV} '
                    '{usr} ByteArray.empty)']}
ALLOW_REQ = ('{spender} ≠ {from} → (allowance message state {from} {spender}) ≠ ' + MAXW +
             ' → {amount}.toNat ≤ (allowance message state {from} {spender}).toNat')
ALLOW_ENS = [
    '{spender} ≠ {from} → (allowance message state {from} {spender}) ≠ ' + MAXW +
    ' → (allowance message s.state {from} {spender}).toNat = '
    '(allowance message state {from} {spender}).toNat - {amount}.toNat',
    '{spender} = {from} → (allowance message s.state {from} {spender}) = '
    '(allowance message state {from} {spender})',
    '(allowance message state {from} {spender}) = ' + MAXW +
    ' → (allowance message s.state {from} {spender}) = (allowance message state {from} {spender})']
MOVE_ENS = [
    '{to} ≠ {from} → (balance message s.state {from}).toNat = '
    '(balance message state {from}).toNat - {amount}.toNat ∧ '
    'balance message s.state {to} = add {amount} (balance message state {to})',
    '{to} = {from} → balance message s.state {from} = balance message state {from}']
UNCHK = ('The addition to `balanceOf[to]` has no check in the code: the corollary gives the new '
         'word as the 256-bit sum, and `Sky/Exact.lean` proves that under the supply invariant '
         'it is the exact sum.')
c['readable'] = {
    'totalSupply': view0('totalSupply(). Success needs no value. Then: returns the word of slot 1 '
                         '(`totalSupply`); no slot changes; no log.',
                         '(totalSupply message state)'),
    'decimals': view0('decimals(). Success needs no value. Then: returns 18; no slot changes; no log.',
                      '18'),
    'deploymentChainId': view0('deploymentChainId(). Success needs no value. Then: returns 1 (a '
                               'constant of the code); no slot changes; no log.', '1'),
    'permitTypehash': view0('PERMIT_TYPEHASH(). Success needs no value. Then: returns the constant '
                            '0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9; '
                            'no slot changes; no log.', 'PERMIT_TYPEHASH'),
    'domainSeparator': {
        'doc': 'DOMAIN_SEPARATOR(). Success needs no value. Then: when the chain id is 1 it returns '
               'the constant of the code; else it returns the keccak of the five domain words with '
               'the chain id of the block and the address of the contract; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['chainIdW message = 1 → s.output = wordBytes DOMAIN_SEPARATOR_MAINNET',
                    'chainIdW message ≠ 1 → s.output = wordBytes (domainSeparatorOf message)',
                    KEEP, NOLOG]},
    'balanceOf': view1('balanceOf(a). Success needs no value, 36 bytes of call data and a clean '
                       'address word (dirty high bits revert). Then: returns `balanceOf[a]`; no slot '
                       'changes; no log.', '(balance message state {a})'),
    'wards': view1('wards(a). Success needs no value, 36 bytes of call data and a clean address '
                   'word. Then: returns `wards[a]`; no slot changes; no log.',
                   '(wardOf message state {a})'),
    'nonces': view1('nonces(a). Success needs no value, 36 bytes of call data and a clean address '
                    'word. Then: returns `nonces[a]`; no slot changes; no log.',
                    '(nonceOf message state {a})'),
    'allowance': {
        'doc': 'allowance(owner, spender). Success needs no value, 68 bytes of call data and two '
               'clean address words. Then: returns `allowance[owner][spender]`; no slot changes; '
               'no log.',
        'let': {'owner': 'arg1 message', 'spender': 'arg2 message'},
        'requires': ['message.value = 0', '4 + 64 ≤ message.data.size',
                     '{owner} = addrArg1 message', '{spender} = addrArg2 message'],
        'ensures': ['s.output = wordBytes (allowance message state {owner} {spender})', KEEP, NOLOG]},
    'rely': ward('rely', 1, 'RELY'),
    'deny': ward('deny', 0, 'DENY'),
    'approve': {
        'doc': 'approve(spender, value) from the caller. Success needs: no value, 68 bytes of call '
               f'data,{CLEAN} and a frame that may write. Then: returns 1; '
               '`allowance[caller][spender]` is `value`; `totalSupply` and every other slot keep '
               'their word; exactly one log, Approval(caller, spender, value).',
        'let': {'owner': 'callerW message', 'spender': 'addrArg1 message', 'value': 'arg2 message'},
        'requires': ['message.value = 0', '4 + 64 ≤ message.data.size', 'arg1 message = {spender}',
                     'message.isStatic = false', 'hasAccount state message.currentTarget'],
        'ensures': ['s.output = wordBytes 1',
                    'allowance message s.state {owner} {spender} = {value}',
                    'totalSupply message s.state = totalSupply message state',
                    '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 3) → storageAt s.state '
                    'message.currentTarget k = storageAt state message.currentTarget k',
                    's.substate.logs = substate.logs.push (log3 message.currentTarget APPROVAL '
                    '{owner} {spender} (wordBytes {value}))']},
    'transfer': {
        'doc': 'transfer(to, value) with `from` the caller. Success needs: no value, 68 bytes of '
               f'call data,{CLEAN} a frame that may write, `to` is not 0 and is not the contract, '
               'and `value <= balanceOf[from]`. Then: returns 1; `balanceOf[from]` is the old word '
               'minus `value` and `balanceOf[to]` the old word plus `value` (when `to = from` the '
               'balance is unchanged); `totalSupply` and every other slot keep their word; exactly '
               'one log, Transfer(from, to, value). ' + UNCHK,
        'let': {'from': 'callerW message', 'to': 'addrArg1 message', 'amount': 'arg2 message'},
        'cases': ['{to} = {from}'],
        'requires': ['message.value = 0', '4 + 64 ≤ message.data.size', 'arg1 message = {to}',
                     'message.isStatic = false', 'hasAccount state message.currentTarget',
                     '{to} ≠ 0', '{to} ≠ thisW message',
                     '{amount}.toNat ≤ (balance message state {from}).toNat'],
        'ensures': ['s.output = wordBytes 1'] + MOVE_ENS + [
                    'totalSupply message s.state = totalSupply message state',
                    '∀ k, k ≠ mapSlot {from} 2 → k ≠ mapSlot {to} 2 → storageAt s.state '
                    'message.currentTarget k = storageAt state message.currentTarget k',
                    's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER '
                    '{from} {to} (wordBytes {amount}))']},
    'transferFrom': {
        'doc': 'transferFrom(from, to, value). Success needs: no value, 100 bytes of call data, two '
               'clean address words, a frame that may write, `to` is not 0 and is not the contract, '
               '`value <= balanceOf[from]`, and when the caller is not `from` and '
               '`allowance[from][caller]` is not the largest word: `value <= allowance[from][caller]`. '
               'Then: returns 1; `balanceOf[from]` is the old word minus `value` and `balanceOf[to]` '
               'the old word plus `value` (when `to = from` the balance is unchanged); '
               '`allowance[from][caller]` is the old word minus `value` when the caller is not '
               '`from` and the allowance is not the largest word, else it is unchanged; '
               '`totalSupply` and every other slot keep their word; exactly one log, '
               'Transfer(from, to, value) (no Approval log). ' + UNCHK,
        'let': {'from': 'addrArg1 message', 'to': 'addrArg2 message', 'amount': 'arg3 message',
                'spender': 'callerW message'},
        'cases': ['{to} = {from}'],
        'requires': ['message.value = 0', '4 + 96 ≤ message.data.size', 'arg1 message = {from}',
                     'arg2 message = {to}',
                     'message.isStatic = false', 'hasAccount state message.currentTarget',
                     '{to} ≠ 0', '{to} ≠ thisW message',
                     '{amount}.toNat ≤ (balance message state {from}).toNat', ALLOW_REQ],
        'ensures': ['s.output = wordBytes 1'] + MOVE_ENS + ALLOW_ENS + [
                    'totalSupply message s.state = totalSupply message state',
                    '∀ k, k ≠ mapSlot {from} 2 → k ≠ mapSlot {to} 2 → k ≠ mapSlot {spender} '
                    '(mapSlot {from} 3) → storageAt s.state message.currentTarget k = storageAt '
                    'state message.currentTarget k',
                    's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER '
                    '{from} {to} (wordBytes {amount}))']},
    'mint': {
        'doc': 'mint(to, value). Success needs: no value, 68 bytes of call data,' + CLEAN +
               ' a frame that may write, `wards[caller] = 1`, `to` is not 0 and is not the '
               'contract, and no overflow of `totalSupply`. There is no other check: a ward mints '
               'any amount to any such address. Then: returns nothing; `totalSupply` is the old '
               'word plus `value`, `balanceOf[to]` is the old word plus `value` (an addition with '
               'no check in the code: given as the 256-bit sum, exact under the supply invariant, '
               '`Sky/Exact.lean`); every other slot keeps its word; exactly one log, '
               'Transfer(0, to, value).',
        'let': {'from': 'callerW message', 'to': 'addrArg1 message', 'amount': 'arg2 message'},
        'requires': ['message.value = 0', '4 + 64 ≤ message.data.size', 'arg1 message = {to}',
                     'message.isStatic = false', 'hasAccount state message.currentTarget',
                     'wardOf message state {from} = 1', '{to} ≠ 0', '{to} ≠ thisW message',
                     '(totalSupply message state).toNat + {amount}.toNat < 2 ^ 256'],
        'ensures': ['s.output = ByteArray.empty',
                    'balance message s.state {to} = add {amount} (balance message state {to})',
                    '(totalSupply message s.state).toNat = (totalSupply message state).toNat + '
                    '{amount}.toNat',
                    '∀ k, k ≠ mapSlot {to} 2 → k ≠ 1 → storageAt s.state message.currentTarget k = '
                    'storageAt state message.currentTarget k',
                    's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER 0 '
                    '{to} (wordBytes {amount}))']},
    'burn': {
        'doc': 'burn(from, value). Success needs: no value, 68 bytes of call data,' + CLEAN +
               ' a frame that may write, `value <= balanceOf[from]`, and when the caller is not '
               '`from` and `allowance[from][caller]` is not the largest word: '
               '`value <= allowance[from][caller]`. No ward is needed. Then: returns nothing; '
               '`balanceOf[from]` is the old word minus `value`; `totalSupply` is the old word '
               'minus `value` (a subtraction with no check in the code: given as the 256-bit '
               'difference, exact under the supply invariant, `Sky/Exact.lean`); '
               '`allowance[from][caller]` is the old word minus `value` when the caller is not '
               '`from` and the allowance is not the largest word, else it is unchanged; every '
               'other slot keeps its word; exactly one log, Transfer(from, 0, value).',
        'let': {'from': 'addrArg1 message', 'amount': 'arg2 message', 'spender': 'callerW message'},
        'requires': ['message.value = 0', '4 + 64 ≤ message.data.size', 'arg1 message = {from}',
                     'message.isStatic = false', 'hasAccount state message.currentTarget',
                     '{amount}.toNat ≤ (balance message state {from}).toNat', ALLOW_REQ],
        'ensures': ['s.output = ByteArray.empty',
                    '(balance message s.state {from}).toNat = (balance message state {from}).toNat '
                    '- {amount}.toNat',
                    'totalSupply message s.state = sub (totalSupply message state) {amount}']
                   + ALLOW_ENS + [
                    '∀ k, k ≠ mapSlot {from} 2 → k ≠ 1 → k ≠ mapSlot {spender} (mapSlot {from} 3) → '
                    'storageAt s.state message.currentTarget k = storageAt state '
                    'message.currentTarget k',
                    's.substate.logs = substate.logs.push (log3 message.currentTarget TRANSFER '
                    '{from} 0 (wordBytes {amount}))']},
}

# ---- sanity witnesses (scripts/gen_sanity.py, form eval) ----
CW = 'Witness.CALLER1W'
MAXN = 115792089237316195423570985008687907853269984665640564039457584007913129639935
def E(args, slots=()):
    return {'args': list(args), 'slots': [list(x) for x in slots]}
BAL2 = ['mapSlot 2 2', 5]
ALLOW2 = [f'mapSlot {CW} (mapSlot 2 3)', 5]
ALLOWMAX = [f'mapSlot {CW} (mapSlot 2 3)', MAXN]
BALC = [f'mapSlot {CW} 2', 5]
WARD = [f'mapSlot {CW} 0', 1]
c['sanity'] = {
    'comment': 'The witness call of each success path (scripts/gen_sanity.py, form eval). target: '
               'the contract is the one address C of the file (SKY compares the receiver with '
               'its own address); chain_id: the chain id of the block of the witness (the two '
               'paths of DOMAIN_SEPARATOR). The caller is Witness.CALLER1; amounts are 1 and the '
               'balances and allowances used are 5; wards[caller] is 1 where a ward is needed.',
    'imports': ['TokenKit.Evm.WitnessOpt'],
    'target': {'def': 'Vector.replicate 20 2',
               'word': '0x0202020202020202020202020202020202020202'},
    'doc': '`<path>_runs` (or `<fn>_runs` for a function with one success path): in the state with one\n'
           'account at the contract `C` (the address of twenty bytes 2) that holds the stated words at\n'
           'the stated slots (every other slot 0), the stated call from the caller `Witness.CALLER1`\n'
           'meets every hypothesis of the success path theorem; so the loop of the interpreter runs it\n'
           'from pc 0 to the end with no error, for every message runner and every gas bound that\n'
           'holds its gas, with the stated output and end state. Every condition is computed by the\n'
           'kernel, the keccak of each mapping slot included: no hypothesis about keccak is used.',
    'totalSupply': E([]), 'decimals': E([]), 'permitTypehash': E([]), 'deploymentChainId': E([]),
    'domainSeparator': {'domainSeparator_p1': dict(E([]), chain_id=5),
                        'domainSeparator_p2': dict(E([]), chain_id=1)},
    'balanceOf': E([2]), 'wards': E([2]), 'nonces': E([2]), 'allowance': E([2, 3]),
    'rely': E([2], [WARD]), 'deny': E([2], [WARD]),
    'approve': E([2, 7]),
    'transfer': E([2, 1], [BALC]),
    'mint': E([3, 1], [WARD]),
    'transferFrom': {'transferFrom_p8': E([2, 3, 1], [BAL2, ALLOW2]),
                     'transferFrom_p10': E([2, 3, 1], [BAL2, ALLOWMAX]),
                     'transferFrom_p12': E([CW, 3, 1], [BALC])},
    'burn': {'burn_p6': E([2, 1], [BAL2, ALLOW2]),
             'burn_p8': E([2, 1], [BAL2, ALLOWMAX]),
             'burn_p10': E([CW, 1], [BALC])},
}
# ---- the axioms test (scripts/gen_axioms.py) ----
c['axioms'] = {
    'comment': 'names: hand-written theorems checked before the generated ones; after: theorems '
               'of files that import the generated ones; declared_only: leave out a generated '
               'name that no Lean file declares.',
    'declared_only': True,
    'imports': ['SkyVerify.Sky.Invariant', 'SkyVerify.Sky.Readable', 'SkyVerify.Sky.Exact',
                'SkyVerify.Sky.Sanity.Zero', 'SkyVerify.Sky.Seq', 'SkyVerify.Sky.PermitSeq',
                'SkyVerify.Sky.PermitBytesSeq', 'SkyVerify.Sky.Instance',
                'SkyVerify.Sky.PermitRun', 'SkyVerify.Sky.Tx'],
    'names': ['valid_CODE', 'selector_cases', 'ends_ok_dispatch', 'runFrame_ok_dispatch',
              'codeWord_4767'],
    'after': ['ok_permit_ec', 'permit_fail_tail', 'permit_wrong_size', 'permit_after_call',
              'permit_call_A', 'permit_call_B', 'permit_contract_A', 'permit_contract_B',
              'ok_permit_full', 'permit_no_code_fails', 'permitEnd_facts', 'permit_end',
              'supply_permit', 'inv_permitCall', 'inv_callsP', 'permitCall_process',
              'process_step_all', 'process_step_all_inv', 'callsP_process', 'permit_readable',
              'permitBytes_wrong_size', 'permitBytes_after_call', 'permitWrites_shift',
              'permit_call_C', 'permit_call_D', 'permit_contract_C', 'permit_contract_D',
              'loadWord_of_bytes', 'wordBytes_loadWord_at', 'load_rawC', 'load_copyC',
              'bytesMem_size', 'bytesMem_word', 'bytesMem_sig', 'bytesMem_top', 'bytes_copy',
              'ok_permitBytes_decoded', 'permitKept_mono', 'gas_shift_eq', 'ok_permitBytes65_full',
              'permitBytes65_no_code_fails', 'permitEnd_no_code',
              'byteAt_rawW', 'byteAt_rawW_miss', 'byteAt_rawW_hit', 'byteAt_wordOf',
              'read_eq_of_bytes', 'byteAt_wordBytes_lo', 'byteAt_wordBytes_hi',
              'magicOr_lo', 'magicOr_hi', 'read196', 'code_data', 'copy_step', 'copy_data',
              'staticcall_sent', 'ownerCall_of_sends',
              'permitBytes65_end', 'supply_permitBytes65', 'inv_permitBytes65Call',
              'calls65_of_callsP', 'inv_calls65', 'permitBytes65Call_process',
              'process_step_sig65', 'process_step_sig65_inv', 'calls65_process',
              'permitBytes65_readable',
              'W_toNat', 'W_self', 'W_add', 'W_sub', 'lenC_ceil', 'len_small', 'sigFree_W',
              'bytesMemAny_sigMem', 'bytes_copy_any', 'copyMem_spec', 'copy_routine',
              'mw_congr', 'mw_byte', 'size_erc1271Bytes', 'byteAt_erc1271Bytes', 'enc_chain',
              'encoder', 'PermitByContractAny.kept', 'permit_contract_any',
              'nonceM_spec', 'digest_chain', 'digest_part', 'bodyMemC_enc', 'domM_spec',
              'bodyMemD_enc', 'body_C', 'body_D', 'PermitBytes65Checks.any', 'sub65_ne',
              'ok_permitBytes_other', 'ok_permitBytes_full', 'permitBytes_other_no_code_fails',
              'permitByContractAny_facts', 'permitBytes_end', 'supply_permitBytes',
              'PermitBytes65Call.any', 'inv_permitBytesCall', 'calls65_any', 'inv_callsAny',
              'permitBytesCall_process', 'process_step_any', 'process_step_any_inv',
              'callsAny_process', 'permitBytes_readable',
              'TokenKit.RunsTo.step', 'TokenKit.RunsTo.reverts', 'TokenKit.extcodesize_outcome',
              'TokenKit.staticcall_kept', 'TokenKit.staticcall_mem_same',
              'TokenKit.load_copied', 'TokenKit.load_copied_word',
              'inv_goodCall', 'inv_untouched', 'inv_calls',
              'goodCall_process', 'untouched_process_failed', 'process_value_fails',
              'process_step', 'process_step_inv', 'calls_process',
              'Readable.bal_le_tot', 'Readable.add_exact_move', 'Readable.transfer_exact',
              'Readable.transferFrom_exact', 'Readable.mint_exact', 'Readable.burn_exact',
              'Sanity.C_toU256',
              'Witness.caller1_toU256', 'Witness.endsL_of_reaches',
              'TokenKit.chainidK', 'TokenKit.codecopyK', 'TokenKit.log2ZK',
              'TokenKit.Supply.bal_le_D', 'TokenKit.Supply.le_D_of_cond',
              'TokenKit.Supply.add_bal_bound', 'TokenKit.Supply.sub_toNat_le',
              'TokenKit.Supply.add_bound_gt', 'TokenKit.Supply.add_fact_gt',
              'TokenKit.Supply.add_nat_gt', 'TokenKit.Supply.add_sub_self',
              # Sky/Instance.lean: one closed instance (the ten-token audit, fixes 5 and 6)
              'Instance.callKeys_m0', 'Instance.allow_ne_total', 'Instance.nonce_ne_total',
              'Instance.allow_ne_nonce', 'Instance.ward_ne_total', 'Instance.sep_iff',
              'Instance.sep_m0_iff', 'Instance.inv_of_zero',
              'Instance.callsAny_from_zero', 'Instance.getStorage_sState_nil',
              'Instance.inv_start',
              'Instance.noDelegation1_of_emptyHash', 'Instance.noDelegation1_before_pectra',
              'Instance.codeHash_sState', 'Instance.noDelegation1_sState',
              'Instance.supply_m0',
              # Sky/PermitRun.lean: a real permit run with a kernel-checked signature
              'Instance.processMessage_precompile_ok', 'Instance.mcg_facts',
              'Instance.writeMax_le', 'Instance.ecrecover_call_runs',
              'Instance.size_permitData', 'Instance.selector_permitData',
              'Instance.arg1_permitData', 'Instance.arg2_permitData',
              'Instance.arg3_permitData', 'Instance.arg4_permitData',
              'Instance.arg5_permitData', 'Instance.arg6_permitData',
              'Instance.arg7_permitData', 'Instance.deadline_ok',
              'Instance.storageAt_recordAccountRead', 'Instance.hasAccount_recordAccountRead',
              'Instance.permit_runs', 'Instance.permit_runs_inv',
              # Sky/FrameRule.lean and Sky/Tx.lean: whole transactions (the ten-token audit, SKY-3)
              'frameKeepsR_of_real',
              'storageOnly_inv', 'code_size_ne_zero', 'code_not_indicator',
              'code_not_delegated', 'inv_zeroBase', 'realFrameKeeps', 'frameKeepsR',
              'supply_message_any_depth', 'supply_transaction', 'supply_any_transactions',
              'supply_from_zero'],
}
json.dump(c, open(os.path.join(HERE, 'config', 'sky.json'), 'w'), indent=1)
print('wrote config/sky.json')

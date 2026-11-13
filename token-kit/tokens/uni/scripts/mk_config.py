#!/usr/bin/env python3
"""Write config/uni.json (the configuration of the kit generators for UNI).
Usage: python3 scripts/mk_config.py   (in tokens/uni)"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
F = lambda name, sig: {'name': name, 'sig': sig}
cfg = {
    'token': 'UNI',
    'address': '0x1f9840a85d5af5bf1d1762f925bdaddc4201f984',
    'compiler': 'solc 0.5.16, optimizer on (999999 runs), ABIEncoderV2',
    'lean_root': 'UniVerify', 'lean_dir': 'Uni',
    'hex': 'data/uni.runtime.hex', 'paths_json': 'work/paths.json',
    'dispatch': {'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 128]},
    'paths': {'raw_memory': 'across_blocks', 'raw_words': True, 'top_bytes': True,
              'code_copy': True, 'heartbeats': 3200000, 'log_before_sstore': True, 'block_env': True, 'env_local': True,
              # the code of _moveDelegates is proved once per shape of the frame at its entry
              # (6946, the side of the source delegate) and at its middle (7279, the side of
              # the destination delegate), and composed: no product of branches is enumerated
              'auto_chain': {'6946': 'mvSrc', '7279': 'mvDst'},
              'block_imports': ['TokenKit.Evm.EnvL', 'TokenKit.Evm.CodeCopy', 'TokenKit.Evm.Named']},
    'prune': 'normalized',
    'slots': {'totalSupply': 0, 'minter': 1, 'mintingAllowedAfter': 2, 'allowances': 3,
              'balances': 4, 'delegates': 5, 'checkpoints': 6, 'numCheckpoints': 7, 'nonces': 8},
    'functions': [
        F('totalSupply', 'totalSupply()'), F('decimals', 'decimals()'), F('minter', 'minter()'),
        F('mintingAllowedAfter', 'mintingAllowedAfter()'), F('mintCap', 'mintCap()'),
        F('minimumTimeBetweenMints', 'minimumTimeBetweenMints()'),
        F('domainTypehash', 'DOMAIN_TYPEHASH()'), F('delegationTypehash', 'DELEGATION_TYPEHASH()'),
        F('permitTypehash', 'PERMIT_TYPEHASH()'),
        F('balanceOf', 'balanceOf(address)'), F('allowance', 'allowance(address,address)'),
        F('nonces', 'nonces(address)'), F('delegates', 'delegates(address)'),
        F('numCheckpoints', 'numCheckpoints(address)'),
        F('checkpoints', 'checkpoints(address,uint32)'),
        F('getCurrentVotes', 'getCurrentVotes(address)'),
        F('approve', 'approve(address,uint256)'), F('setMinter', 'setMinter(address)'),
        F('transfer', 'transfer(address,uint256)'),
        F('transferFrom', 'transferFrom(address,address,uint256)'),
        F('mint', 'mint(address,uint256)'), F('delegate', 'delegate(address)'),
    ],
    'fallbacks': [{'name': 'valueSent', 'kind': 'value'}, {'name': 'short', 'kind': 'short'},
                  {'name': 'other', 'kind': 'other'}],
    'readonly_loops': [F('name', 'name()'), F('symbol', 'symbol()'),
                       F('getPriorVotes', 'getPriorVotes(address,uint256)')],
    'stops': [4071, 4886],
    'prefix_functions': [F('delegateBySig', 'delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)'),
                         F('permit', 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)')],
    'segments': [
        {'name': 'delegateBySigTail', 'pc': 4073,
         'stack': [1, 770, 1, 0, 'dg', 'sh', 'ds', 'sigS', 'sigR', 'sigV', 'expiry', 'nonce',
                   'delegatee', 633, 'sel'],
         'raw_mem': {'size': 800, 'fp': 642, 'words': {'610': 'rec'}}, 'post_def': True},
        {'name': 'permitMaxTail', 'pc': 4888,
         'stack': [1, 834, 1, 0, 'dg', 'sh', 'ds', 115792089237316195423570985008687907853269984665640564039457584007913129639935, 'sigS', 'sigR', 'sigV', 'deadline',
                   'rawAmount', 'spender', 'owner', 633, 'sel'],
         'raw_mem': {'size': 864, 'fp': 706, 'words': {'674': 'rec'}}, 'post_def': True},
        {'name': 'permitTail', 'pc': 4888,
         'stack': [1, 930, 1, 0, 'dg', 'sh', 'ds', 'amount', 'sigS', 'sigR', 'sigV', 'deadline',
                   'rawAmount', 'spender', 'owner', 633, 'sel'],
         'raw_mem': {'size': 960, 'fp': 802, 'words': {'770': 'rec'}}, 'post_def': True},
    ],
    # 'supply' is not in the list: Frame.lean and Invariant.lean are written by the generator of the
    # token scripts/gen_supply_keys.py (the kit's gen_supply_chain.py with the finite-key `Sep`)
    'generators': ['code', 'dispatch', 'paths', 'loops', 'sanity', 'axioms'],
    # scripts/gen_sig.py: Sig.lean (delegateBySig and permit under the real runner)
    'token_generators': ['scripts/gen_sig.py', 'scripts/gen_supply_keys.py'],
    # scripts/gen_supply_keys.py: Frame.lean (what the segments of _moveDelegates leave
    # unchanged) and Invariant.lean (the sum of the uint96 balances minus totalSupply)
    'supply': {
        'style': 'chain', 'D': 'Dsum', 'inv_unfold': 'SupplyMask.Inv',
        'what': 'the sum of the `uint96` balances of all addresses minus `totalSupply`',
        'frame_pred': 'CkSlot', 'frame_lemma': 'Dsum_frame', 'ro_lemma': 'SupplyMask.D_of_ro',
        'frame_imports': ['UniVerify.Uni.Sep'],
        # the hypothesis on keccak: finitely many slots (the ten-token audit, UNI-2)
        'sep': 'Sep (callKeys message) (ckKeys message state)', 'ck_slots': [6, 7],
        'frame_rules': 'and_mask_comm, mask_idem, storageAt_readSlot, st_ck hk, st_num hk',
        'disch': 'slot_side',
        'norm': "and_mask_comm, mask_idem, mask_toU256', and_m96_comm, m96_idem, storageAt_readSlot",
        'rules': "and_mask_comm, mask_idem, mask_toU256', and_m96_comm, m96_idem, storageAt_readSlot, "
                 'D_rd, D_bal hsep, D_tot hsep, D_allow hsep, D_minter hsep, '
                 'D_after hsep, D_deleg hsep, m96_or',
        'arith': 'toNat_2p96, toNat_zeroW', 'arith_small': 'm96_small',
        'arith_goal': 'sub96_nat, add96_nat, add_nat',
    },
    # scripts/gen_sanity.py (form eval): one concrete call per success path of the functions
    # whose paths end in the function itself. The functions that go on into _moveDelegates
    # (transfer, transferFrom, mint, delegate) and the two that call ECRECOVER have no generated
    # witness: one run of each is written by hand in Uni/Runs.lean and Uni/PermitRun.lean.
    'sanity': dict(
        [(f, {'args': [], 'slots': []}) for f in (
            'totalSupply', 'decimals', 'minter', 'mintingAllowedAfter', 'mintCap',
            'minimumTimeBetweenMints', 'domainTypehash', 'delegationTypehash', 'permitTypehash')]
        + [(f, {'args': [2], 'slots': []}) for f in (
            'balanceOf', 'nonces', 'delegates', 'numCheckpoints')]
        + [('allowance', {'args': [2, 3], 'slots': []}),
           ('checkpoints', {'args': [2, 0], 'slots': []}),
           ('getCurrentVotes', {
               'getCurrentVotes_p3': {'args': [2], 'slots': []},
               'getCurrentVotes_p4': {'args': [2], 'slots': [['mapSlot 2 7', 1]]}}),
           ('approve', {
               'approve_p4': {'args': [2, 115792089237316195423570985008687907853269984665640564039457584007913129639935], 'slots': []},
               'approve_p7': {'args': [2, 7], 'slots': []}}),
           ('setMinter', {'args': [2], 'slots': [[1, 'Witness.CALLER1W']]}),
           ('imports', ['TokenKit.Evm.WitnessOpt']),
           ('comment', 'The witness call of each success path that ends in its function '
                       '(scripts/gen_sanity.py, form eval).')]),
    'events': {'TRANSFER': 'Transfer(address,address,uint256)',
               'APPROVAL': 'Approval(address,address,uint256)'},
}
def theorems(rel):
    """The names of the theorems of one Lean file (empty when the file is not there yet)."""
    f = os.path.join(HERE, '..', rel)
    if not os.path.exists(f):
        return []
    import re
    return re.findall(r'^theorem ([A-Za-z0-9_.\']+)', open(f).read(), re.M)


def more_paths():
    """The path theorems and the completeness theorems of the functions that the kit does not
    list by itself: the two functions that stop at the call of ECRECOVER and the segments of
    _moveDelegates (work/paths.json, when it is there)."""
    f = os.path.join(HERE, '..', 'work', 'paths.json')
    if not os.path.exists(f):
        return []
    d = json.load(open(f))
    out = []
    for fn in sorted(d):
        if fn in ('delegateBySig', 'permit') or fn.startswith('mv') or fn.endswith('Entry'):
            out += [p['name'] for p in d[fn]['paths']]
            out += [p['name'] + '_mem' for p in d[fn]['paths']]
            out += ['ok_' + fn, 'ok_%s_ends' % fn]
    # the names that a generated file declares (not every path has a `_mem` theorem)
    gen = os.path.join(HERE, '..', 'UniVerify', 'Uni', 'Gen')
    have = set()
    for fl in os.listdir(gen) if os.path.isdir(gen) else []:
        have |= set(theorems(os.path.join('UniVerify', 'Uni', 'Gen', fl)))
    return [n for n in out if n in have]


KIT = os.path.join('..', '..', 'TokenKit', 'Evm')
# scripts/gen_axioms.py: the theorems checked by name before the scan of every constant.
# Run this script again after a generation that adds theorems (it reads their names).
cfg['axioms'] = {
    'comment': 'names: hand-written theorems checked before the generated ones; after: theorems '
               'of files that import the generated ones, and of the functions the kit does not '
               'list by itself; declared_only: leave out a generated name that no Lean file '
               'declares.',
    'declared_only': True, 'dotted_decl': True,
    'imports': ['UniVerify.Uni.Invariant', 'UniVerify.Uni.Sig', 'UniVerify.Uni.SigSupply',
                'UniVerify.Uni.Seq', 'UniVerify.Uni.Readable', 'UniVerify.Uni.Sanity.Zero',
                'UniVerify.Uni.Tx', 'UniVerify.Uni.Instance', 'UniVerify.Uni.PermitRun',
                'UniVerify.Uni.Runs'],
    'names': ['valid_CODE', 'selector_cases', 'ends_ok_dispatch', 'runFrame_ok_dispatch'],
    'after': more_paths()
    + [t for f in ('Sep', 'Frame', 'Sig', 'SigSupply', 'Seq', 'Readable')
       for t in theorems(os.path.join('UniVerify', 'Uni', f + '.lean'))]
    + ['delta_step']
    + ['TokenKit.SupplyMask.' + t for t in theorems(os.path.join(KIT, 'SupplyMask.lean'))]
    + ['TokenKit.' + t for t in theorems(os.path.join(KIT, 'Bits96.lean'))]
    + theorems(os.path.join('UniVerify', 'Uni', 'Tx.lean'))
    # Uni/Instance.lean: one closed instance (the ten-token audit, fixes 5 and 6)
    + ['Instance.' + t for t in theorems(os.path.join('UniVerify', 'Uni', 'Instance.lean'))]
    # Uni/PermitRun.lean, Uni/Runs.lean: one successful run of each of the six writers of the
    # Sanity gap (the ten-token audit, fix 6, UNI-3)
    + ['Instance.' + t for t in theorems(os.path.join('UniVerify', 'Uni', 'PermitRun.lean'))]
    + ['Instance.' + t for t in theorems(os.path.join('UniVerify', 'Uni', 'Runs.lean'))],
}
json.dump(cfg, open(os.path.join(HERE, '..', 'config', 'uni.json'), 'w'), indent=1)
print('config/uni.json written')

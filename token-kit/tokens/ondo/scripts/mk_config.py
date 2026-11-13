#!/usr/bin/env python3
"""Write config/ondo.json (the configuration of the kit generators for ONDO).
Usage: python3 scripts/mk_config.py   (in tokens/ondo)"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
F = lambda name, sig: {'name': name, 'sig': sig}
AUTO = {'6501': 'tt', '6912': 'vest', '7089': 'core', '9085': 'mvSrc', '9325': 'mvDst',
        '9509': 'wck'}
NAMES = [F('name', 'name()'), F('symbol', 'symbol()')]
LOOPS = [F('getPriorVotes', 'getPriorVotes(address,uint256)')]
STOPS = [5175]
PREFIX = [F('delegateBySig', 'delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32)')]
SEGMENTS = [{'name': 'delegateBySigTail', 'pc': 5177,
             'stack': [1, 770, 1, 0, 'dg', 'sh', 'ds', 'sigS', 'sigR', 'sigV', 'expiry', 'nonce',
                       'delegatee', 670, 'sel'],
             'raw_mem': {'size': 800, 'fp': 642, 'words': {'610': 'rec'}}, 'post_def': True}]
DEAD = []
AX_IMPORTS = ['OndoVerify.Ondo.Invariant', 'OndoVerify.Ondo.Sig', 'OndoVerify.Ondo.SigSupply',
              'OndoVerify.Ondo.Seq', 'OndoVerify.Ondo.Readable', 'OndoVerify.Ondo.Sanity.Zero']
AX_FILES = ('Arith', 'Sep', 'Frame', 'Invariant', 'Sig', 'SigSupply', 'Seq', 'Readable')
# the ONDO fix round (hand-written): files in namespace OndoVerify, and files in namespace
# OndoVerify.Instance (their names are listed as Instance.<name>)
AX_FILES5 = ('Tx', 'Vesting')
AX_FILES5_INST = ('Instance', 'Votes', 'Runs')
AX_IMPORTS += ['OndoVerify.Ondo.' + f for f in AX_FILES5 + AX_FILES5_INST
               if os.path.exists(os.path.join(HERE, '..', 'OndoVerify', 'Ondo', f + '.lean'))]
# Witness calls (scripts/gen_sanity.py, form eval): one concrete call for each success path that
# ends in its function. CW is the address word of the caller of the witness.
def _E(args=(), slots=()):
    return {'args': list(args), 'slots': [list(x) for x in slots]}
CW = 'Witness.CALLER1W'
def _role(r, who=CW):
    return ['mapSlot %s (mapSlot %s 0)' % (who, r), 1]
MINTER = 71998914331801701415977457805802827292338598818749192222732755537001613711014
TIMELOCK = 105792966476986369818188973763942834817227259111886716069005259966222125283040
IFACE = 54909818011127210282586622383458683342160741266077104324147033802515469565952
MAXW = 2 ** 256 - 1
SANITY = {'imports': ['TokenKit.Evm.WitnessOpt'],
          'comment': 'The witness call of each success path that ends in its function '
                     '(scripts/gen_sanity.py, form eval).'}
for _f in ['totalSupply', 'decimals', 'cliffTimestamp', 'transferAllowed', 'tranche1VestingPeriod',
           'tranche2VestingPeriod', 'seedVestingPeriod', 'domainTypehash', 'delegationTypehash',
           'minterRole', 'transferRole', 'timelockUpdateRole', 'defaultAdminRole', 'passedCliff',
           'passedAllVestingPeriods', 'name', 'symbol']:
    SANITY[_f] = _E()
for _f in ['balanceOf', 'nonces', 'delegates', 'numCheckpoints', 'getRoleAdmin']:
    SANITY[_f] = _E([2])
SANITY['hasRole'] = _E([5, 2])
SANITY['allowance'] = _E([2, 3])
SANITY['checkpoints'] = _E([2, 0])
SANITY['supportsInterface'] = {'supportsInterface_p3': _E([0]), 'supportsInterface_p4': _E([IFACE])}
SANITY['getCurrentVotes'] = {'getCurrentVotes_p3': _E([2]),
                             'getCurrentVotes_p4': _E([2], [['mapSlot 2 9', 1]])}
SANITY['getVestedBalance'] = {'getVestedBalance_p3': _E([2])}
SANITY['approve'] = {'approve_p4': _E([2, MAXW]), 'approve_p7': _E([2, 7])}
SANITY['enableTransfer'] = _E([], [_role(0)])
SANITY['updateCliffTimestamp'] = _E([7], [_role(0)])
SANITY['updateTrancheBalance'] = _E([2, 7, 1], [_role(TIMELOCK)])
SANITY['mint'] = _E([2, 7], [_role(MINTER)])
SANITY['grantRole'] = {'grantRole_p5': _E([5, 2], [_role(0)]),
                       'grantRole_p6': _E([5, 2], [_role(0), _role(5, 2)])}
SANITY['revokeRole'] = {'revokeRole_p5': _E([5, 2], [_role(0), _role(5, 2)]),
                        'revokeRole_p6': _E([5, 2], [_role(0)])}
SANITY['renounceRole'] = {'renounceRole_p5': _E([5, CW], [_role(5)]),
                          'renounceRole_p6': _E([5, CW])}

cfg = {
    'token': 'ONDO',
    'address': '0xfaba6f8e4a5e8ab82f62fe7c39859fa577269be3',
    'compiler': 'solc 0.8.3, optimizer on (100 runs)',
    'lean_root': 'OndoVerify', 'lean_dir': 'Ondo',
    'hex': 'data/ondo.runtime.hex', 'paths_json': 'work/paths.json',
    'dispatch': {'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 128]},
    'paths_imports': ['OndoVerify.Ondo.Arith'],
    'paths': {'dead_table': 'config/dead.json', 'raw_memory': 'across_blocks', 'raw_words': True, 'top_bytes': True,
              'code_copy': True, 'heartbeats': 3200000, 'log_before_sstore': True, 'block_env': True, 'env_local': True,
              # shared code is proved once per shape of the frame at its entry and composed, so
              # no product of branches is enumerated: 6501 _transferTokens, 6912 its vesting
              # check, 7089 its balance moves, 9085 / 9325 the two sides of _moveDelegates,
              # 9509 _writeCheckpoint
              'auto_chain': AUTO,
              'block_imports': ['TokenKit.Evm.EnvL', 'TokenKit.Evm.CodeCopy', 'TokenKit.Evm.Named']},
    'prune': 'normalized',
    'slots': {'roles': 0, 'cliffTimestamp': 1, 'investorBalances': 2, 'transferAllowed': 3,
              'totalSupply': 4, 'allowances': 5, 'balances': 6, 'delegates': 7, 'checkpoints': 8,
              'numCheckpoints': 9, 'nonces': 10},
    'functions': [
        F('totalSupply', 'totalSupply()'), F('decimals', 'decimals()'),
        F('cliffTimestamp', 'cliffTimestamp()'), F('transferAllowed', 'transferAllowed()'),
        F('tranche1VestingPeriod', 'tranche1VestingPeriod()'),
        F('tranche2VestingPeriod', 'tranche2VestingPeriod()'),
        F('seedVestingPeriod', 'seedVestingPeriod()'),
        F('domainTypehash', 'DOMAIN_TYPEHASH()'), F('delegationTypehash', 'DELEGATION_TYPEHASH()'),
        F('minterRole', 'MINTER_ROLE()'), F('transferRole', 'TRANSFER_ROLE()'),
        F('timelockUpdateRole', 'TIMELOCK_UPDATE_ROLE()'), F('defaultAdminRole', 'DEFAULT_ADMIN_ROLE()'),
        F('passedCliff', 'passedCliff()'), F('passedAllVestingPeriods', 'passedAllVestingPeriods()'),
        F('supportsInterface', 'supportsInterface(bytes4)'),
        F('getRoleAdmin', 'getRoleAdmin(bytes32)'), F('hasRole', 'hasRole(bytes32,address)'),
        F('balanceOf', 'balanceOf(address)'), F('allowance', 'allowance(address,address)'),
        F('nonces', 'nonces(address)'), F('delegates', 'delegates(address)'),
        F('numCheckpoints', 'numCheckpoints(address)'),
        F('checkpoints', 'checkpoints(address,uint32)'),
        F('getCurrentVotes', 'getCurrentVotes(address)'),
        F('getFreedBalance', 'getFreedBalance(address)'),
        F('getVestedBalance', 'getVestedBalance(address)'),
        F('approve', 'approve(address,uint256)'),
        F('enableTransfer', 'enableTransfer()'),
        F('updateCliffTimestamp', 'updateCliffTimestamp(uint256)'),
        F('updateTrancheBalance', 'updateTrancheBalance(address,uint256,uint8)'),
        F('grantRole', 'grantRole(bytes32,address)'), F('revokeRole', 'revokeRole(bytes32,address)'),
        F('renounceRole', 'renounceRole(bytes32,address)'),
        F('mint', 'mint(address,uint256)'),
        F('transfer', 'transfer(address,uint256)'),
        F('transferFrom', 'transferFrom(address,address,uint256)'),
        F('delegate', 'delegate(address)'),
    ] + NAMES,
    'fallbacks': [{'name': 'valueSent', 'kind': 'value'}, {'name': 'short', 'kind': 'short'},
                  {'name': 'other', 'kind': 'other'}],
    'readonly_loops': LOOPS,
    'stops': STOPS,
    'prefix_functions': PREFIX,
    'segments': SEGMENTS,
    'dead_branches': DEAD,
    'generators': ['code', 'dispatch', 'paths', 'loops', 'supply', 'sanity', 'axioms'],
    'token_generators': ['scripts/gen_sig.py'],
    'supply': {
        'style': 'chain', 'D': 'Dsum', 'inv_unfold': 'SupplyMask.Inv',
        'what': 'the sum of the `uint96` balances of all addresses minus `totalSupply`',
        'frame_pred': 'CkSlot', 'frame_lemma': 'Dsum_frame', 'ro_lemma': 'SupplyMask.D_of_ro',
        'frame_imports': ['OndoVerify.Ondo.Sep', 'OndoVerify.Ondo.Arith'],
        'imports': ['OndoVerify.Ondo.Arith'],
        'seg_kinds': {'tt': 'delta', 'vest': 'delta', 'core': 'delta',
                      'mvSrc': 'frame', 'mvDst': 'frame', 'wck': 'frame'},
        'sep': 'Sep (callKeys message) (ckKeys message state) (loadWord message.data 4 32)',
        'frame_rules': 'and_mask_comm, mask_idem, storageAt_readSlot, st_ck hk, st_num hk',
        'disch': 'slot_side',
        'norm': "and_mask_comm, mask_idem, mask_toU256', and_m96_comm, m96_idem, storageAt_readSlot",
        'rules': "and_mask_comm, mask_idem, mask_toU256', and_m96_comm, m96_idem, storageAt_readSlot, "
                 'D_rd, D_bal hsep, D_tot hsep, D_allow hsep, D_cliff hsep, D_flag hsep, D_inv hsep, '
                 'D_role hsep, D_deleg hsep, D_nonce hsep, m96_or',
    },
    'sanity': SANITY,
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
        if fn in ('delegateBySig',) or re.sub(r'\d+$', '', fn) in AUTO.values() or fn.endswith('Entry'):
            out += [p['name'] for p in d[fn]['paths']]
            out += [p['name'] + '_mem' for p in d[fn]['paths']]
            out += ['ok_' + fn, 'ok_%s_ends' % fn]
    # the names that a generated file declares (not every path has a `_mem` theorem)
    gen = os.path.join(HERE, '..', 'OndoVerify', 'Ondo', 'Gen')
    have = set()
    for fl in os.listdir(gen) if os.path.isdir(gen) else []:
        have |= set(theorems(os.path.join('OndoVerify', 'Ondo', 'Gen', fl)))
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
    'imports': AX_IMPORTS,
    'names': ['valid_CODE', 'selector_cases', 'ends_ok_dispatch', 'runFrame_ok_dispatch'],
    'after': more_paths()
    + [t for f in AX_FILES
       for t in theorems(os.path.join('OndoVerify', 'Ondo', f + '.lean'))
       # supply_<fn> and supply_preserved of Invariant.lean are listed by gen_axioms.py itself
       if not (f == 'Invariant' and t.startswith('supply_'))]
    + ['TokenKit.SupplyMask.' + t for t in theorems(os.path.join(KIT, 'SupplyMask.lean'))]
    + ['TokenKit.' + t for t in theorems(os.path.join(KIT, 'Bits96.lean'))]
    + [t for f in AX_FILES5 for t in theorems(os.path.join('OndoVerify', 'Ondo', f + '.lean'))]
    + ['Instance.' + t for f in AX_FILES5_INST
       for t in theorems(os.path.join('OndoVerify', 'Ondo', f + '.lean'))],
}
json.dump(cfg, open(os.path.join(HERE, '..', 'config', 'ondo.json'), 'w'), indent=1)
print('config/ondo.json written')

#!/usr/bin/env python3
"""Write config/wbtc.json (built here because it is long and repetitive); then run
scripts/regen_wbtc.sh config/wbtc.json."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
FUNCS = [
    ('mintingFinished', 'mintingFinished()'),
    ('approve', 'approve(address,uint256)'),
    ('totalSupply', 'totalSupply()'),
    ('transferFrom', 'transferFrom(address,address,uint256)'),
    ('decimals', 'decimals()'),
    ('unpause', 'unpause()'),
    ('mint', 'mint(address,uint256)'),
    ('burn', 'burn(uint256)'),
    ('claimOwnership', 'claimOwnership()'),
    ('paused', 'paused()'),
    ('decreaseApproval', 'decreaseApproval(address,uint256)'),
    ('balanceOf', 'balanceOf(address)'),
    ('renounceOwnership', 'renounceOwnership()'),
    ('finishMinting', 'finishMinting()'),
    ('pause', 'pause()'),
    ('owner', 'owner()'),
    ('transfer', 'transfer(address,uint256)'),
    ('increaseApproval', 'increaseApproval(address,uint256)'),
    ('allowance', 'allowance(address,address)'),
    ('pendingOwner', 'pendingOwner()'),
    ('transferOwnership', 'transferOwnership(address)'),
]
cfg = {
    'token': 'WBTC',
    'address': '0x2260fac5e5542a773aa44fbcfedf7c193bc2c599',
    'compiler': 'solc 0.4.24, optimizer on (200 runs)',
    'lean_root': 'WbtcVerify', 'lean_dir': 'Wbtc',
    'hex': 'data/wbtc.runtime.hex', 'paths_json': 'work/paths.json',
    'dispatch': {
        # the ten-token audit, WBTC-5: the default sentence (a table split by GT comparisons) is wrong for
        # this code
        'split_doc': 'The table is linear (solc 0.4, no split by\nGT comparisons): each entry is tested in turn.',
        'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 128],
        'value_check': 'per_function',
        'layout_doc': [
            'Storage layout, read off the bytecode (see docs/MAP.md):', '',
            '- `balances[a]` at `mapSlot a 0`.',
            '- `totalSupply_` at slot 1.',
            '- `allowed[owner][spender]` at `mapSlot spender (mapSlot owner 2)`.',
            '- `name` (a string) at slot 3 and `symbol` (a string) at slot 4.',
            '- slot 5 packs: `decimals` in byte 0, `owner` in bits 8..167, `mintingFinished` in',
            '  byte 21 (bit 168) and `paused` in byte 22 (bit 176).',
            '- `pendingOwner` in the low 160 bits of slot 6.']},
    'paths': {'raw_memory': 'across_blocks', 'raw_words': True, 'env08': True,
              'log_before_sstore': True,
              'block_imports': ['WbtcVerify.Wbtc.Lib']},
    'prune': 'normalized',
    'slots': {'balances': 0, 'totalSupply': 1, 'allowances': 2},
    'functions': [dict(name=n, sig=s) for n, s in FUNCS],
    'fallbacks': [{'name': 'short', 'kind': 'short'}, {'name': 'other', 'kind': 'other'}],
    'readonly_loops': [{'name': 'name', 'sig': 'name()'}, {'name': 'symbol', 'sig': 'symbol()'}],
    'stops': [1521],
    'prefix_functions': [{'name': 'reclaimToken', 'sig': 'reclaimToken(address)'}],
    'generators': ['code', 'dispatch', 'paths', 'loops'],
    'token_generators': ['scripts/gen_value.py'],
    'events': {'TRANSFER': 'Transfer(address,address,uint256)',
               'APPROVAL': 'Approval(address,address,uint256)',
               'MINT': 'Mint(address,uint256)', 'BURN': 'Burn(address,uint256)',
               'PAUSE': 'Pause()', 'UNPAUSE': 'Unpause()',
               'OWNERSHIP_TRANSFERRED': 'OwnershipTransferred(address,address)'},
}
for _m in ['mk_config_more.py', 'mk_config_reclaim.py', 'mk_config_readable.py', 'mk_config_axioms.py']:
    more = os.path.join(HERE, _m)
    if os.path.exists(more):
        exec(open(more).read())
json.dump(cfg, open(os.path.join(HERE, '..', 'config', 'wbtc.json'), 'w'), indent=1)
print('config/wbtc.json written')

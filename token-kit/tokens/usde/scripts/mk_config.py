#!/usr/bin/env python3
"""Write config/usde.json. The configuration is long and repetitive (one readable entry and one
witness per function), so it is built here; run this, then scripts/regen_usde.sh."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
FUNCS = [
    ('totalSupply', 'totalSupply()'), ('balanceOf', 'balanceOf(address)'),
    ('allowance', 'allowance(address,address)'), ('decimals', 'decimals()'),
    ('owner', 'owner()'), ('pendingOwner', 'pendingOwner()'), ('minter', 'minter()'),
    ('nonces', 'nonces(address)'), ('domainSeparator', 'DOMAIN_SEPARATOR()'),
    ('transfer', 'transfer(address,uint256)'), ('approve', 'approve(address,uint256)'),
    ('transferFrom', 'transferFrom(address,address,uint256)'),
    ('increaseAllowance', 'increaseAllowance(address,uint256)'),
    ('decreaseAllowance', 'decreaseAllowance(address,uint256)'),
    ('mint', 'mint(address,uint256)'), ('burn', 'burn(uint256)'),
    ('burnFrom', 'burnFrom(address,uint256)'),
    ('transferOwnership', 'transferOwnership(address)'),
    ('acceptOwnership', 'acceptOwnership()'), ('renounceOwnership', 'renounceOwnership()'),
    ('setMinter', 'setMinter(address)'),
]
cfg = {
    'token': 'USDE',
    'address': '0x4c9edd5852cd905f086c759e8383e09bff1e68b3',
    'compiler': 'solc 0.8.19, optimizer on (20000 runs), EVM paris',
    'lean_root': 'UsdeVerify', 'lean_dir': 'Usde',
    'hex': 'data/usde.runtime.hex', 'paths_json': 'work/paths.json',
    'dispatch': {
        'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 128],
        'layout_doc': [
            'Storage layout, read off the bytecode (see docs/MAP.md):', '',
            '- `_owner` in the low 160 bits of slot 0; `_pendingOwner` in the low 160 bits of slot 1.',
            '- `_balances[a]` at `mapSlot a 2`.',
            '- `_allowances[owner][spender]` at `mapSlot spender (mapSlot owner 3)`.',
            '- `_totalSupply` at slot 4; `_name` at slot 5; `_symbol` at slot 6.',
            '- the fallback strings of the EIP-712 name and version at slots 7 and 8 (not read: both are short strings held in the code).',
            '- `_nonces[a]` at `mapSlot a 9`.',
            '- `minter` in the low 160 bits of slot 11.']},
    'paths': {'raw_memory': 'across_blocks', 'raw_words': True,
              'block_imports': ['UsdeVerify.Usde.Lib'],
              # switches of the shared generators (scripts/ of the kit)
              'env_local': True, 'log_static_alt': True, 'short_revert': True,
              'block_imports_first': True},
    'prune': 'normalized',
    'slots': {'owner': 0, 'pendingOwner': 1, 'balances': 2, 'allowances': 3, 'totalSupply': 4,
              'nonces': 9, 'minter': 11},
    'functions': [dict(name=n, sig=s) for n, s in FUNCS],
    'fallbacks': [{'name': 'valueSent', 'kind': 'value'}, {'name': 'short', 'kind': 'short'},
                  {'name': 'other', 'kind': 'other'}],
    'readonly_loops': [{'name': 'name', 'sig': 'name()'}, {'name': 'symbol', 'sig': 'symbol()'},
                       {'name': 'eip712Domain', 'sig': 'eip712Domain()'}],
    'generators': ['code', 'dispatch', 'paths', 'loops'],
    'events': {'TRANSFER': 'Transfer(address,address,uint256)',
               'APPROVAL': 'Approval(address,address,uint256)',
               'OWNERSHIP': 'OwnershipTransferred(address,address)',
               'OWNERSHIP_STARTED': 'OwnershipTransferStarted(address,address)',
               'MINTER_UPDATED': 'MinterUpdated(address,address)'},
    'stops': [6035],
    'prefix_functions': [{'name': 'permit',
                          'sig': 'permit(address,address,uint256,uint256,uint8,bytes32,bytes32)'}],
    'segments': [],
}
exec(open(os.path.join(HERE, 'mk_config_more.py')).read()) if os.path.exists(os.path.join(HERE, 'mk_config_more.py')) else None
json.dump(cfg, open(os.path.join(HERE, '..', 'config', 'usde.json'), 'w'), indent=1)
print('config/usde.json written')

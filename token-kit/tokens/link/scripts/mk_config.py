#!/usr/bin/env python3
"""Write config/link.json (built here because it is long and repetitive); then run
scripts/regen_link.sh config/link.json."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
FUNCS = [
    ('totalSupply', 'totalSupply()'), ('balanceOf', 'balanceOf(address)'),
    ('allowance', 'allowance(address,address)'), ('decimals', 'decimals()'),
    ('transfer', 'transfer(address,uint256)'), ('approve', 'approve(address,uint256)'),
    ('transferFrom', 'transferFrom(address,address,uint256)'),
    ('increaseApproval', 'increaseApproval(address,uint256)'),
    ('decreaseApproval', 'decreaseApproval(address,uint256)'),
]
cfg = {
    'token': 'LINK',
    'address': '0x514910771af9ca656af840dff83e8264ecf986ca',
    'compiler': 'solc 0.4.16, optimizer on (200 runs)',
    'lean_root': 'LinkVerify', 'lean_dir': 'Link',
    'hex': 'data/link.runtime.hex', 'paths_json': 'work/paths.json',
    'dispatch': {
        'generate': True, 'mode': 'walk', 'memory_words': [0, 0, 96],
        'value_check': 'per_function', 'min_size': 1,
        'size_proof': "obtain ⟨hsize, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok",
        'layout_doc': [
            'Storage layout, read off the bytecode (see docs/MAP.md):', '',
            '- `balances[a]` at `mapSlot a 1`.',
            '- `allowed[owner][spender]` at `mapSlot spender (mapSlot owner 2)`.',
            '- `totalSupply` is the constant 10^27 held in the code (no slot); slot 0 is never read or written.',
            '- `name`, `symbol` and `decimals` are constants held in the code.']},
    'paths': {'raw_memory': 'across_blocks', 'raw_words': True,
              'block_imports': ['LinkVerify.Link.Lib']},
    'prune': 'normalized',
    'slots': {'balances': 1, 'allowances': 2},
    'functions': [dict(name=n, sig=s) for n, s in FUNCS],
    'fallbacks': [{'name': 'short', 'kind': 'short'}, {'name': 'other', 'kind': 'other'}],
    'readonly_loops': [{'name': 'name', 'sig': 'name()'}, {'name': 'symbol', 'sig': 'symbol()'}],
    'stops': [530],
    'prefix_functions': [{'name': 'transferAndCall',
                          'sig': 'transferAndCall(address,uint256,bytes)'}],
    'generators': ['code', 'dispatch', 'paths', 'loops', 'supply', 'sanity'],
    'sanity': {
        'comment': 'The witness call of each success path (scripts/gen_sanity.py, form eval). '
                   'The caller is Witness.CALLER1; amounts are 1 and the balances and '
                   'allowances used are 5.',
        'imports': ['TokenKit.Evm.WitnessOpt'],
        'contract_word': '(0x514910771af9ca656af840dff83e8264ecf986ca : U256)',
        'doc': '`<path>_runs` (or `<fn>_runs` for a function with one success path): in the state with one\naccount at the contract `C` that holds the stated words at the stated slots (every other slot\n0), the stated call from the caller `Witness.CALLER1` meets every hypothesis of the success path\ntheorem; so the loop of the interpreter runs it from pc 0 to the end with no error, for every\nmessage runner and every gas bound that holds its gas, with the stated output and end state.\nEvery condition is computed by the kernel, the keccak of each mapping slot included: no\nhypothesis about keccak is used.\n`hC` fixes the address word of the contract `C` to the address of LINK on mainnet (transfer,\napprove and transferFrom compare the receiver with the address of the contract);\n`Sanity/Addr.lean` gives such an address.',
        'totalSupply': {'args': [], 'slots': []},
        'decimals': {'args': [], 'slots': []},
        'balanceOf': {'args': [2], 'slots': []},
        'allowance': {'args': [2, 3], 'slots': []},
        'approve': {'args': [2, 7], 'slots': []},
        'increaseApproval': {'args': [2, 1], 'slots': []},
        'decreaseApproval': {
            'decreaseApproval_p2': {'args': [2, 1], 'slots': []},
            'decreaseApproval_p4': {'args': [2, 1],
                                    'slots': [['mapSlot 2 (mapSlot Witness.CALLER1W 2)', 5]]}},
        'transfer': {'args': [2, 1], 'slots': [['mapSlot Witness.CALLER1W 1', 5]]},
        'transferFrom': {'args': [2, 3, 1],
                         'slots': [['mapSlot 2 1', 5],
                                   ['mapSlot Witness.CALLER1W (mapSlot 2 2)', 5]]},
    },
    'token_generators': ['scripts/gen_value.py'],
    'supply': {
        'comment': 'checked04: the SafeMath checks of Solidity 0.4 with the optimizer on '
                   '(sub: ISZERO (GT v a); add: ISZERO (LT (ADD v b) b)); the invariant has no '
                   'total supply slot (the total is a constant of the code).',
        'checked04': True,
        'what': 'the sum of all balances is the constant `10^27` that `totalSupply()` returns',
        'what_kept': 'if the sum of all balances was `10^27` before, it is after.',
        'unfold': 'Inv',
        'rules': 'Supply.sumBal_read, S_bal hsep, S_allow hsep, storageAt_readSlot',
        'ro': 'inv_of_ro',
        'dispatch': "  obtain ⟨_, i, hi⟩ := ends_ok_dispatch hfork hsize' start hrun hok\n",
    },
    'events': {'TRANSFER': 'Transfer(address,address,uint256)',
               'APPROVAL': 'Approval(address,address,uint256)',
               'TRANSFER_DATA': 'Transfer(address,address,uint256,bytes)'},
}
more = os.path.join(HERE, 'mk_config_more.py')
if os.path.exists(more):
    exec(open(more).read())
json.dump(cfg, open(os.path.join(HERE, '..', 'config', 'link.json'), 'w'), indent=1)
print('config/link.json written')

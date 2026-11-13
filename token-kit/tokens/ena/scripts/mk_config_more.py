# more of the configuration (run by mk_config.py): the two tails of permit after the STATICCALL
REST = [1, 0, 0, 0, 'sigS', 'sigR', 'sigV', 'dg', 5793, 0, 0, 0, 'sigS', 'sigR', 'sigV', 'dg',
        2684, 0, 'dg', 'sh', 'sigS', 'sigR', 'sigV', 'deadline', 'value', 'spender', 'owner',
        626, 'sel']
cfg['segments'] = [
    {'name': 'permitTailC', 'pc': 6113, 'stack': [1, 512] + REST,
     'raw_mem': {'size': 512, 'fp': 384, 'words': {'352': 'rec'}}, 'post_def': True},
    {'name': 'permitTailR', 'pc': 6113, 'stack': [1, 704] + REST,
     'raw_mem': {'size': 704, 'fp': 576, 'words': {'544': 'rec'}}, 'post_def': True},
]

# the supply invariant (scripts/gen_supply.py of this folder): checked08 with the facts of the
# `unchecked` blocks of OpenZeppelin 4.9 (balance of the receiver, total supply on a burn)
cfg['supply'] = {
    'comment': 'checked08 + unchecked: Solidity 0.8.20 with the optimizer on and OpenZeppelin '
               '4.9 (unchecked balance of the receiver and unchecked total supply on a burn: '
               'the proof uses the invariant itself there, lemmas of Ena/SupplyLib.lean); '
               'caller_key raw: the caller is a key of callKeys with no mask; norm: every key '
               'to one form; disch: the side goals of the rules of Sep.lean.',
    'checked08': True,
    'never_ok': True,
    'unchecked': {'balances': 2, 'totalSupply': 4},
    'caller_key': 'raw',
    'what': 'the sum of all balances is `_totalSupply`',
    'norm': "and_mask_comm, mask_idem, mask_toU256', storageAt_readSlot",
    'disch': 'slot_side',
    'rules': 'Supply.D_read, D_bal hsep, D_tot hsep, D_allow hsep, D_nonce hsep, D_owner hsep, '
             'D_pending hsep, D_lastMint hsep, storageAt_readSlot',
}
cfg['generators'] = ['code', 'dispatch', 'paths', 'loops', 'supply']
# the readable corollaries and the sanity witnesses
exec(open(os.path.join(HERE, 'mk_config_readable.py')).read())

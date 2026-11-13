# Run by mk_config.py (exec, with the dict `cfg` in scope): the supply invariant, the readable
# corollaries, the witnesses and the axioms test of WBTC.
cfg['generators'] = ['code', 'dispatch', 'paths', 'loops', 'supply']
cfg['supply'] = {
    'comment': 'checked04: the SafeMath checks of Solidity 0.4 with the optimizer on; '
               'caller_key raw: the caller is a key of callKeys with no mask; never_ok: '
               'renounceOwnership fails on every path.',
    'checked04': True,
    'never_ok': True,
    'caller_key': 'raw',
    'what': 'the sum of all balances is `totalSupply_`',
    'what_kept': 'if the sum of all balances was `totalSupply_` before, it is after.',
    'norm': 'and_mask_comm, mask_idem, mask_toU256\', storageAt_readSlot',
    'disch': 'slot_side',
    'rules': 'Supply.D_read, D_bal hsep, D_tot hsep, D_allow hsep, D_owner hsep, '
             'D_pending hsep, storageAt_readSlot',
    'dispatch': '  obtain ⟨_, i, hi⟩ := ends_ok_dispatch hfork hsize\' start hrun hok\n',
}

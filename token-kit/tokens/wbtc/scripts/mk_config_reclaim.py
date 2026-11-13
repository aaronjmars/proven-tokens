# Run by mk_config.py (exec, with the dict `cfg` in scope): the cut of reclaimToken(address)
# around its two outside calls. The path generator has no rule for EXTCODESIZE, GAS, CALL and
# RETURNDATASIZE, so the function is cut there; the opcodes in between are generated segments
# and the glue is hand-written (WbtcVerify/Wbtc/Reclaim/*.lean).
#   1521 EXTCODESIZE, 1535 GAS, 1536 CALL (balanceOf), 1537..1561 by hand (the return data is
#   read at 1561), 3196 EXTCODESIZE, 3210 GAS, 3211 CALL (transfer), 3212..3236 by hand.
MASK_T = 't'
cfg['stops'] = [1521, 1535, 3196, 3210]
cfg['segments'] = [
    # after EXTCODESIZE of the token, before the first call: REVERT when it has no code
    {'name': 'reclaimCodeA', 'pc': 1522,
     'stack': ['cs', 't2', 0, 128, 36, 128, 32, 164, 0x70a08231, 't2', 0, 't', 570, 'sel'],
     'raw_mem': {'size': 192, 'fp': 128, 'words': {}}, 'post_def': True},
    # after RETURNDATASIZE of the first call: the size check, the balance word, the second
    # read of the owner, the call data of transfer(owner, balance), up to EXTCODESIZE
    {'name': 'reclaimMid', 'pc': 1562,
     'stack': ['n', 128, 0, 't', 570, 'sel'],
     'raw_mem': {'size': 192, 'fp': 128, 'words': {'128': 'bal'}}, 'post_def': True},
    # after the second EXTCODESIZE, before the second call
    {'name': 'reclaimCodeB', 'pc': 3197,
     'stack': ['cs', 't3', 0, 128, 68, 128, 32, 196, 0xa9059cbb, 't3', 'bal', 'owner', 't2',
               1617, 'bal', 't', 570, 'sel'],
     'raw_mem': {'size': 224, 'fp': 128, 'words': {}}, 'post_def': True},
    # after RETURNDATASIZE of the second call: the size check, the returned word, STOP
    {'name': 'reclaimEnd', 'pc': 3237,
     'stack': ['n', 128, 'bal', 'owner', 't2', 1617, 'bal', 't', 570, 'sel'],
     'raw_mem': {'size': 224, 'fp': 128, 'words': {'128': 'ret'}}, 'post_def': True},
]

# Run by mk_config.py (exec, with the dict `cfg` in scope): the readable corollaries of WBTC
# (scripts/gen_readable.py writes WbtcVerify/Wbtc/Readable.lean from these descriptions) and the
# witnesses of its success paths (scripts/gen_sanity.py writes WbtcVerify/Wbtc/Sanity/Zero.lean).
# reclaimToken(address) is not here: it makes two outside calls and has its own files.
_BAL = 'balance message state'
_BAL_END = 'balance message s.state'
_ALLOW = 'allowance message state'
_ALLOW_END = 'allowance message s.state'
_TOT = 'totalSupply message state'
_TOT_END = 'totalSupply message s.state'
_SA = 'storageAt state message.currentTarget'
_SA_END = 'storageAt s.state message.currentTarget'
_SAME = '∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
_KEEP = 'storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
_NOLOG = 's.substate.logs = substate.logs'
_WRITE = ['message.value = 0', 'message.isStatic = false',
          'hasAccount state message.currentTarget']
_OWNER = 'sender message = ownerOf message state'
_UNPAUSED = 'pausedOf message state = 0'
_P168 = '(374144419156711147060143317175368453031918731001856 : U256)'
_P176 = '(95780971304118053647396689196894323976171195136475136 : U256)'
# all bits but byte 22 (`paused`), all bits but 8..167 (`owner`), all bits but the low 160
_K176 = '(115792089237316195423546560861005357749589898509895355986843660353153328480255 : U256)'
_KO = '(115792089237316195423570984634543488696558837605497246864089130975994398638335 : U256)'
_HIGH = '(115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256)'
_NOSIZE = ('The code has no check of the size of the call data: bytes of an argument past the '
           'end of the call data read as zero.')
_FLAGS_KEPT = ['ownerOf message s.state = ownerOf message state',
               'mintingFinishedOf message s.state = mintingFinishedOf message state',
               'decimalsOf message s.state = decimalsOf message state']

cfg['readable_opts'] = {
    'comment': 'facts checked04: the condition shapes of Solidity 0.4 with the optimizer on '
               '(gen_readable.facts04; lemmas of WbtcVerify/Wbtc/ReadableLib.lean); caller_key '
               'raw: the caller is a key with no mask and `sender` is its word; close: the '
               'closing tactic; several_paths same_claims: every success path proves the same '
               'claims (decreaseApproval has two); simp: the mask on the right of AND, the mask '
               'of the word of an address, the fields of the packed slot 5 after a write, the '
               'logs with one and two topics; header: the fields of slots 5 and 6.',
    'facts': 'checked04',
    'caller_key': 'raw',
    'close': 'readable_close08',
    'several_paths': 'same_claims',
    'imports': ['TokenKit.Evm.ReadableOpt', 'TokenKit.Evm.Opt06', 'TokenKit.Evm.Bits08',
                'WbtcVerify.Wbtc.ReadableLib'],
    'simp': ['and_mask_comm', "mask_toU256'", 'and_255_comm', 'and_255_idem',
             'slot_5_6', 'slot_6_5',
             'paused_pause', 'owner_pause', 'minting_pause', 'decimals_pause',
             'paused_unpause', 'owner_unpause', 'minting_unpause', 'decimals_unpause',
             'owner_claim', 'paused_claim', 'minting_claim', 'decimals_claim',
             'mask_and_high', 'mask_or_high',
             'logs_logSub1', 'Readable.logs_logSub2', 'log1', 'Readable.log2'],
    'unfold': ['ownerOf', 'pausedOf', 'mintingFinishedOf', 'decimalsOf', 'pendingOwnerOf'],
    'header': [
        '/-- `owner` of the called contract in the state `S`: bits 8 to 167 of slot 5. -/\n'
        'abbrev ownerOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd MASK (div (storageAt S m.currentTarget 5) (256 : U256))',
        '/-- The byte of `paused` of the called contract in the state `S` (byte 22 of slot 5; '
        'not 0:\npaused). -/\n'
        'abbrev pausedOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd (255 : U256) (div (storageAt S m.currentTarget 5)\n    ' + _P176 + ')',
        '/-- The byte of `mintingFinished` of the called contract in the state `S` (byte 21 of '
        'slot 5;\nnot 0: minting is finished). -/\n'
        'abbrev mintingFinishedOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd (255 : U256) (div (storageAt S m.currentTarget 5)\n    ' + _P168 + ')',
        '/-- `decimals` of the called contract in the state `S`: byte 0 of slot 5. -/\n'
        'abbrev decimalsOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd (255 : U256) (storageAt S m.currentTarget 5)',
        '/-- `pendingOwner` of the called contract in the state `S`: the low 160 bits of slot 6. '
        '-/\n'
        'abbrev pendingOwnerOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd MASK (storageAt S m.currentTarget 6)'],
    'sep_doc': 'A theorem whose\nfunction writes two or more mapping or supply slots (transfer, '
               'transferFrom, mint, burn) takes\n`Sep (callKeys message)` (the hypothesis on '
               'keccak of Sep.lean, not proved): without it two of the\nslots could be the same '
               'slot. The other theorems take no hypothesis on keccak.',
    'doc': [
        'WBTC (Solidity 0.4.24) has no check of the size of the call data: bytes of an argument '
        'past the\nend of the call data read as zero, so no theorem here has a claim on '
        '`message.data.size`.\nSlot 5 packs four fields: `decimalsOf` (byte 0), `ownerOf` (bits 8 '
        'to 167), `mintingFinishedOf`\n(byte 21) and `pausedOf` (byte 22); `pendingOwnerOf` is the '
        'low 160 bits of slot 6. A theorem of\na function that writes slot 5 or slot 6 gives the '
        'word written and each field after the write.\n"Every other slot keeps its word" is said '
        'for every slot number `k` other than the slots named;\nthat a named mapping slot is not '
        'slot 5 or 6 is a fact about keccak and is not claimed here.',
        'What the bytes do (see also Roles.lean): `mint` and `burn` are for the owner only and '
        'are NOT\nblocked by the pause; `mint` needs `mintingFinished` to be 0 and takes any '
        'receiver, 0 included;\n`burn` burns tokens of the caller (the owner); `transfer`, '
        '`transferFrom`, `approve`,\n`increaseApproval` and `decreaseApproval` fail while paused; '
        '`finishMinting` writes nothing and\nreturns 0 (false); `transferOwnership` only writes '
        '`pendingOwner` (no log, any word, 0 included)\nand `claimOwnership`, from the pending '
        'owner, moves it into `owner`; `renounceOwnership` has no\nsuccessful run (it has no '
        'theorem here: see `renounceOwnership_fails` in Roles.lean).'],
}

cfg['readable'] = {
    'mintingFinished': {
        'doc': 'mintingFinished(). Success needs no value. Then: returns 1 when byte 21 of slot '
               '5 is not 0, else 0; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (isZero (isZero (mintingFinishedOf message state)))',
                    _SAME, _NOLOG],
    },
    'totalSupply': {
        'doc': 'totalSupply(). Success needs no value. Then: returns the word of slot 1 '
               '(`totalSupply_`); no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': [f's.output = wordBytes ({_TOT})', _SAME, _NOLOG],
    },
    'decimals': {
        'doc': 'decimals(). Success needs no value. Then: returns byte 0 of slot 5; no slot '
               'changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (decimalsOf message state)', _SAME, _NOLOG],
    },
    'paused': {
        'doc': 'paused(). Success needs no value. Then: returns 1 when byte 22 of slot 5 is not '
               '0, else 0; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (isZero (isZero (pausedOf message state)))',
                    _SAME, _NOLOG],
    },
    'owner': {
        'doc': 'owner(). Success needs no value. Then: returns the address in bits 8 to 167 of '
               'slot 5; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (ownerOf message state)', _SAME, _NOLOG],
    },
    'pendingOwner': {
        'doc': 'pendingOwner(). Success needs no value. Then: returns the address in the low 160 '
               'bits of slot 6; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (pendingOwnerOf message state)', _SAME, _NOLOG],
    },
    'balanceOf': {
        'doc': 'balanceOf(owner). Success needs no value. Then: returns `balances[owner]` (the '
               'argument masked to 160 bits); no slot changes; no log. ' + _NOSIZE,
        'let': {'owner': 'addrArg1 message'},
        'requires': ['message.value = 0'],
        'ensures': [f's.output = wordBytes ({_BAL} {{owner}})', _SAME, _NOLOG],
    },
    'allowance': {
        'doc': 'allowance(owner, spender). Success needs no value. Then: returns '
               '`allowed[owner][spender]` (the arguments masked to 160 bits); no slot changes; '
               'no log. ' + _NOSIZE,
        'let': {'owner': 'addrArg1 message', 'spender': 'addrArg2 message'},
        'requires': ['message.value = 0'],
        'ensures': [f's.output = wordBytes ({_ALLOW} {{owner}} {{spender}})', _SAME, _NOLOG],
    },
    'transfer': {
        'doc': 'transfer(to, value) with `from` the caller. Success needs: no value, a frame that '
               'may write, an account of the contract, the token not paused, '
               '`value <= balances[from]`, `to` not 0, and (when `to` is not `from`) no overflow '
               'of `balances[to]`. Then: returns 1; `balances[from]` is the old word minus '
               '`value` and `balances[to]` the old word plus `value` (when `to = from` the '
               'balance is unchanged); every other slot keeps its word; exactly one log, '
               'Transfer(from, to, value). `to` may be the contract itself. ' + _NOSIZE,
        'let': {'from': 'sender message', 'to': 'addrArg1 message', 'amount': 'arg2 message'},
        'cases': ['{to} = {from}'],
        'requires': _WRITE + [
            _UNPAUSED,
            f'{{amount}}.toNat ≤ ({_BAL} {{from}}).toNat',
            '{to} ≠ 0',
            f'{{to}} ≠ {{from}} → ({_BAL} {{to}}).toNat + {{amount}}.toNat < 2 ^ 256'],
        'ensures': [
            's.output = wordBytes 1',
            f'{{to}} ≠ {{from}} → ({_BAL_END} {{from}}).toNat = ({_BAL} {{from}}).toNat - '
            f'{{amount}}.toNat ∧ ({_BAL_END} {{to}}).toNat = ({_BAL} {{to}}).toNat + '
            '{amount}.toNat',
            f'{{to}} = {{from}} → {_BAL_END} {{from}} = {_BAL} {{from}}',
            '∀ k, k ≠ mapSlot {from} 0 → k ≠ mapSlot {to} 0 → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget TRANSFER '
            '{from} {to} (wordBytes {amount}))'],
    },
    'approve': {
        'doc': 'approve(spender, value) from the caller `owner`. Success needs: no value, a frame '
               'that may write, an account of the contract, the token not paused. Then: returns '
               '1; `allowed[owner][spender]` is `value` (whatever it was: no check of the old '
               'allowance); every other slot keeps its word; exactly one log, Approval(owner, '
               'spender, value). `spender` may be 0. No hypothesis on keccak is needed. '
               + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'value': 'arg2 message'},
        'sep': False,
        'requires': _WRITE + [_UNPAUSED],
        'ensures': [
            's.output = wordBytes 1',
            f'{_ALLOW_END} {{owner}} {{spender}} = {{value}}',
            '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 2) → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget APPROVAL '
            '{owner} {spender} (wordBytes {value}))'],
    },
    'transferFrom': {
        'doc': 'transferFrom(from, to, value) by the caller `spender`. Success needs: no value, a '
               'frame that may write, an account of the contract, the token not paused, '
               '`value <= balances[from]`, `value <= allowed[from][spender]`, `to` not 0, and '
               '(when `to` is not `from`) no overflow of `balances[to]`. Then: returns 1; '
               '`balances[from]` is the old word minus `value` and `balances[to]` the old word '
               'plus `value` (when `to = from` the balance is unchanged); '
               '`allowed[from][spender]` is the old word minus `value` (whoever `spender` is: '
               '`from`, `to` or another address; an allowance of `2^256 - 1` is lowered too); '
               'every other slot keeps its word; exactly one log, Transfer(from, to, value) (no '
               'Approval log). ' + _NOSIZE,
        'let': {'from': 'addrArg1 message', 'to': 'addrArg2 message', 'amount': 'arg3 message',
                'spender': 'sender message'},
        'cases': ['{to} = {from}'],
        'requires': _WRITE + [
            _UNPAUSED,
            f'{{amount}}.toNat ≤ ({_BAL} {{from}}).toNat',
            f'{{amount}}.toNat ≤ ({_ALLOW} {{from}} {{spender}}).toNat',
            '{to} ≠ 0',
            f'{{to}} ≠ {{from}} → ({_BAL} {{to}}).toNat + {{amount}}.toNat < 2 ^ 256'],
        'ensures': [
            's.output = wordBytes 1',
            f'{{to}} ≠ {{from}} → ({_BAL_END} {{from}}).toNat = ({_BAL} {{from}}).toNat - '
            f'{{amount}}.toNat ∧ ({_BAL_END} {{to}}).toNat = ({_BAL} {{to}}).toNat + '
            '{amount}.toNat',
            f'{{to}} = {{from}} → {_BAL_END} {{from}} = {_BAL} {{from}}',
            f'({_ALLOW_END} {{from}} {{spender}}).toNat = ({_ALLOW} {{from}} {{spender}}).toNat - '
            '{amount}.toNat',
            '∀ k, k ≠ mapSlot {from} 0 → k ≠ mapSlot {to} 0 → '
            'k ≠ mapSlot {spender} (mapSlot {from} 2) → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget TRANSFER '
            '{from} {to} (wordBytes {amount}))'],
    },
    'increaseApproval': {
        'doc': 'increaseApproval(spender, added) from the caller `owner`. Success needs: no '
               'value, a frame that may write, an account of the contract, the token not paused, '
               'and no overflow of `allowed[owner][spender]`. Then: returns 1; '
               '`allowed[owner][spender]` is the old word plus `added`; every other slot keeps '
               'its word; exactly one log, Approval(owner, spender, new allowance). No '
               'hypothesis on keccak is needed. ' + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'added': 'arg2 message'},
        'sep': False,
        'requires': _WRITE + [
            _UNPAUSED,
            f'({_ALLOW} {{owner}} {{spender}}).toNat + {{added}}.toNat < 2 ^ 256'],
        'ensures': [
            's.output = wordBytes 1',
            f'({_ALLOW_END} {{owner}} {{spender}}).toNat = ({_ALLOW} {{owner}} {{spender}}).toNat '
            '+ {added}.toNat',
            '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 2) → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget APPROVAL '
            f'{{owner}} {{spender}} (wordBytes (add {{added}} ({_ALLOW} {{owner}} {{spender}}))))'],
    },
    'decreaseApproval': {
        'doc': 'decreaseApproval(spender, subtracted) from the caller `owner`. Success needs: no '
               'value, a frame that may write, an account of the contract, the token not paused. '
               'Then: returns 1; `allowed[owner][spender]` is 0 when `subtracted` is at least '
               'the old word, else the old word minus `subtracted`; every other slot keeps its '
               'word; exactly one log, Approval(owner, spender, new allowance). No hypothesis on '
               'keccak is needed. ' + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'subtracted': 'arg2 message',
                'old': _ALLOW + ' (sender message) (addrArg1 message)'},
        'sep': False,
        'requires': _WRITE + [_UNPAUSED],
        'ensures': [
            's.output = wordBytes 1',
            f'{{old}}.toNat ≤ {{subtracted}}.toNat → {_ALLOW_END} {{owner}} {{spender}} = 0',
            f'{{subtracted}}.toNat < {{old}}.toNat → ({_ALLOW_END} {{owner}} {{spender}}).toNat = '
            '{old}.toNat - {subtracted}.toNat',
            '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 2) → ' + _KEEP,
            '{old}.toNat ≤ {subtracted}.toNat → s.substate.logs = substate.logs.push '
            '(Readable.log3 message.currentTarget APPROVAL {owner} {spender} '
            '(wordBytes (0 : U256)))',
            '{subtracted}.toNat < {old}.toNat → s.substate.logs = substate.logs.push '
            '(Readable.log3 message.currentTarget APPROVAL {owner} {spender} '
            '(wordBytes (sub {old} {subtracted})))'],
    },
    'mint': {
        'doc': 'mint(to, amount) by the owner. Success needs: no value, a frame that may write, '
               'an account of the contract, the caller is the owner, `mintingFinished` is 0, no '
               'overflow of `totalSupply_` and no overflow of `balances[to]`. The pause is NOT '
               'checked and `to` may be 0. Then: returns 1; `totalSupply_` and `balances[to]` '
               'are each the old word plus `amount`; every other slot keeps its word; exactly '
               'two logs, Mint(to, amount) then Transfer(0, to, amount). ' + _NOSIZE,
        'let': {'to': 'addrArg1 message', 'amount': 'arg2 message'},
        'requires': _WRITE + [
            _OWNER,
            'mintingFinishedOf message state = 0',
            f'({_TOT}).toNat + {{amount}}.toNat < 2 ^ 256',
            f'({_BAL} {{to}}).toNat + {{amount}}.toNat < 2 ^ 256'],
        'ensures': [
            's.output = wordBytes 1',
            f'({_TOT_END}).toNat = ({_TOT}).toNat + {{amount}}.toNat',
            f'({_BAL_END} {{to}}).toNat = ({_BAL} {{to}}).toNat + {{amount}}.toNat',
            '∀ k, k ≠ 1 → k ≠ mapSlot {to} 0 → ' + _KEEP,
            's.substate.logs = (substate.logs.push (Readable.log2 message.currentTarget MINT '
            '{to} (wordBytes {amount}))).push (Readable.log3 message.currentTarget TRANSFER 0 '
            '{to} (wordBytes {amount}))'],
    },
    'burn': {
        'doc': 'burn(value) by the owner `from` (the caller). Success needs: no value, a frame '
               'that may write, an account of the contract, the caller is the owner, '
               '`value <= balances[from]` and `value <= totalSupply_`. The pause is NOT checked. '
               'Then: returns nothing; `balances[from]` and `totalSupply_` are each the old word '
               'minus `value`; every other slot keeps its word; exactly two logs, Burn(from, '
               'value) then Transfer(from, 0, value). ' + _NOSIZE,
        'let': {'from': 'sender message', 'amount': 'arg1 message'},
        'requires': _WRITE + [
            _OWNER,
            f'{{amount}}.toNat ≤ ({_BAL} {{from}}).toNat',
            f'{{amount}}.toNat ≤ ({_TOT}).toNat'],
        'ensures': [
            's.output = ByteArray.empty',
            f'({_BAL_END} {{from}}).toNat = ({_BAL} {{from}}).toNat - {{amount}}.toNat',
            f'({_TOT_END}).toNat = ({_TOT}).toNat - {{amount}}.toNat',
            '∀ k, k ≠ mapSlot {from} 0 → k ≠ 1 → ' + _KEEP,
            's.substate.logs = (substate.logs.push (Readable.log2 message.currentTarget BURN '
            '{from} (wordBytes {amount}))).push (Readable.log3 message.currentTarget TRANSFER '
            '{from} 0 (wordBytes {amount}))'],
    },
    'pause': {
        'doc': 'pause() by the owner. Success needs: no value, a frame that may write, an '
               'account of the contract, the caller is the owner, and the token is not paused. '
               'Then: returns nothing; byte 22 of slot 5 is 1 and the other bytes of slot 5 keep '
               'their value (owner, mintingFinished, decimals); every other slot keeps its word; '
               'exactly one log, Pause().',
        'sep': False,
        'requires': _WRITE + [_OWNER, _UNPAUSED],
        'ensures': [
            's.output = ByteArray.empty',
            'pausedOf message s.state = 1'] + _FLAGS_KEPT + [
            f'{_SA_END} 5 = bitwiseOr {_P176} (bitwiseAnd {_K176} ({_SA} 5))',
            '∀ k, k ≠ 5 → ' + _KEEP,
            's.substate.logs = substate.logs.push (log1 message.currentTarget PAUSE '
            'ByteArray.empty)'],
    },
    'unpause': {
        'doc': 'unpause() by the owner. Success needs: no value, a frame that may write, an '
               'account of the contract, the caller is the owner, and the token is paused. '
               'Then: returns nothing; byte 22 of slot 5 is 0 and the other bytes of slot 5 keep '
               'their value (owner, mintingFinished, decimals); every other slot keeps its word; '
               'exactly one log, Unpause().',
        'sep': False,
        'requires': _WRITE + [_OWNER, 'pausedOf message state ≠ 0'],
        'ensures': [
            's.output = ByteArray.empty',
            'pausedOf message s.state = 0'] + _FLAGS_KEPT + [
            f'{_SA_END} 5 = bitwiseAnd {_K176} ({_SA} 5)',
            '∀ k, k ≠ 5 → ' + _KEEP,
            's.substate.logs = substate.logs.push (log1 message.currentTarget UNPAUSE '
            'ByteArray.empty)'],
    },
    'finishMinting': {
        'doc': 'finishMinting() by the owner. Success needs: no value and the caller is the '
               'owner. Then: returns 0 (false); no slot changes (`mintingFinished` is NOT set); '
               'no log. It writes nothing, so it also runs in a frame that may not write.',
        'requires': ['message.value = 0', _OWNER],
        'ensures': ['s.output = wordBytes (0 : U256)', _SAME, _NOLOG],
    },
    'transferOwnership': {
        'doc': 'transferOwnership(newOwner) by the owner. Success needs: no value, a frame that '
               'may write, an account of the contract, and the caller is the owner. Then: '
               'returns nothing; the low 160 bits of slot 6 (`pendingOwner`) are `newOwner` (the '
               'argument masked to 160 bits; 0 and the owner itself are accepted) and its high '
               'bits keep their value; slot 5 keeps its word, so the owner does NOT change; '
               'every other slot keeps its word; no log. ' + _NOSIZE,
        'let': {'new': 'addrArg1 message'},
        'sep': False,
        'requires': _WRITE + [_OWNER],
        'ensures': [
            's.output = ByteArray.empty',
            'pendingOwnerOf message s.state = {new}',
            'ownerOf message s.state = ownerOf message state',
            f'{_SA_END} 6 = bitwiseOr {{new}} (bitwiseAnd {_HIGH} ({_SA} 6))',
            '∀ k, k ≠ 6 → ' + _KEEP,
            _NOLOG],
    },
    'claimOwnership': {
        'doc': 'claimOwnership() by the pending owner. Success needs: no value, a frame that may '
               'write, an account of the contract, and the caller is `pendingOwner` (the low 160 '
               'bits of slot 6). Then: returns nothing; `owner` is the old `pendingOwner` (the '
               'caller) and the other bytes of slot 5 keep their value (paused, '
               'mintingFinished, decimals); `pendingOwner` is 0; every other slot keeps its '
               'word; exactly one log, OwnershipTransferred(old owner, new owner).',
        'sep': False,
        'requires': _WRITE + ['sender message = pendingOwnerOf message state'],
        'ensures': [
            's.output = ByteArray.empty',
            'ownerOf message s.state = pendingOwnerOf message state',
            'pendingOwnerOf message s.state = 0',
            'pausedOf message s.state = pausedOf message state',
            'mintingFinishedOf message s.state = mintingFinishedOf message state',
            'decimalsOf message s.state = decimalsOf message state',
            f'{_SA_END} 5 = bitwiseOr (mul (pendingOwnerOf message state) (256 : U256)) '
            f'(bitwiseAnd {_KO} ({_SA} 5))',
            f'{_SA_END} 6 = bitwiseAnd {_HIGH} ({_SA} 6)',
            '∀ k, k ≠ 5 → k ≠ 6 → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget '
            'OWNERSHIP_TRANSFERRED (ownerOf message state) (pendingOwnerOf message state) '
            'ByteArray.empty)'],
    },
}

if 'readable' not in cfg['generators']:
    cfg['generators'].append('readable')

# The witnesses (scripts/gen_sanity.py, form eval). Slot 5 holds the owner in bits 8 to 167:
# `_OWN5` is the word with the caller `Witness.CALLER1` as owner and 8 decimals; `_OWN5P` is
# the same word with the byte of `paused` set.
_C1 = 'Witness.CALLER1W'
_OWN5 = '(0x' + '01' * 20 + '08 : U256)'
_OWN5P = '(0x0100' + '01' * 20 + '08 : U256)'
cfg['sanity'] = {
    'comment': 'The witness call of each success path (scripts/gen_sanity.py, form eval): the '
               'argument words and the words of the slots of the state. The caller is '
               'Witness.CALLER1 (word Witness.CALLER1W); amounts are 1 and the balances, '
               'allowances and total supply used are 5. A key `<path>@<name>` is one more '
               'witness `<fn>_<name>_runs` of the same path on another state; a path of kind '
               'revert named here gets a witness `<path>_reverts` (the run ends with an error).',
    'imports': ['TokenKit.Evm.WitnessOpt'],
    'doc': '`<path>_runs` (or `<fn>_runs` for a function with one success path): in the state '
           'with one\naccount at the contract `C` that holds the stated words at the stated '
           'slots (every other slot\n0), the stated call from the caller `Witness.CALLER1` meets '
           'every hypothesis of the success path\ntheorem; so the loop of the interpreter runs it '
           'from pc 0 to the end with no error, for every\nmessage runner and every gas bound '
           'that holds its gas, with the stated output and end state.\nEvery condition is '
           'computed by the kernel, the keccak of each mapping slot included: no\nhypothesis '
           'about keccak is used.\n\nThe word `0x0101..0108` of slot 5 is: owner '
           '`Witness.CALLER1` (bits 8 to 167), `mintingFinished`\n0, `paused` 0, decimals 8; '
           '`0x01000101..0108` is the same with `paused` 1.\n`mint_paused_runs`, `burn_paused_runs`: a mint and a burn '
           'succeed while the token is paused. `<path>_reverts`: the stated call\nmeets every '
           'hypothesis of a REVERT path theorem, so it ends with an error: a transfer, a transferFrom and an approve while the\ntoken is '
           'paused, a mint by a caller that is not the owner, a claimOwnership by a caller that '
           'is\nnot the pending owner, and renounceOwnership by the owner (its last path, which '
           'returns the\nreason string).\nreclaimToken(address) is not here: its witnesses need '
           'a second contract (the witness stream).',
    'mintingFinished': {'args': [], 'slots': []},
    'totalSupply': {'args': [], 'slots': [[1, 5]]},
    'decimals': {'args': [], 'slots': [[5, _OWN5]]},
    'paused': {'args': [], 'slots': [[5, _OWN5P]]},
    'owner': {'args': [], 'slots': [[5, _OWN5]]},
    'pendingOwner': {'args': [], 'slots': [[6, 2]]},
    'balanceOf': {'args': [2], 'slots': [['mapSlot 2 0', 5]]},
    'allowance': {'args': [2, 3], 'slots': [['mapSlot 3 (mapSlot 2 2)', 5]]},
    'approve': {
        'approve_p3': {'args': [2, 7], 'slots': []},
        'approve_p1': {'args': [2, 7], 'slots': [[5, _OWN5P]]}},
    'increaseApproval': {'args': [2, 1], 'slots': []},
    'decreaseApproval': {
        'decreaseApproval_p3': {'args': [2, 1], 'slots': []},
        'decreaseApproval_p6': {'args': [2, 1],
                                'slots': [[f'mapSlot 2 (mapSlot {_C1} 2)', 5]]}},
    'transfer': {
        'transfer_p6': {'args': [2, 1], 'slots': [[f'mapSlot {_C1} 0', 5]]},
        'transfer_p1': {'args': [2, 1], 'slots': [[5, _OWN5P], [f'mapSlot {_C1} 0', 5]]}},
    'transferFrom': {
        'transferFrom_p8': {'args': [2, 3, 1],
                            'slots': [['mapSlot 2 0', 5],
                                      [f'mapSlot {_C1} (mapSlot 2 2)', 5]]},
        'transferFrom_p1': {'args': [2, 3, 1],
                            'slots': [[5, _OWN5P], ['mapSlot 2 0', 5],
                                      [f'mapSlot {_C1} (mapSlot 2 2)', 5]]}},
    'mint': {
        'mint_p6': {'args': [2, 1], 'slots': [[5, _OWN5], [1, 5]]},
        'mint_p6@paused': {'args': [2, 1], 'slots': [[5, _OWN5P], [1, 5]]},
        'mint_p1': {'args': [2, 1], 'slots': [[1, 5]]}},
    'burn': {
        'burn_p5': {'args': [1], 'slots': [[5, _OWN5], [1, 5], [f'mapSlot {_C1} 0', 5]]},
        'burn_p5@paused': {'args': [1],
                           'slots': [[5, _OWN5P], [1, 5], [f'mapSlot {_C1} 0', 5]]}},
    'pause': {'args': [], 'slots': [[5, _OWN5]]},
    'unpause': {'args': [], 'slots': [[5, _OWN5P]]},
    'finishMinting': {'args': [], 'slots': [[5, _OWN5]]},
    'transferOwnership': {'args': [2], 'slots': [[5, _OWN5]]},
    'claimOwnership': {
        'claimOwnership_p4': {'args': [], 'slots': [[5, '(0x0208 : U256)'], [6, _C1]]},
        'claimOwnership_p1': {'args': [], 'slots': [[5, _OWN5], [6, 2]]}},
    'renounceOwnership': {
        'renounceOwnership_p2': {'args': [], 'slots': [[5, _OWN5]]}},
}
if 'sanity' not in cfg['generators']:
    cfg['generators'].append('sanity')

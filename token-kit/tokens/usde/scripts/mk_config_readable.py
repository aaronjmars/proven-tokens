# The readable corollaries and the sanity witnesses of USDe (run by mk_config.py after
# mk_config_more.py; `cfg` is the configuration being built).
MAXW = '(115792089237316195423570985008687907853269984665640564039457584007913129639935 : U256)'
HIGH = '(115792089237316195423570985007226406215939081747436879206741300988257197096960 : U256)'
C = 'message.currentTarget'
V0 = 'message.value = 0'
ST = 'message.isStatic = false'
ACC = 'hasAccount state message.currentTarget'
SAME = '∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
NOLOG = 's.substate.logs = substate.logs'


def keep(*slots):
    return ('∀ k, ' + ''.join(f'k ≠ {x} → ' for x in slots)
            + 'storageAt s.state message.currentTarget k = storageAt state message.currentTarget k')


def size(n):
    return f'4 + {n} ≤ message.data.size'


AL = '(allowance message state {from} {spender})'
AL1 = '(allowance message s.state {from} {spender})'
TR = 'log3 message.currentTarget TRANSFER'
AP = 'log3 message.currentTarget APPROVAL'

R = {}
R['totalSupply'] = {
    'doc': 'totalSupply(). Success needs no value. Then: returns the word of slot 4; no slot '
           'changes; no log.',
    'requires': [V0],
    'ensures': ['s.output = wordBytes (totalSupply message state)', SAME, NOLOG]}
R['balanceOf'] = {
    'doc': 'balanceOf(a). Success needs no value, 36 bytes of call data and an argument word '
           'with no bit above the 160 low bits. Then: returns `_balances[a]`; no slot changes; '
           'no log.',
    'let': {'a': 'addrArg1 message'},
    'requires': [V0, size(32), 'arg1 message = {a}'],
    'ensures': ['s.output = wordBytes (balance message state {a})', SAME, NOLOG]}
R['allowance'] = {
    'doc': 'allowance(o, sp). Success needs no value, 68 bytes of call data and two argument '
           'words with no bit above the 160 low bits. Then: returns `_allowances[o][sp]`; no '
           'slot changes; no log.',
    'let': {'o': 'addrArg1 message', 'sp': 'addrArg2 message'},
    'requires': [V0, size(64), 'arg1 message = {o}', 'arg2 message = {sp}'],
    'ensures': ['s.output = wordBytes (allowance message state {o} {sp})', SAME, NOLOG]}
R['decimals'] = {
    'doc': 'decimals(). Success needs no value. Then: returns 18; no slot changes; no log.',
    'requires': [V0],
    'ensures': ['s.output = wordBytes 18', SAME, NOLOG]}
for fn, ab, slot in [('owner', 'ownerOf', 0), ('pendingOwner', 'pendingOwnerOf', 1),
                     ('minter', 'minterOf', 11)]:
    R[fn] = {
        'doc': f'{fn}(). Success needs no value. Then: returns the address in the low 160 bits '
               f'of slot {slot}; no slot changes; no log.',
        'requires': [V0],
        'ensures': [f's.output = wordBytes ({ab} message state)', SAME, NOLOG]}
R['nonces'] = {
    'doc': 'nonces(a). Success needs no value, 36 bytes of call data and an argument word with '
           'no bit above the 160 low bits. Then: returns `_nonces[a]`; no slot changes; no log.',
    'let': {'a': 'addrArg1 message'},
    'requires': [V0, size(32), 'arg1 message = {a}'],
    'ensures': ['s.output = wordBytes (nonceOf message state {a})', SAME, NOLOG]}
R['transfer'] = {
    'doc': 'transfer(to, amount) with `from` the caller. Success needs: no value, 68 bytes of '
           'call data, a clean address word, a frame that may write, `from` and `to` not 0, and '
           '`amount <= _balances[from]`. Then: returns 1; `_balances[from]` is the old word '
           'minus `amount`; `_balances[to]` is the old word plus `amount` as a 256-bit word '
           '(the bytecode does not check this addition: `transfer_no_wrap` shows that it does '
           'not wrap under the supply invariant); when `to = from` the balance is unchanged; '
           '`_totalSupply` and every other slot keep their word; exactly one log, '
           'Transfer(from, to, amount).',
    'let': {'from': 'callerW message', 'to': 'addrArg1 message', 'amount': 'arg2 message'},
    'cases': ['{to} = {from}'],
    'requires': [V0, size(64), 'arg1 message = {to}', ST, ACC, '{from} ≠ 0', '{to} ≠ 0',
                 '{amount}.toNat ≤ (balance message state {from}).toNat'],
    'ensures': ['s.output = wordBytes 1',
                '{to} ≠ {from} → (balance message s.state {from}).toNat = (balance message state {from}).toNat - {amount}.toNat',
                '{to} ≠ {from} → balance message s.state {to} = add {amount} (balance message state {to})',
                '{to} = {from} → balance message s.state {from} = balance message state {from}',
                'totalSupply message s.state = totalSupply message state',
                keep('mapSlot {from} 2', 'mapSlot {to} 2'),
                's.substate.logs = substate.logs.push (' + TR + ' {from} {to} (wordBytes {amount}))']}
R['approve'] = {
    'doc': 'approve(spender, value) from the caller. Success needs: no value, 68 bytes of call '
           'data, a clean address word, a frame that may write, the caller and `spender` not 0. '
           'Then: returns 1; `_allowances[caller][spender]` is `value`; `_totalSupply` and '
           'every other slot keep their word; exactly one log, Approval(caller, spender, value).',
    'let': {'owner': 'callerW message', 'spender': 'addrArg1 message', 'value': 'arg2 message'},
    'requires': [V0, size(64), 'arg1 message = {spender}', ST, ACC, '{owner} ≠ 0',
                 '{spender} ≠ 0'],
    'ensures': ['s.output = wordBytes 1',
                'allowance message s.state {owner} {spender} = {value}',
                'totalSupply message s.state = totalSupply message state',
                keep('mapSlot {spender} (mapSlot {owner} 3)'),
                's.substate.logs = substate.logs.push (' + AP + ' {owner} {spender} (wordBytes {value}))']}
R['transferFrom'] = {
    'doc': 'transferFrom(from, to, amount) with `spender` the caller. Success needs: no value, '
           '100 bytes of call data, two clean address words, a frame that may write, `from` '
           'and `to` not 0, `amount <= _balances[from]`, and when `_allowances[from][spender]` '
           'is not the largest word: `amount <= _allowances[from][spender]` and the caller is '
           'not 0. Then: returns 1; `_balances[from]` is the old word minus `amount`; '
           '`_balances[to]` is the old word plus `amount` as a 256-bit word (not checked by '
           'the bytecode: see `transfer_no_wrap`); when `to = from` the balance is unchanged; '
           'the allowance is the old word minus `amount` when it is not the largest word, else '
           'it is unchanged; `_totalSupply` and every other slot keep their word; the logs: '
           'Approval(from, spender, new allowance) when the allowance is not the largest word, '
           'then Transfer(from, to, amount).',
    'let': {'from': 'addrArg1 message', 'to': 'addrArg2 message', 'amount': 'arg3 message',
            'spender': 'callerW message'},
    'cases': ['{to} = {from}'],
    'requires': [V0, size(96), 'arg1 message = {from}', 'arg2 message = {to}', ST, ACC,
                 '{from} ≠ 0', '{to} ≠ 0',
                 AL + ' ≠ ' + MAXW + ' → {amount}.toNat ≤ ' + AL + '.toNat',
                 AL + ' ≠ ' + MAXW + ' → {spender} ≠ 0',
                 '{amount}.toNat ≤ (balance message state {from}).toNat'],
    'ensures': ['s.output = wordBytes 1',
                '{to} ≠ {from} → (balance message s.state {from}).toNat = (balance message state {from}).toNat - {amount}.toNat',
                '{to} ≠ {from} → balance message s.state {to} = add {amount} (balance message state {to})',
                '{to} = {from} → balance message s.state {from} = balance message state {from}',
                AL + ' ≠ ' + MAXW + ' → ' + AL1 + '.toNat = ' + AL + '.toNat - {amount}.toNat',
                AL + ' = ' + MAXW + ' → ' + AL1 + ' = ' + AL,
                'totalSupply message s.state = totalSupply message state',
                keep('mapSlot {from} 2', 'mapSlot {to} 2', 'mapSlot {spender} (mapSlot {from} 3)'),
                AL + ' ≠ ' + MAXW + ' → s.substate.logs = (substate.logs.push (' + AP
                + ' {from} {spender} (wordBytes (sub ' + AL + ' {amount})))).push (' + TR
                + ' {from} {to} (wordBytes {amount}))',
                AL + ' = ' + MAXW + ' → s.substate.logs = substate.logs.push (' + TR
                + ' {from} {to} (wordBytes {amount}))']}
OA = '(allowance message state {owner} {spender})'
R['increaseAllowance'] = {
    'doc': 'increaseAllowance(spender, added) from the caller. Success needs: no value, 68 '
           'bytes of call data, a clean address word, a frame that may write, the caller and '
           '`spender` not 0, and no overflow of the allowance. Then: returns 1; '
           '`_allowances[caller][spender]` is the old word plus `added`; `_totalSupply` and '
           'every other slot keep their word; exactly one log, Approval(caller, spender, new '
           'allowance).',
    'let': {'owner': 'callerW message', 'spender': 'addrArg1 message', 'added': 'arg2 message'},
    'requires': [V0, size(64), 'arg1 message = {spender}', ST, ACC, '{owner} ≠ 0',
                 '{spender} ≠ 0', OA + '.toNat + {added}.toNat < 2 ^ 256'],
    'ensures': ['s.output = wordBytes 1',
                '(allowance message s.state {owner} {spender}).toNat = ' + OA + '.toNat + {added}.toNat',
                'totalSupply message s.state = totalSupply message state',
                keep('mapSlot {spender} (mapSlot {owner} 3)'),
                's.substate.logs = substate.logs.push (' + AP
                + ' {owner} {spender} (wordBytes (add {added} ' + OA + ')))']}
R['decreaseAllowance'] = {
    'doc': 'decreaseAllowance(spender, subtracted) from the caller. Success needs: no value, 68 '
           'bytes of call data, a clean address word, a frame that may write, the caller and '
           '`spender` not 0, and `subtracted <= _allowances[caller][spender]`. Then: returns 1; '
           'the allowance is the old word minus `subtracted`; `_totalSupply` and every other '
           'slot keep their word; exactly one log, Approval(caller, spender, new allowance).',
    'let': {'owner': 'callerW message', 'spender': 'addrArg1 message',
            'subtracted': 'arg2 message'},
    'requires': [V0, size(64), 'arg1 message = {spender}', ST, ACC, '{owner} ≠ 0',
                 '{spender} ≠ 0', '{subtracted}.toNat ≤ ' + OA + '.toNat'],
    'ensures': ['s.output = wordBytes 1',
                '(allowance message s.state {owner} {spender}).toNat = ' + OA + '.toNat - {subtracted}.toNat',
                'totalSupply message s.state = totalSupply message state',
                keep('mapSlot {spender} (mapSlot {owner} 3)'),
                's.substate.logs = substate.logs.push (' + AP
                + ' {owner} {spender} (wordBytes (sub ' + OA + ' {subtracted})))']}
R['mint'] = {
    'doc': 'mint(to, amount). Success needs: no value, 68 bytes of call data, a clean address '
           'word, a frame that may write, the caller is the address `minter` of slot 11, `to` '
           'is not 0, and no overflow of `_totalSupply`. There is no other check: the minter '
           'mints any amount to any address but 0. Then: returns nothing; `_totalSupply` is '
           'the old word plus `amount`; `_balances[to]` is the old word plus `amount` as a '
           '256-bit word (not checked by the bytecode: `mint_no_wrap` shows that it does not '
           'wrap under the supply invariant); every other slot keeps its word; exactly one '
           'log, Transfer(0, to, amount).',
    'let': {'to': 'addrArg1 message', 'amount': 'arg2 message'},
    'requires': [V0, size(64), 'arg1 message = {to}', ST, ACC,
                 'callerW message = minterOf message state', '{to} ≠ 0',
                 '(totalSupply message state).toNat + {amount}.toNat < 2 ^ 256'],
    'ensures': ['s.output = ByteArray.empty',
                '(totalSupply message s.state).toNat = (totalSupply message state).toNat + {amount}.toNat',
                'balance message s.state {to} = add {amount} (balance message state {to})',
                keep('4', 'mapSlot {to} 2'),
                's.substate.logs = substate.logs.push (' + TR + ' 0 {to} (wordBytes {amount}))']}
R['burn'] = {
    'doc': 'burn(amount) by the caller. Success needs: no value, 36 bytes of call data, a frame '
           'that may write, the caller not 0, and `amount <= _balances[caller]`. Then: returns '
           'nothing; `_balances[caller]` is the old word minus `amount`; `_totalSupply` is the '
           'old word minus `amount` as a 256-bit word (not checked by the bytecode: '
           '`burn_no_wrap` shows that it does not wrap under the supply invariant); every '
           'other slot keeps its word; exactly one log, Transfer(caller, 0, amount).',
    'let': {'from': 'callerW message', 'amount': 'arg1 message'},
    'requires': [V0, size(32), ST, ACC, '{from} ≠ 0',
                 '{amount}.toNat ≤ (balance message state {from}).toNat'],
    'ensures': ['s.output = ByteArray.empty',
                '(balance message s.state {from}).toNat = (balance message state {from}).toNat - {amount}.toNat',
                'totalSupply message s.state = sub (totalSupply message state) {amount}',
                keep('mapSlot {from} 2', '4'),
                's.substate.logs = substate.logs.push (' + TR + ' {from} 0 (wordBytes {amount}))']}
R['burnFrom'] = {
    'doc': 'burnFrom(from, amount) with `spender` the caller. Success needs: no value, 68 bytes '
           'of call data, a clean address word, a frame that may write, `from` not 0, '
           '`amount <= _balances[from]`, and when `_allowances[from][spender]` is not the '
           'largest word: `amount <= _allowances[from][spender]` and the caller is not 0. '
           'Then: returns nothing; `_balances[from]` is the old word minus `amount`; '
           '`_totalSupply` is the old word minus `amount` as a 256-bit word (not checked by '
           'the bytecode: see `burn_no_wrap`); the allowance is the old word minus `amount` '
           'when it is not the largest word, else it is unchanged; every other slot keeps its '
           'word; the logs: Approval(from, spender, new allowance) when the allowance is not '
           'the largest word, then Transfer(from, 0, amount).',
    'let': {'from': 'addrArg1 message', 'amount': 'arg2 message', 'spender': 'callerW message'},
    'requires': [V0, size(64), 'arg1 message = {from}', ST, ACC, '{from} ≠ 0',
                 AL + ' ≠ ' + MAXW + ' → {amount}.toNat ≤ ' + AL + '.toNat',
                 AL + ' ≠ ' + MAXW + ' → {spender} ≠ 0',
                 '{amount}.toNat ≤ (balance message state {from}).toNat'],
    'ensures': ['s.output = ByteArray.empty',
                '(balance message s.state {from}).toNat = (balance message state {from}).toNat - {amount}.toNat',
                'totalSupply message s.state = sub (totalSupply message state) {amount}',
                AL + ' ≠ ' + MAXW + ' → ' + AL1 + '.toNat = ' + AL + '.toNat - {amount}.toNat',
                AL + ' = ' + MAXW + ' → ' + AL1 + ' = ' + AL,
                keep('mapSlot {from} 2', '4', 'mapSlot {spender} (mapSlot {from} 3)'),
                AL + ' ≠ ' + MAXW + ' → s.substate.logs = (substate.logs.push (' + AP
                + ' {from} {spender} (wordBytes (sub ' + AL + ' {amount})))).push (' + TR
                + ' {from} 0 (wordBytes {amount}))',
                AL + ' = ' + MAXW + ' → s.substate.logs = substate.logs.push (' + TR
                + ' {from} 0 (wordBytes {amount}))']}
R['transferOwnership'] = {
    'doc': 'transferOwnership(newOwner) by the owner (Ownable2Step: it only names the pending '
           'owner). Success needs: no value, 36 bytes of call data, a clean address word, a '
           'frame that may write, and the caller is the owner. `newOwner` may be 0. Then: '
           'returns nothing; the low 20 bytes of slot 1 are `newOwner` (the other bytes keep '
           'their value), so the pending owner is `newOwner`; every other slot keeps its word '
           '(the owner does not change); exactly one log, OwnershipTransferStarted(owner, '
           'newOwner).',
    'let': {'new': 'addrArg1 message'},
    'sep': False,
    'requires': [V0, size(32), 'arg1 message = {new}', ST, ACC,
                 'callerW message = ownerOf message state'],
    'ensures': ['s.output = ByteArray.empty',
                f'storageAt s.state {C} 1 = bitwiseOr {{new}} (bitwiseAnd {HIGH} (storageAt state {C} 1))',
                'pendingOwnerOf message s.state = {new}',
                keep('1'),
                's.substate.logs = substate.logs.push (log3 message.currentTarget OWNERSHIP_STARTED (ownerOf message state) {new} ByteArray.empty)']}
R['acceptOwnership'] = {
    'doc': 'acceptOwnership() by the pending owner. Success needs: no value, a frame that may '
           'write, and the caller is the pending owner. Then: returns nothing; the low 20 '
           'bytes of slot 1 are 0 (no pending owner) and the low 20 bytes of slot 0 are the '
           'caller (the other bytes of both slots keep their value), so the owner is the '
           'caller; every other slot keeps its word; exactly one log, '
           'OwnershipTransferred(old owner, caller).',
    'sep': False,
    'requires': [V0, ST, ACC, 'callerW message = pendingOwnerOf message state'],
    'ensures': ['s.output = ByteArray.empty',
                f'storageAt s.state {C} 1 = bitwiseAnd {HIGH} (storageAt state {C} 1)',
                f'storageAt s.state {C} 0 = bitwiseOr (callerW message) (bitwiseAnd {HIGH} (storageAt state {C} 0))',
                'pendingOwnerOf message s.state = 0',
                'ownerOf message s.state = callerW message',
                keep('1', '0'),
                's.substate.logs = substate.logs.push (log3 message.currentTarget OWNERSHIP (ownerOf message state) (callerW message) ByteArray.empty)']}
R['setMinter'] = {
    'doc': 'setMinter(newMinter) by the owner. Success needs: no value, 36 bytes of call data, '
           'a clean address word, a frame that may write, and the caller is the owner. '
           '`newMinter` may be 0 (then nobody can mint). Then: returns nothing; the low 20 '
           'bytes of slot 11 are `newMinter` (the other bytes keep their value), so the '
           'minter is `newMinter`; every other slot keeps its word; exactly one log, '
           'MinterUpdated(newMinter, old minter).',
    'let': {'new': 'addrArg1 message'},
    'sep': False,
    'requires': [V0, size(32), 'arg1 message = {new}', ST, ACC,
                 'callerW message = ownerOf message state'],
    'ensures': ['s.output = ByteArray.empty',
                f'storageAt s.state {C} 11 = bitwiseOr {{new}} (bitwiseAnd {HIGH} (storageAt state {C} 11))',
                'minterOf message s.state = {new}',
                keep('11'),
                's.substate.logs = substate.logs.push (log3 message.currentTarget MINTER_UPDATED {new} (minterOf message state) ByteArray.empty)']}
cfg['readable'] = R
cfg['readable_opts'] = {
    'comment': 'facts: the condition shapes of optimized Solidity 0.8 (gen_readable.facts08 of '
               'this folder, with the checked addition ISZERO (GT a (ADD v a))); caller_key '
               'raw: the caller is a key of callKeys with no mask; close: the closing tactic; '
               'several_paths same_claims: every success path proves the same claims; simp: '
               'more rewrite rules (masks to one form, the two ownership slots, bit lemmas of '
               'Usde/ReadableLib.lean); header/unfold: more abbreviations of the token.',
    'facts': 'checked08',
    'add_gtc': True,
    'caller_key': 'raw',
    'close': 'readable_close08',
    'several_paths': 'same_claims',
    'imports': ['TokenKit.Evm.ReadableOpt', 'TokenKit.Evm.Opt06', 'UsdeVerify.Usde.ReadableLib'],
    'simp': ['and_mask_comm', "mask_toU256'", 'and_high_comm', 'add_sub_same', 'mask_or_high',
             'mask_or_high_addr', 'mask_and_high',
             'eq_false (by decide : (0 : U256) ≠ 1)', 'eq_false (by decide : (1 : U256) ≠ 0)'],
    'unfold': ['callerW', 'ownerOf', 'pendingOwnerOf', 'minterOf', 'nonceOf'],
    'header': [
        '/-- The caller, as a word (an address word: below 2^160). -/\n'
        'abbrev callerW (m : Message fork) : U256 := m.caller.toU256',
        '/-- `owner()` of the called contract in the state `S`: the address in slot 0. -/\n'
        'abbrev ownerOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd MASK (storageAt S m.currentTarget 0)',
        '/-- `pendingOwner()` of the called contract in the state `S`: the address in slot 1. -/\n'
        'abbrev pendingOwnerOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd MASK (storageAt S m.currentTarget 1)',
        '/-- `minter()` of the called contract in the state `S`: the address in slot 11. -/\n'
        'abbrev minterOf (m : Message fork) (S : State.TransactionState) : U256 :=\n'
        '  bitwiseAnd MASK (storageAt S m.currentTarget 11)',
        '/-- `_nonces[a]` of the called contract in the state `S`. -/\n'
        'abbrev nonceOf (m : Message fork) (S : State.TransactionState) (a : U256) : U256 :=\n'
        '  storageAt S m.currentTarget (mapSlot a 9)'],
    'heartbeats': 4000000,
}

# sanity: one concrete call for every success path (form eval of gen_sanity.py)
CW = 'Witness.CALLER1W'
BIG = 115792089237316195423570985008687907853269984665640564039457584007913129639935
cfg['sanity'] = {
    'comment': 'The witness call of each success path (scripts/gen_sanity.py, form eval): the '
               'argument words and the words of the slots of the state. The caller is '
               'Witness.CALLER1 (word Witness.CALLER1W); amounts are 1 and the balances and '
               'allowances used are 5; the owner, the pending owner or the minter is the '
               'caller where the path needs it. domainSeparator (three paths that depend on '
               'the address of the contract and on the chain id) has hand-written witnesses '
               'in Sanity/Domain.lean.',
    'imports': ['TokenKit.Evm.WitnessOpt'],
    'doc': '`<path>_runs` (or `<fn>_runs` for a function with one success path): in the state '
           'with one\naccount at the contract `C` that holds the stated words at the stated '
           'slots (every other slot\n0), the stated call from the caller `Witness.CALLER1` '
           'meets every hypothesis of the success path\ntheorem; so the loop of the '
           'interpreter runs it from pc 0 to the end with no error, for every\nmessage runner '
           'and every gas bound that holds its gas, with the stated output and end state.\n'
           'Every condition is computed by the kernel, the keccak of each mapping slot '
           'included: no\nhypothesis about keccak is used.',
    'totalSupply': {'args': [], 'slots': []},
    'decimals': {'args': [], 'slots': []},
    'owner': {'args': [], 'slots': []},
    'pendingOwner': {'args': [], 'slots': []},
    'minter': {'args': [], 'slots': []},
    'balanceOf': {'args': [2], 'slots': []},
    'nonces': {'args': [2], 'slots': []},
    'allowance': {'args': [2, 3], 'slots': []},
    'transfer': {'args': [2, 1], 'slots': [[f'mapSlot {CW} 2', 5]]},
    'approve': {'args': [2, 7], 'slots': []},
    'transferFrom': {
        'transferFrom_p10': {'args': [2, 3, 1],
                             'slots': [['mapSlot 2 2', 5], [f'mapSlot {CW} (mapSlot 2 3)', 5]]},
        'transferFrom_p15': {'args': [2, 3, 1],
                             'slots': [['mapSlot 2 2', 5], [f'mapSlot {CW} (mapSlot 2 3)', BIG]]}},
    'increaseAllowance': {'args': [2, 1], 'slots': []},
    'decreaseAllowance': {'args': [2, 1], 'slots': [[f'mapSlot 2 (mapSlot {CW} 3)', 5]]},
    'mint': {'args': [2, 1], 'slots': [[11, CW]]},
    'burn': {'args': [1], 'slots': [[f'mapSlot {CW} 2', 5], [4, 5]]},
    'burnFrom': {
        'burnFrom_p8': {'args': [2, 1],
                        'slots': [['mapSlot 2 2', 5], [f'mapSlot {CW} (mapSlot 2 3)', 5], [4, 5]]},
        'burnFrom_p12': {'args': [2, 1],
                         'slots': [['mapSlot 2 2', 5], [f'mapSlot {CW} (mapSlot 2 3)', BIG],
                                   [4, 5]]}},
    'transferOwnership': {'args': [2], 'slots': [[0, CW]]},
    'acceptOwnership': {'args': [], 'slots': [[1, CW]]},
    'setMinter': {'args': [2], 'slots': [[0, CW]]},
}
cfg['generators'] = ['code', 'dispatch', 'paths', 'loops', 'supply', 'readable', 'sanity',
                     'axioms']


# The axioms test. `after`: every theorem of the hand-written files (found by name in the files,
# so a new theorem is never forgotten), the generated theorems of `permit` (a prefix function:
# its paths stop at the STATICCALL and have no entry in the list of functions), and the lemmas
# of the kit library that `permit` uses.
def _hand_theorems(rel):
    import re
    src = open(os.path.join(HERE, '..', 'UsdeVerify', 'Usde', rel)).read()
    ns, out = '', []
    for ln in src.split('\n'):
        m = re.match(r'namespace (\S+)', ln)
        if m:
            ns = m.group(1)
        m = re.match(r'\s*theorem (\S+)', ln)
        if m:
            full = ns + '.' + m.group(1)
            out.append(full[len('UsdeVerify.'):] if full.startswith('UsdeVerify.') else full)
    return out


_HAND = ['Lib.lean', 'SupplyLib.lean', 'Sep.lean', 'ReadableLib.lean', 'Seq.lean', 'Permit.lean',
         'PermitSeq.lean', 'ReadableMore.lean', os.path.join('Sanity', 'Domain.lean')]
_PERMIT_GEN = []
_gen = open(os.path.join(HERE, '..', 'UsdeVerify', 'Usde', 'Gen', 'PPermit.lean')).read() \
    if os.path.exists(os.path.join(HERE, '..', 'UsdeVerify', 'Usde', 'Gen', 'PPermit.lean')) else ''
import re as _re
_PERMIT_GEN = _re.findall(r'^theorem (\S+)', _gen, _re.M)
cfg['axioms'] = {
    'comment': 'names: hand-written theorems checked before the generated ones; after: theorems '
               'of files that import the generated ones; declared_only: leave out a generated '
               'name that no Lean file declares.',
    'declared_only': True,
    'dotted_decl': True,
    'imports': ['UsdeVerify.Usde.Invariant', 'UsdeVerify.Usde.Readable',
                'UsdeVerify.Usde.Sanity.Zero', 'UsdeVerify.Usde.Seq', 'UsdeVerify.Usde.PermitSeq',
                'UsdeVerify.Usde.ReadableMore', 'UsdeVerify.Usde.Sanity.Domain'],
    'names': ['valid_CODE', 'selector_cases', 'ends_ok_dispatch', 'runFrame_ok_dispatch'],
    'after': _PERMIT_GEN + ['ok_permitTailC_ends', 'ok_permitTailR_ends']
    + [t for f in _HAND for t in _hand_theorems(f)]
    + ['Witness.caller1_toU256', 'Witness.endsL_of_reaches',
       'TokenKit.gas_outcome', 'TokenKit.staticcallStep_missing', 'TokenKit.step_at_staticcall',
       'TokenKit.staticcall_outcome', 'TokenKit.returndatacopyG', 'TokenKit.bubble_no_ok',
       'TokenKit.processMessage_precompile', 'TokenKit.runPrecompile_ecrecover',
       'TokenKit.precompileAddress_one', 'TokenKit.ecrecover_ran', 'TokenKit.insertMany_self',
       'TokenKit.incorporateChild_precompile', 'TokenKit.size_compute', 'TokenKit.load_ecrecover',
       'TokenKit.extendMemory_two', 'TokenKit.size_ecrecover_write',
       'TokenKit.read_ecrecover_other', 'TokenKit.ecrecover_call_ok',
       'TokenKit.wordBytes_loadWord', 'TokenKit.load_rawW', 'TokenKit.load_rawW_self',
       'TokenKit.readWord_raw', 'TokenKit.memoryReadBytes_add', 'TokenKit.read0_raw',
       'TokenKit.read_rawW', 'TokenKit.read4_raw', 'TokenKit.keccakK', 'TokenKit.timestampL'],
}

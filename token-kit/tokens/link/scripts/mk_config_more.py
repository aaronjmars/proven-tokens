# Run by mk_config.py (exec, with the dict `cfg` in scope): the readable corollaries of LINK
# (scripts/gen_readable.py writes LinkVerify/Link/Readable.lean from these descriptions).
_BAL = 'balance message state'
_BAL_END = 'balance message s.state'
_ALLOW = 'allowance message state'
_ALLOW_END = 'allowance message s.state'
_SAME = '∀ k, storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
_KEEP = 'storageAt s.state message.currentTarget k = storageAt state message.currentTarget k'
_SELF = 'message.currentTarget.toU256'
_WRITE = ['message.value = 0', 'message.isStatic = false',
          'hasAccount state message.currentTarget']
_NOSIZE = ('The code has no check of the size of the call data: bytes of an argument past the '
           'end of the call data read as zero.')

# names added to the axioms test by later hand-written files (witnesses, readable corollary of
# transferAndCall)
AXIOMS_EXTRA = ['tac_move_readable', 'transferAndCall_readable',
                'Sanity.transferAndCall_stop_runs', 'Sanity.transferAndCall_stop_runs_closed',
                'Sanity.transferAndCall_nocode_runs',
                'Sanity.transferAndCall_nocode_runs_closed',
                'Sanity.transferAndCall_low_runs', 'Sanity.transferAndCall_low_runs_closed',
                'Sanity.transferAndCall_reverts', 'Sanity.transferAndCall_reverts_closed',
                'Sanity.calleeKeeps_stop', 'Sanity.supply_tac_530_of',
                'Sanity.supply_transferAndCall_stop']

cfg['readable_opts'] = {
    'comment': 'facts checked04: the condition shapes of Solidity 0.4 with the optimizer on '
               '(gen_readable.facts04; lemmas of LinkVerify/Link/ReadableLib.lean); close: the '
               'closing tactic; several_paths same_claims: every success path proves the same '
               'claims (decreaseApproval has two); simp: the mask on the right of AND; sep_doc, '
               'doc: text of the head of the file.',
    'facts': 'checked04',
    'close': 'readable_close08',
    'several_paths': 'same_claims',
    'imports': ['TokenKit.Evm.ReadableOpt', 'TokenKit.Evm.Opt06', 'LinkVerify.Link.ReadableLib'],
    'simp': ['and_mask_comm'],
    'sep_doc': 'A theorem whose\nfunction writes two or more slots takes `Sep (callKeys message)` '
               '(the hypothesis on keccak of\nSep.lean, not proved): without it two of the slots '
               'could be the same slot.',
    'doc': [
        'LINK (Solidity 0.4.16) has no check of the size of the call data: bytes of an argument '
        'past the\nend of the call data read as zero, so no theorem here has a claim on '
        '`message.data.size`.\nThe total supply is no slot: `totalSupply()` returns the constant '
        '`10^27` of the code.\n`approve`, `increaseApproval` and `decreaseApproval` write one slot, '
        'so their theorems take no\nhypothesis on keccak; `transfer` and `transferFrom` take '
        '`Sep (callKeys message)`.\nIn `transfer`, `approve` and `transferFrom` the modifier '
        '`validRecipient` rejects the receiver\n(or spender) 0 and the address of the contract '
        'itself (`message.currentTarget.toU256`).'],
}

cfg['readable'] = {
    'totalSupply': {
        'doc': 'totalSupply(). Success needs no value. Then: returns the constant `10^27` held in '
               'the code (the total supply is no slot); no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (1000000000000000000000000000 : U256)',
                    '(1000000000000000000000000000 : U256).toNat = 10 ^ 27',
                    _SAME, 's.substate.logs = substate.logs'],
    },
    'decimals': {
        'doc': 'decimals(). Success needs no value. Then: returns the constant 18 held in the '
               'code; no slot changes; no log.',
        'requires': ['message.value = 0'],
        'ensures': ['s.output = wordBytes (18 : U256)', _SAME, 's.substate.logs = substate.logs'],
    },
    'balanceOf': {
        'doc': 'balanceOf(owner). Success needs no value. Then: returns `balances[owner]` (the '
               'argument masked to 160 bits); no slot changes; no log. ' + _NOSIZE,
        'let': {'owner': 'addrArg1 message'},
        'requires': ['message.value = 0'],
        'ensures': [f's.output = wordBytes ({_BAL} {{owner}})', _SAME,
                    's.substate.logs = substate.logs'],
    },
    'allowance': {
        'doc': 'allowance(owner, spender). Success needs no value. Then: returns '
               '`allowed[owner][spender]` (the arguments masked to 160 bits); no slot changes; '
               'no log. ' + _NOSIZE,
        'let': {'owner': 'addrArg1 message', 'spender': 'addrArg2 message'},
        'requires': ['message.value = 0'],
        'ensures': [f's.output = wordBytes ({_ALLOW} {{owner}} {{spender}})', _SAME,
                    's.substate.logs = substate.logs'],
    },
    'transfer': {
        'doc': 'transfer(to, value) with `from` the caller. Success needs: no value, a frame that '
               'may write, an account of the contract, `to` not 0 and not the contract itself '
               '(validRecipient), `value <= balances[from]`, and (when `to` is not `from`) no '
               'overflow of `balances[to]`. Then: returns 1; `balances[from]` is the old word '
               'minus `value` and `balances[to]` the old word plus `value` (when `to = from` the '
               'balance is unchanged); every other slot keeps its word; exactly one log, '
               'Transfer(from, to, value). ' + _NOSIZE,
        'let': {'from': 'sender message', 'to': 'addrArg1 message', 'amount': 'arg2 message'},
        'cases': ['{to} = {from}'],
        'requires': _WRITE + [
            '{to} ≠ 0', '{to} ≠ ' + _SELF,
            f'{{amount}}.toNat ≤ ({_BAL} {{from}}).toNat',
            f'{{to}} ≠ {{from}} → ({_BAL} {{to}}).toNat + {{amount}}.toNat < 2 ^ 256'],
        'ensures': [
            's.output = wordBytes 1',
            f'{{to}} ≠ {{from}} → ({_BAL_END} {{from}}).toNat = ({_BAL} {{from}}).toNat - '
            f'{{amount}}.toNat ∧ ({_BAL_END} {{to}}).toNat = ({_BAL} {{to}}).toNat + '
            '{amount}.toNat',
            f'{{to}} = {{from}} → {_BAL_END} {{from}} = {_BAL} {{from}}',
            '∀ k, k ≠ mapSlot {from} 1 → k ≠ mapSlot {to} 1 → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget TRANSFER '
            '{from} {to} (wordBytes {amount}))'],
    },
    'approve': {
        'doc': 'approve(spender, value) from the caller `owner`. Success needs: no value, a frame '
               'that may write, an account of the contract, `spender` not 0 and not the contract '
               'itself (validRecipient). Then: returns 1; `allowed[owner][spender]` is `value`; '
               'every other slot keeps its word; exactly one log, Approval(owner, spender, '
               'value). No hypothesis on keccak is needed. ' + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'value': 'arg2 message'},
        'sep': False,
        'requires': _WRITE + ['{spender} ≠ 0', '{spender} ≠ ' + _SELF],
        'ensures': [
            's.output = wordBytes 1',
            f'{_ALLOW_END} {{owner}} {{spender}} = {{value}}',
            '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 2) → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget APPROVAL '
            '{owner} {spender} (wordBytes {value}))'],
    },
    'transferFrom': {
        'doc': 'transferFrom(from, to, value) by the caller `spender`. Success needs: no value, a '
               'frame that may write, an account of the contract, `to` not 0 and not the contract '
               'itself (validRecipient), `value <= balances[from]`, (when `to` is not `from`) no '
               'overflow of `balances[to]`, and `value <= allowed[from][spender]`. Then: returns '
               '1; `balances[from]` is the old word minus `value` and `balances[to]` the old word '
               'plus `value` (when `to = from` the balance is unchanged); '
               '`allowed[from][spender]` is the old word minus `value` (whoever `spender` is: '
               '`from`, `to` or another address); every other slot keeps its word; exactly one '
               'log, Transfer(from, to, value) (no Approval log). ' + _NOSIZE,
        'let': {'from': 'addrArg1 message', 'to': 'addrArg2 message', 'amount': 'arg3 message',
                'spender': 'sender message'},
        'cases': ['{to} = {from}'],
        'requires': _WRITE + [
            '{to} ≠ 0', '{to} ≠ ' + _SELF,
            f'{{amount}}.toNat ≤ ({_BAL} {{from}}).toNat',
            f'{{to}} ≠ {{from}} → ({_BAL} {{to}}).toNat + {{amount}}.toNat < 2 ^ 256',
            f'{{amount}}.toNat ≤ ({_ALLOW} {{from}} {{spender}}).toNat'],
        'ensures': [
            's.output = wordBytes 1',
            f'{{to}} ≠ {{from}} → ({_BAL_END} {{from}}).toNat = ({_BAL} {{from}}).toNat - '
            f'{{amount}}.toNat ∧ ({_BAL_END} {{to}}).toNat = ({_BAL} {{to}}).toNat + '
            '{amount}.toNat',
            f'{{to}} = {{from}} → {_BAL_END} {{from}} = {_BAL} {{from}}',
            f'({_ALLOW_END} {{from}} {{spender}}).toNat = ({_ALLOW} {{from}} {{spender}}).toNat - '
            '{amount}.toNat',
            '∀ k, k ≠ mapSlot {from} 1 → k ≠ mapSlot {to} 1 → '
            'k ≠ mapSlot {spender} (mapSlot {from} 2) → ' + _KEEP,
            's.substate.logs = substate.logs.push (Readable.log3 message.currentTarget TRANSFER '
            '{from} {to} (wordBytes {amount}))'],
    },
    'increaseApproval': {
        'doc': 'increaseApproval(spender, added) from the caller `owner` (no validRecipient: '
               '`spender` may be 0 or the contract). Success needs: no value, a frame that may '
               'write, an account of the contract, and no overflow of `allowed[owner][spender]`. '
               'Then: returns 1; `allowed[owner][spender]` is the old word plus `added`; every '
               'other slot keeps its word; exactly one log, Approval(owner, spender, new '
               'allowance). No hypothesis on keccak is needed. ' + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'added': 'arg2 message'},
        'sep': False,
        'requires': _WRITE + [
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
        'doc': 'decreaseApproval(spender, subtracted) from the caller `owner` (no validRecipient). '
               'Success needs: no value, a frame that may write, an account of the contract. '
               'Then: returns 1; `allowed[owner][spender]` is 0 when `subtracted` is above the '
               'old word, else the old word minus `subtracted`; every other slot keeps its word; '
               'exactly one log, Approval(owner, spender, new allowance). No hypothesis on keccak '
               'is needed. ' + _NOSIZE,
        'let': {'owner': 'sender message', 'spender': 'addrArg1 message',
                'subtracted': 'arg2 message', 'old': _ALLOW + ' (sender message) (addrArg1 message)'},
        'sep': False,
        'requires': list(_WRITE),
        'ensures': [
            's.output = wordBytes 1',
            f'{{old}}.toNat < {{subtracted}}.toNat → {_ALLOW_END} {{owner}} {{spender}} = 0',
            f'{{subtracted}}.toNat ≤ {{old}}.toNat → ({_ALLOW_END} {{owner}} {{spender}}).toNat = '
            '{old}.toNat - {subtracted}.toNat',
            '∀ k, k ≠ mapSlot {spender} (mapSlot {owner} 2) → ' + _KEEP,
            '{old}.toNat < {subtracted}.toNat → s.substate.logs = substate.logs.push '
            '(Readable.log3 message.currentTarget APPROVAL {owner} {spender} '
            '(wordBytes (0 : U256)))',
            '{subtracted}.toNat ≤ {old}.toNat → s.substate.logs = substate.logs.push '
            '(Readable.log3 message.currentTarget APPROVAL {owner} {spender} '
            '(wordBytes (sub {old} {subtracted})))'],
    },
}

# witnesses added by the fix round of the ten-token audit (Sanity/Base.lean)
_WIT4 = ['Sanity.sumTo_zero', 'Sanity.holdsCode_baseState', 'Sanity.inv_baseState',
         'Sanity.good_baseState', 'Sanity.inv_runL_baseState']
# the ten-token audit, LINK-4: the witness with a receiver that calls back into the token (ReWit/Re.lean,
# ReWit/Run.lean, ReWit/Closed.lean)
_WIT4 += ['Sanity.' + n for n in [
    'size_RE', 're_not_delegated', 're_call', 'spec_message_runs', 're_message_runs',
    'frameOf_noValue', 'clean_of_spec', 're_clean', 're_inner_spec', 're_inner_runs',
    'tacCallGas_le', 'tac_call_run_re', 'reMeter_le', 'tac_re_core', 'callKeys_m_re',
    'supply_tac_re_frame', 'process_tac_re', 'msgL_tac_re', 're_hash_ne', 'holdsCode_reState',
    'getCode_reState', 'inv_reState', 'reenter_closed']]

if 'readable' not in cfg['generators']:
    cfg['generators'].append('readable')


# The axioms test (scripts/gen_axioms.py writes LinkVerify/Test/Axioms.lean). `names`: the
# hand-written theorems; `after`: theorems of files that import the generated ones. The scan of
# part 2 of the test covers every constant of every module of the root file anyway.
_TAC = ['tac_revert_zero', 'tac_revert_self', 'tac_invalid_low', 'tac_stuck_static',
        'tac_invalid_over', 'tac_done', 'tac_second_check', 'tac_to_gas', 'tac_at_call',
        'tac_call_range', 'tac_after_ok', 'tac_after_fail', 'ok_tac_pre', 'ok_tac_post',
        'ok_tac_dec_gas', 'ok_tac_len', "ok_tac_pre_gas", 'tac_log2_words', 'tac_call_words',
        'tac_call_selector', 'sel_bytes', 'tac_log2_head', 'tac_call_head', 'tacDoneSs_eq',
        'tacCallSs_eq', 'tacCallSt_eq', 'tacToZero_iff', 'tacToSet_iff', 'tacToSelf_iff',
        'tacLow_iff', 'tacFunded_iff', 'tacOver_iff', 'tacFits_iff', 'tacHasCode_iff',
        'tac_ext', 'tac_call_mem',
        # Whole.lean
        'tac_to_ne', 'inv_tacDoneSt', 'inv_tacCallSt', 'holdsCode_tacCallSt',
        'tac_after_fail_any', 'no_ok_after_fail', 'ok_tac_whole']
_REENTER = ['processMessage_good', 'processCreateMessage_good',
            'processCreateMessage_good_of_sane', 'processRunner_good', 'processRunner_goodKept',
            'runFrame_keeps', 'HoldsCode.hasAccount', 'holdsCode_writeSlot',
            'HoldsCode.of_readsAs']
# Fix round of the ten-token audit (LINK-1, LINK-2). `_GLOBAL`: the old forms, which assume the GLOBAL
# keccak hypotheses SepAll and NoCollision (almost certainly false); the hypothesis is in the
# name and they are corollaries only. `_LOCAL`: the run-local forms (Trace.lean, AnyLocal.lean,
# SeqLocal.lean, TraceWit.lean, Sanity/Base.lean): the headline theorems.
_GLOBAL = ['frameKeeps_sepAll', 'calleeKeeps_processRunner_sepAll_noCollision',
           'supply_all_real_sepAll_noCollision', 'process_good_sepAll_noCollision',
           'create_good_sepAll_noCollision', 'good_msg_sepAll_noCollision',
           'good_create_sepAll_noCollision', 'good_other', 'good_run_sepAll_noCollision',
           'inv_run_sepAll_noCollision']
_LOCAL = (['SepAll.msg']
          + ['Trace.' + n for n in [
              'processMessage_good_local', 'processCreateMessage_good_local',
              'processRunner_good_local', 'runFrame_keeps_local', 'runFrame_agree',
              'clean_of_global', 'clean_of_no_sent', 'not_sent_of_specG']]
          + ['frameKeepsQ', 'runnerKeeps_processRunner_local',
             'calleeKeeps_processRunner_local', 'supply_all_real_local',
             'cleanRunL_of_sepAll_noCollision', 'cleanFrameL_of_sepAll_noCollision',
             'supply_all_real_of_global',
             'process_good_local', 'create_good_local', 'good_msgL', 'good_createL',
             'good_runL', 'inv_runL', 'Sep.restrict', 'cleanL_of_sepList',
             'cleanL_of_sepAll_noCollision', 'cleanCreateL_of_sepAll_noCollision',
             'Msg.toLocal', 'Create.toLocal', 'Run.toLocal', 'inv_run_of_global',
             'not_sent_totalSupply', 'cleanL_totalSupply', 'cleanL_totalSupply_other',
             'process_good_totalSupply']
          + _WIT4)
cfg['axioms'] = {
    'comment': 'names: hand-written theorems checked before the generated ones; after: theorems '
               'of files that import the generated ones. transferAndCall is a prefix function '
               '(its generated path stops at pc 530): its generated theorems and the '
               'hand-written ones that finish it are named here. There is no skip list.',
    'declared_only': True,
    'declared_only_comment': 'the two fallbacks (call data shorter than 4 bytes with size 0, '
                             'unknown selector) never end with no error, so they have no '
                             'supply theorem: supply_short and supply_other are not declared '
                             'and are left out (printed in the head of Test/Axioms.lean).',
    'imports': ['LinkVerify.Link.Invariant'],
    'names': ['CODE_eq', 'size_CODE', 'and_div_selector', 'div_and_selector',
              'mask_idem', 'mask_lt', 'S_bal', 'S_allow', 'sumBal_congr', 'inv_of_ro',
              'TokenKit.Supply.add_fact_ltc', 'TokenKit.extendMemory_in', 'TokenKit.callInS',
              'TokenKit.callIn_outcome', 'TokenKit.callIn_outcome_any',
              'Sanity.link_address_word'],
    'after': (['Complete.ends_ok_dispatch', 'Complete.name_value', 'Complete.symbol_value',
               'Complete.value_zero_of_ok',
               'Paths.transferAndCall_p0', 'Paths.transferAndCall_p1',
               'Paths.ok_transferAndCall']
              + ['Tac.' + n for n in _TAC]
              + ['Reenter.' + n for n in _REENTER]
              + ['storageOnly_inv', 'code_not_delegated', 'SepAll.call',
                 'supply_tac_530', 'supply_transferAndCall', 'supply_all',
                 'calleeKeeps_of_keepsOn']
              + _GLOBAL + _LOCAL
              + AXIOMS_EXTRA),
}
cfg['generators'].append('axioms')

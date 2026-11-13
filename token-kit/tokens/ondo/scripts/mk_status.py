#!/usr/bin/env python3
"""Write status.json of tokens/ondo. The counts are read from the Lean files and from the build
log (logs/ondo.log of the repo) and the axioms output (logs/ondo.axioms); the texts are written by hand here.
Usage: python3 scripts/mk_status.py <seconds of the clean build>"""
import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
TH = re.compile(r'^(?:private |protected )?(?:theorem|lemma) (\S+)', re.M)


def names(path):
    return TH.findall(open(path).read())


def count(path):
    return len(names(path))


def many(pattern):
    return sum(count(f) for f in glob.glob(pattern))


log = open('../../../logs/ondo.log', errors='replace').read()
ax = open('../../../logs/ondo.axioms').read()
final = [l for l in log.splitlines() if l.startswith('Build completed')]
exit_line = [l for l in log.splitlines() if l.startswith('EXIT=')]
checked = int(re.search(r'theorems checked: (\d+)', ax).group(1))
scan = re.search(r'AXIOM SCAN OK: (\d+) constants \((\d+) theorems\)', ax)
assert 'only standard axioms' in ax and 'count matches' in ax
assert exit_line and exit_line[-1] == 'EXIT=0' and final

pfiles = glob.glob('OndoVerify/Ondo/Gen/P*.lean')
groups = {}
oks = 0
for f in pfiles:
    b = re.sub(r'\d+$', '', os.path.basename(f)[1:-5])
    g = groups.setdefault(b, [0, 0])
    ns = names(f)
    g[0] += 1
    g[1] += len(ns)
    oks += len([n for n in ns if n.startswith('ok_')])
seg = {k: groups[k] for k in ('Tt', 'Vest', 'Core', 'MvSrc', 'MvDst', 'Wck')}
inv = names('OndoVerify/Ondo/Invariant.lean')
frame = names('OndoVerify/Ondo/Frame.lean')
sanity = names('OndoVerify/Ondo/Sanity/Zero.lean')
runs = [n for n in sanity if n.endswith('_runs')]
readable = names('OndoVerify/Ondo/Readable.lean')
dead = json.load(open('config/dead.json'))
ndead = len(dead if isinstance(dead, list) else dead.get('rules', dead))
total = sum(count(f) for f in glob.glob('OndoVerify/**/*.lean', recursive=True))
secs = sys.argv[1] if len(sys.argv) > 1 else '?'
now = subprocess.check_output(['date', '-u', '+%Y-%m-%d %H:%M UTC']).decode().strip()

d = {
    'token': 'ONDO',
    'address': '0xfaba6f8e4a5e8ab82f62fe7c39859fa577269be3',
    'project': 'tokens/ondo',
    'namespace': 'OndoVerify',
    'config': 'config/ondo.json (written by scripts/mk_config.py) and config/dead.json (the table '
              'of dead branches, %d rules, each proved in Lean where it is used)' % ndead,
    'date': '2026-11-12',
    'bytecode': {
        'runtime_bytes': 11822,
        'compiler': 'solc 0.8.3, optimizer on (100 runs), per Etherscan as noted in '
                    'survey/tokens/ONDO/SOURCE.md; 53 trailing bytes are compiler metadata',
        'constant': 'OndoVerify/Ondo/Code.lean (CODE_eq, size_CODE, getElem_CODE, byteAt_CODE), '
                    'bytes in Ondo/Code/',
        'hash_test': 'OndoVerify/Test/Hash.lean (run by the interpreter at build time, not a '
                     'theorem)',
        'jumpdest_validity': 'valid_CODE (Ondo/Code.lean), pushData_CODE (Ondo/Steps.lean)',
        'opcode_counts_confirmed': 'SSTORE 17, SLOAD 67, SHA3 78, STATICCALL 1, TIMESTAMP 6, '
                                   'NUMBER 2, CHAINID 1 (docs/MAP.md); ABI 42 functions, 12 of '
                                   'them write storage',
    },
    'build': {
        'where': 'E2B box lean-fix5-ondo (8 GB, removed after the run), '
                 '/home/user/token-kit/tokens/ondo, Lean v4.35.0',
        'command': 'scripts/box.sh with CLEAN=1 (removes tokens/ondo/.lake/build first): lake '
                   'build of the five biggest path modules one at a time, then lake build of the '
                   'whole project. Log: logs/ondo.log',
        'exit_code': 0,
        'final_line': final[-1],
        'wall_time': 'DONE %ss' % secs,
        'sorry_in_log': log.count('sorry'),
        'axioms_check': "bash ../../scripts/check_axioms.sh <log> OndoVerify/Test/Axioms.lean: "
                        "'count matches Test/Axioms.lean: %d', 'only standard axioms' (propext, "
                        "Classical.choice, Quot.sound). The scan of every constant also passed: "
                        "'AXIOM SCAN OK: %s constants (%s theorems) of OndoVerify and TokenKit'. "
                        "Output in logs/ondo.axioms." % (checked, scan.group(1),
                                                                    scan.group(2)),
        'tree_check': 'md5 of every file of tokens/ondo (without .lake and work) on the Mac and '
                      'on the box compared after the last push: identical',
        'memory_note': 'PGetVestedBalance, PGetFreedBalance and PVest0..2 peak near 3.5 GB RSS '
                       'each. LEAN_NUM_THREADS does not limit the number of lake jobs, so box.sh '
                       'builds these five alone first (SEQ=). The shared kit on the box was built '
                       'once at the start and not pushed again.',
    },
    'theorem_counts': {
        'total_theorem_declarations': total,
        'checked_by_name_in_Test_Axioms': checked,
        'code_and_jumpdests': count('OndoVerify/Ondo/Code.lean') + count('OndoVerify/Ondo/Steps.lean'),
        'dispatcher': '%d in Complete/Dispatch.lean' % count('OndoVerify/Ondo/Complete/Dispatch.lean'),
        'basic_blocks': '%d in %d files Gen/B*.lean' % (many('OndoVerify/Ondo/Gen/B*.lean'),
                                                       len(glob.glob('OndoVerify/Ondo/Gen/B*.lean'))),
        'paths_and_completeness': '%d in %d files Gen/P*.lean: path specs (exact storage writes, '
                                  'logs, gas, return data), of which %d completeness theorems '
                                  'ok_<fn> and ok_<segment>' % (many('OndoVerify/Ondo/Gen/P*.lean'),
                                                                len(pfiles), oks),
        'shared_segments': 'files and theorems per chained segment (one file per entry shape): '
                           + ', '.join('%s %d files %d theorems' % (k, v[0], v[1])
                                       for k, v in seg.items())
                           + '. tt = _transferTokens entry (pc 6501), vest = the vesting check '
                             '(6912), core = the balance move (7089), mvSrc / mvDst = '
                             '_moveDelegates source and destination side (9085, 9325), wck = '
                             '_writeCheckpoint (9509)',
        'readonly_loops': '%d in Gen/Loops.lean, ending in ro_getPriorVotes (no storage write, no '
                          'log; nothing about the returned value)' % count('OndoVerify/Ondo/Gen/Loops.lean'),
        'arith': '%d in Arith.lean (word arithmetic for the vesting branches: word_omega, '
                 'dead_omega, vest_le, seed_le, div_max_ge)' % count('OndoVerify/Ondo/Arith.lean'),
        'separation': '%d in Sep.lean' % count('OndoVerify/Ondo/Sep.lean'),
        'frame': '%d in Frame.lean (%d <segment>_frame: what a segment leaves unchanged; %d '
                 '<segment>_delta: the segment keeps Dsum)' % (
                     len(frame), len([n for n in frame if n.endswith('_frame')]),
                     len([n for n in frame if n.endswith('_delta')])),
        'supply_invariant': '%d in Invariant.lean (%d delta_<fn>, %d supply_<fn>; delta_step and '
                            'supply_preserved among them) + %d in SigSupply.lean (delegateBySig '
                            'under the real runner, delta_step_real, supply_preserved_real)' % (
                                len(inv), len([n for n in inv if n.startswith('delta_')]),
                                len([n for n in inv if n.startswith('supply_')]),
                                count('OndoVerify/Ondo/SigSupply.lean')),
        'signatures_real_runner': '%d in Sig.lean (deleg_call, ok_delegateBySig_real)' % count('OndoVerify/Ondo/Sig.lean'),
        'sequences': '%d in Seq.lean' % count('OndoVerify/Ondo/Seq.lean'),
        'readable': '%d in Readable.lean (%s)' % (len(readable), ', '.join(
            n for n in readable if n.endswith('_readable') or n == 'mint_amounts')),
        'sanity_witnesses': '%d real runs in Sanity/Zero.lean (%d theorems with the size lemmas) + '
                            '3 runs in Runs.lean (%d theorems: transfer, transferFrom, delegate through the shared '
                            'segments)' % (len(runs), len(sanity), count('OndoVerify/Ondo/Runs.lean')),
        'transactions': '%d in Tx.lean (supply_any_transactions and the run-local steps)' % count('OndoVerify/Ondo/Tx.lean'),
        'instance': '%d in Instance.lean (inv_start, realSep_m0_iff, supply_m0, the slot facts)' % count('OndoVerify/Ondo/Instance.lean'),
        'votes': '%d in Votes.lean (mint_votes_counterexample, mint_votes_gap)' % count('OndoVerify/Ondo/Votes.lean'),
        'vesting': '%d in Vesting.lean (vcase0..7, vest<i>_rule, transfer_vesting, transferFrom_vesting)' % count('OndoVerify/Ondo/Vesting.lean'),
        'vacuity': 'scripts/vacuity_scan.py (z3) over the 1115 distinct generated paths: 0 '
                   'vacuous. 10 paths were not settled at 4 s; a second run at 60 s per path over '
                   'the four vesting functions (80 paths) settled all of them as satisfiable '
                   '(the two scan runs, logs not kept). Before that, %d dead-branch rules dropped '
                   'the vacuous paths at generation time; each rule is proved by dead_omega in '
                   'the completeness theorem that skips the branch. The z3 scan is evidence, '
                   'not a Lean proof: only the real runs above are proofs that a path is taken.' % ndead,
    },
    'main_theorems': {
        'supply_preserved': 'Invariant.lean. From Berlin, one call frame, any selector except '
                            'delegateBySig: if the call succeeds, Inv (sum over all addresses of '
                            'the low 96 bits of the balance slot = totalSupply, slot 4) still '
                            'holds. Uses Sep.',
        'supply_any_transactions': 'Tx.lean (the ONDO audit, ONDO-1). THE HEADLINE. On the shared '
                                   'library TokenKit.Seq, like the 11 other tokens: the '
                                   'invariant holds after any finite list of whole transactions '
                                   '(EthLib processTransaction: gas purchase, EIP-7702 '
                                   'authorizations, the message at any depth, calls back into '
                                   'ONDO included, refunds, fee, deletions), each from Dencun '
                                   'and before Glamsterdam. Also supply_message_any_depth, '
                                   'supply_transaction, supply_from_zero (from all-zero storage). '
                                   'Hypotheses: Seq.TxClean with Q = QMsg (run-local, see '
                                   'assumptions).',
        'supply_m0 / inv_start / realSep_m0_iff / qMsg_m0': 'Instance.lean (ONDO-2). One concrete '
                                   'state (sState C [], all storage 0) and one concrete call '
                                   '(allowance(K, K) from Witness.CALLER1): inv_start proves the '
                                   'start invariant, noDelegation1_sState proves NoDelegation1 '
                                   'for every such state, sigSigner_m0 proves the signer word is '
                                   '0 (v = 0), 26 slot facts are computed by the kernel, and '
                                   'realSep_m0_iff shows RealSep for this call is exactly the 21 '
                                   'facts of KeyFacts (each says a given slot is the balance slot '
                                   'of no address word: over 2^160 keccak values, cannot be run). '
                                   'supply_m0: the closed instance of supply_preserved_real with '
                                   'only the fork range and KeyFacts.',
        'transfer_runs, transferFrom_runs, delegate_runs': 'Runs.lean (ONDO-3). Real runs that end '
                                   'with no error, through the shared segments: transfer(2, 7) and '
                                   'transferFrom(K, 2, 7) from a state where the caller holds 10 '
                                   'and transfers are on (tt, vest, core, mvSrc segments composed '
                                   'with Reaches.trans), delegate(...) through mvSrc, mvDst and '
                                   'wck (writes a checkpoint; hypothesis: block number below '
                                   '2^32). Berlin to before Glamsterdam, every message runner.',
        'transfer_vesting, transferFrom_vesting': 'Vesting.lean (ONDO-4). The vesting rule in plain '
                                   'words (VestRule, lockedAt), proved from the 8 cases of '
                                   'vest0/vest1/vest2_ends: after a successful transfer or '
                                   'transferFrom of amount a from holder h with initial lock B, '
                                   'tranche t, cliff c and time now, either B = 0, or c + '
                                   '60566400 < 2^256, the tranche is at most 2 while now <= c + '
                                   '60566400, the locked part lockedAt B t c now is at most the '
                                   'balance and a <= balance - locked. lockedAt: B while now <= c; '
                                   '0 after c + 60566400; tranche 0: B - B*min(now-c, 15811200)/'
                                   '15811200; tranche 1: the same with 47433600; seed: B - (B/3 + '
                                   '2*(B*(now-c)/60566400)/3).',
        'mint_votes_counterexample, mint_votes_gap': 'Votes.lean (ONDO-5). The planned "votes add '
                                   'up" invariant is FALSE and is not claimed: mint adds to a '
                                   'balance and writes no checkpoint. mint_votes_counterexample: '
                                   'from a closed state, mint(2, 7) runs with no error and after '
                                   'every such run the balance of 2 is 7, its delegate is K and K '
                                   'still has 0 checkpoints. mint_votes_gap: the true general fact '
                                   '(balance grows by the amount, numCheckpoints and every '
                                   'checkpoint of a delegate stay).',
        'supply_preserved_real': 'SigSupply.lean. All 42 selectors and the three revert paths '
                                 '(valueSent, short, other: ONDO has no fallback function, and '
                                 'Complete/Dispatch.lean proves these never end without an error), '
                                 'delegateBySig '
                                 'included, under EthLib\'s real runner (the real ECRECOVER '
                                 'precompile, no assumption on its output), Paris to before '
                                 'Glamsterdam. Uses RealSep and hdel.',
        'delta_step / delta_step_real': 'The exact form: Dsum (sum of balances minus totalSupply) '
                                        'after a successful call equals Dsum before.',
        'mint_readable + mint_amounts': 'Readable.lean. Who: the caller has MINTER_ROLE. dst is '
                                        'not 0. The amount and the old totalSupply are below 2^96 '
                                        'and their sum is below 2^96 (the only cap; no waiting '
                                        'time, no percent cap). Only slot 4 and balances[dst] can '
                                        'change. mint_amounts: totalSupply grows by exactly the '
                                        'amount and the low 96 bits of balances[dst] grow by '
                                        'exactly the amount (hypothesis: the balance slot of dst '
                                        'is not slot 4).',
        'role and admin writers': 'updateCliffTimestamp_readable and enableTransfer_readable '
                                  '(caller has DEFAULT_ADMIN_ROLE; only slot 1 / slot 3 can '
                                  'change), updateTrancheBalance_readable (TIMELOCK_UPDATE_ROLE; '
                                  'only investorBalances[investor]), grantRole_readable and '
                                  'revokeRole_readable (caller has the admin role of the role; '
                                  'only the member slot), renounceRole_readable (account = '
                                  'caller), approve_readable (only allowances[caller][spender]).',
        'transfer_readable, transferFrom_readable': 'The amount is below 2^96, and transferAllowed '
                                                   '(low byte of slot 3) is set or the caller has '
                                                   'TRANSFER_ROLE.',
        'delegate_readable, delegateBySig_readable': 'delegate: only delegates[caller] and the '
                                                    'checkpoint slots of the old and the new '
                                                    'delegate can change. delegateBySig (real '
                                                    'runner): the recovered signer is not 0, the '
                                                    'nonce of the call data equals the stored '
                                                    'nonce of the signer, timestamp <= expiry.',
        'ok_delegateBySig_real': 'Sig.lean. Completeness of delegateBySig through the STATICCALL '
                                 'to address 1 with the kit model of the ECRECOVER precompile.',
        'process_step_inv / calls_process': 'Seq.lean, the OLDER WEAKER model, kept (not a '
                                            'headline): its Calls assumes each other step leaves '
                                            'the storage of the token alone (Calls.other). '
                                            'Superseded by Tx.lean, which needs no such step '
                                            'assumption. Paris to before Glamsterdam.',
    },
    'assumptions': [
        'Sep (callKeys message) (ckKeys message state) role, used by every delta_<fn>, '
        'supply_<fn>, delta_step, supply_preserved and the <segment>_delta theorems: keccak '
        'separation of storage slots, stated for finite lists only. A = caller and the two address '
        'arguments; D = A plus their delegates in the start state. Fields: slot 4, slot 1 and slot '
        '3 are the balance slot of no address; the balance slot of a word of A is the balance slot '
        'of no other address; allowance, investorBalances, role member, delegates and nonces slots '
        'keyed by words of A are no balance slot and not slot 4; allowance and nonces slots of A '
        'are not delegates slots of A; numCheckpoints and checkpoints slots (index below 2^32) of '
        'words of D are no balance slot and not slot 4. "No balance slot" ranges over the 2^160 '
        'address words for one fixed slot. This is a statement about keccak that cannot be proved '
        'in Lean and is believed true (a failure would be a keccak collision).',
        'RealSep message state, used by delta_delegateBySig_real, supply_delegateBySig_real, '
        'delta_step_real, supply_preserved_real, GoodCall, process_step, process_step_inv, '
        'calls_process: the same Sep with the recovered signer added to A and its delegate added '
        'to D.',
        'hdel / NoDelegation1, used by ok_delegateBySig_real, delegateBySig_readable and every '
        'theorem of SigSupply.lean and Seq.lean under the real runner: from Pectra, the account at '
        'address 1 holds no EIP-7702 delegation code. Fork from Paris and before Glamsterdam.',
        'mint_amounts only: hne, the balance slot of dst is not slot 4 (one keccak fact; it '
        'follows from Sep.total).',
        'delegate_readable only: the new delegatee and the old delegate of the caller are in the '
        'list D that names the checkpoint slots (a premise that fixes D, not a keccak fact).',
        'Fork range (ONDO-8): the generated path theorems, supply_preserved, delta_step, every '
        'delta_/supply_<fn> and every readable theorem except delegateBySig_readable are STATED '
        'from Berlin with no upper bound, with the one-counter Nat gas meter. They are true '
        'theorems, but from Glamsterdam EthLib does not run that meter, so for those forks they '
        'speak about a run EthLib does not make: their meaning is per call, one-counter meter, '
        'before Glamsterdam. Only the real-runner theorems (SigSupply, Sig, Seq, Tx, supply_m0) '
        'carry fork < .glamsterdam in the statement. Call data size below 2^256.',
        'supply_any_transactions, supply_transaction, supply_message_any_depth, supply_from_zero '
        '(Tx.lean): Seq.TxClean of each transaction with Q = QMsg = RealSep and NoDelegation1, '
        'run-local: each message that really enters the code at C during the run, with its start '
        'state, meets RealSep and NoDelegation1; each code a creation deposits with the keccak hash '
        'of CODE is CODE; no authorization sets a code with that hash; call data below 2^256 bytes. '
        'Fork of each transaction from Dencun and before Glamsterdam. Start: C holds CODE and Inv '
        'holds (or all-zero storage for supply_from_zero).',
        'supply_m0 (Instance.lean): KeyFacts (21 named keccak facts, exactly RealSep for that call '
        'and state by realSep_m0_iff) and Paris <= fork < Glamsterdam.',
        'delegate_runs (Runs.lean): the block number is below 2^32 (the checkpoint write path).',
        'transferFrom_vesting (Vesting.lean): three keccak facts, the allowance slot of the call is '
        'not the investorBalances slot of the holder, not slot 1, not the balance slot of the '
        'holder.',
        'mint_keeps_checkpoint, mint_keeps_numCheckpoints, mint_votes_gap (Votes.lean): the '
        'checkpoint / numCheckpoints slot named is not slot 4 and not the balance slot of dst '
        '(keccak facts); mint_votes_gap also hne as in mint_amounts. mint_votes_counterexample has '
        'no hypothesis but the fork (from Berlin).',
        'Inv is assumed before the call (it is an invariant; it is not proved for the '
        'constructor: the creation code is not part of this work).',
        'process_step / process_step_inv / calls_process: message.code = CODE and the target is '
        'no precompile address.',
    ],
    'not_covered': [
        'Votes (ONDO-5): the old plan "latest checkpoint votes of a delegate = sum of the balances '
        'that delegate to it" is FALSE (mint_votes_counterexample) and is not claimed. Not proved: '
        'the weaker true form (every function but mint keeps, per delegate, votes minus delegated '
        'balances; mint lowers it by the amount).',
        'Vesting (ONDO-4): the transfer check is restated (transfer_vesting, transferFrom_vesting). '
        'Not restated: the return values of getFreedBalance and getVestedBalance (path theorems '
        'only), and the exact new balances of transfer and transferFrom (core<i>_ends).',
        'Real runs (ONDO-3): %d generated runs in Sanity/Zero.lean plus transfer_runs, '
        'transferFrom_runs, delegate_runs (Runs.lean). Missing: delegateBySig (needs a real '
        'secp256k1 signature for the ONDO domain and a port of the forward ECRECOVER rule of UNI '
        'PermitRun), getFreedBalance (8 paths) and getVestedBalance (7 of 8), getPriorVotes '
        '(loop), and transferFrom with spender != src (one run each: the role path and spender = '
        'src only). The z3 vacuity scan says the other paths are satisfiable: that is evidence, '
        'not a Lean proof.' % len(runs),
        'getPriorVotes: only ro_getPriorVotes (no write, no log) and the entry path; nothing '
        'about the returned value. name and symbol: the path theorems give the returned bytes as '
        'the code builds them, with no readable corollary.',
        'delegateBySig (ONDO-9): the digest is the EIP-712 digest of the source (constants checked '
        'in check_eip712.out (audit scratch, not kept)). There is no authorization theorem: nothing says '
        'a successful delegateBySig was signed by the key of the account whose delegate changed. '
        'delegate_readable and delegateBySig_readable give the slots that may change and the '
        'checks, not that delegates[caller] becomes the delegatee, the nonce grows by one, or how '
        'many votes move (those writes are only inside the ends definitions).',
        'The EIP-8037 gas meter (Glamsterdam) is not ported; every theorem stops before '
        'Glamsterdam.',
        'Constructor and initial state: not covered (runtime code only). Reentrancy is not an '
        'issue here: the only external call is the STATICCALL to address 1.',
        'The bytecode was not compared line by line with the published Solidity source.',
    ],
    'contract_findings': [
        'totalSupply can grow: mint adds the amount to totalSupply and to balances[dst]. Who: any '
        'caller that holds MINTER_ROLE (mint_readable). Cap: only that the amount and the new '
        'total fit in 96 bits. No time lock and no percent cap in the bytecode (unlike UNI).',
        'There is no burn: among the generated paths, slot 4 (totalSupply) is written only in the '
        'mint path (Gen/PMint.lean), and that write adds the amount.',
        'mint writes exactly two slots (totalSupply and balances[dst]) and one log: it does not '
        'move votes to the delegate of dst (ok_mint).',
        'Roles: grantRole and revokeRole need the admin role stored for the role (the word that '
        'getRoleAdmin reads); a holder of that admin role can therefore give MINTER_ROLE to any '
        'address. '
        'Locks (ONDO-6): updateTrancheBalance (TIMELOCK_UPDATE_ROLE) sets a lock only when the '
        'stored initial balance is 0, amount 1..2^96-1, tranche < 3: each address is locked once '
        '(ok_updateTrancheBalance; updateTrancheBalance_readable drops these conditions). The role '
        'can lock ANY unlocked address for up to 2^96 - 1, not tied to its balance; while locked a '
        'holder can send only balance - locked, and all transfers out revert when the lock exceeds '
        'the balance. Locks also apply to tokens received later (the check is on the whole '
        'balance). DEFAULT_ADMIN_ROLE sets cliffTimestamp to any value at any time: a later cliff '
        're-locks every locked address, and a cliff above 2^256 - 1 - 60566400 makes every transfer '
        'out of a locked address revert (Vesting.lean, VestRule). DEFAULT_ADMIN_ROLE also turns '
        'transfers on.',
        'Transfer gate (ONDO-7): for transferFrom the TRANSFER_ROLE checked is the one of msg.sender '
        '(the spender), not of src (tt1_ends / tt2_ends). While transfers are off, a TRANSFER_ROLE '
        'holder with an allowance can move anyone\'s tokens, and nobody can pull tokens from a role '
        'holder without the role. enableTransfer only writes 1 into the low byte of slot 3 and no '
        'other path writes slot 3: transfers cannot be switched off again.',
        'enableTransfer can only write slot 3, and among the generated paths slot 3 is written only '
        'there (Gen/PEnableTransfer.lean); what it writes is in ok_enableTransfer. '
        'While transferAllowed is 0, only holders of TRANSFER_ROLE can call transfer and '
        'transferFrom with success.',
        'delegateBySig reads nonces[signer] after the ECRECOVER call, for the recovered address, '
        'and requires it to equal the nonce of the call data; a recovered address 0 reverts.',
        'Balances are uint96 in the low bits of the slot; the code keeps the high 160 bits on a '
        'write, so the invariant is stated over the low 96 bits.',
    ],
    'generator_and_library_changes': {
        'shared_kit': 'None. Nothing under token-kit/scripts, token-kit/TokenKit or TokenKit.lean '
                      'was edited. The box kept the kit it had built at the start.',
        'local_copies_of_generators': 'tokens/ondo/scripts/ holds copies of the kit generators '
                                      '(gen_paths.py, gen_supply_chain.py, gen_axioms.py, '
                                      'gen_sanity.py, ...) with the ONDO changes (dead_table, '
                                      'finite Sep, one-pass axioms scan) that the kit does not '
                                      'have. Regenerate ONLY with tokens/ondo/scripts/regen_ondo.sh: '
                                      'the kit scripts/regen.sh on config/ondo.json would not '
                                      'reproduce the checked files (ONDO-10).',
        'changes_in_the_copies': [
            'gen_paths.py: paths.dead_table (config/dead.json): a branch whose condition matches a '
            'rule is not followed; the completeness theorem closes it with dead_omega. '
            'scripts/deadpat.py matches the rules, scripts/vacuity_scan.py finds candidates with '
            'z3.',
            'gen_supply_chain.py: segment kinds for six chained segments, Sep over finite key '
            'lists, membership side goals closed by key_mem / key_mem_sep (Sep.lean).',
            'gen_axioms.py: the scan of declared names splits the text once (the kit version is '
            'quadratic and did not finish on 58 MB of sources).',
            'gen_sig.py (from UNI): pcs, stack shape and memory sizes of the ONDO delegateBySig.',
        ],
        'hand_written': 'Arith.lean, Sep.lean, SigSupply.lean, Seq.lean, Readable.lean, Tx.lean, '
                        'Instance.lean, Votes.lean (body of mint_votes_runs copied from the '
                        'generated Sanity witness), Runs.lean and Vesting.lean (written by small '
                        'helper scripts outside the tree, checked in as plain Lean); '
                        'scripts/mk_config.py, box.sh, boxw.sh, errs.sh, mk_status.py',
        'lessons': [
            'A plain assumption or exact between two different mapSlot terms makes Lean unfold '
            'keccak and run out of heartbeats: use with_reducible assumption.',
            'In first | ... | simp [...], end a simp alternative with done, or a simp that does '
            'not close the goal counts as success.',
            'lake does not honor LEAN_NUM_THREADS as a job limit: build the biggest modules alone '
            'first on an 8 GB box.',
        ],
    },
    'to_merge_into_kit': [
        'paths.dead_table + deadpat.py + vacuity_scan.py (drop vacuous paths with Lean-checked '
        'rules) into scripts/gen_paths.py.',
        'The finite Sep (key lists) and the key_mem macros into gen_supply_chain.py, and the same '
        'repair for UNI Sep.',
        'The one-pass split in gen_axioms.py.',
        'Arith.lean (word_omega, dead_omega) as a TokenKit/Evm file.',
        'box.sh SEQ= (big modules one at a time), boxw.sh, errs.sh as shared box helpers.',
        'Runs.lean (copied from UNI): writeMax_le, writeCost_le22100, the macros gas_bound and '
        'acc_side, endsL_join (compose segment runs).',
        'Vesting.lean: m160_m160 (bitwiseAnd M160 is idempotent), and the word-level vcase0..7 '
        'lemmas as a pattern for vesting checks.',
        'Instance.lean: byteAt_append_left, byteAt_append_right, word32_sigInput, '
        'recoveredWord_v0, getStorage_sState_nil, noDelegation1_of_emptyHash, '
        'noDelegation1_before_pectra, codeHash_sState, noDelegation1_sState (generic, not ONDO).',
    ],
    'history': [
        '2026-11-11 17:17 UTC first agent: box, config, generated paths, vacuity rules, first '
        'build round.',
        '2026-11-11 21:13 UTC second agent resumed: Frame / Invariant fixed (key_mem), Sig, '
        'SigSupply, Seq, Readable, Sanity, Axioms; paused by the lead about 21:50 UTC, resumed '
        '22:50 UTC; final clean build.',
        '2026-11-12 ONDO fix round (ONDO audit, ONDO-1..10): Tx.lean, Instance.lean, Runs.lean, '
        'Vesting.lean, Votes.lean; status texts fixed; box lean-fix5-ondo; clean build and status '
        'written %s.' % now,
    ],
}
txt = json.dumps(d, indent=1, ensure_ascii=False)
assert chr(0x2013) not in txt and chr(0x2014) not in txt
open('status.json', 'w').write(txt + '\n')
print('status.json written:', total, 'theorems,', checked, 'checked,', len(runs), 'witnesses')

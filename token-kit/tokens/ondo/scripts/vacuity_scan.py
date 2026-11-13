#!/usr/bin/env python3
"""Find vacuous path theorems: paths of work/paths.json whose branch conditions contradict each
other, and write the branches that decide them (config/dead.json, read by gen_paths.py as
`paths.dead_table`).

Every condition is translated to a 256-bit bit-vector formula (isZero, lessThan, greaterThan,
equal, the bitwise operations, add, sub, mul and div by a numeral, shifts, signed comparisons).
Reads of the storage, keccak, the call data and the block fields are free words. A product of
two words that are no numerals and a division by a word that is no numeral are free functions,
with the two facts of OndoVerify/Ondo/Arith.lean about them (`vest_le`, `div_max_ge`). The
formulas go to the SMT solver Z3. For a path whose conditions are unsatisfiable the script
finds the first condition that the earlier ones decide and a smallest set of earlier conditions
that decides it.

This is a development check: nothing it prints is trusted. Lean checks each recorded branch
again when it compiles the `dead_omega` proof that gen_paths.py writes for it. A path that the
solver cannot settle within the time limit is printed as UNKNOWN.

Usage: uv run --with z3-solver python3 scripts/vacuity_scan.py work/paths.json [name regex ...]
       (--no-table: do not write config/dead.json)"""
import json
import os
import re
import sys

import z3

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import deadpat as dp  # noqa: E402

W = 256
ATOMS = {}
FMUL = z3.Function('fmul', z3.BitVecSort(W), z3.BitVecSort(W), z3.BitVecSort(W))
FDIV = z3.Function('fdiv', z3.BitVecSort(W), z3.BitVecSort(W), z3.BitVecSort(W))


def atom(t):
    k = dp.flat(t)
    if k not in ATOMS:
        ATOMS[k] = z3.BitVec('a%d' % len(ATOMS), W)
    return ATOMS[k]


def b2w(c):
    return z3.If(c, z3.BitVecVal(1, W), z3.BitVecVal(0, W))


def tr(t):
    n = dp.num(t)
    if n is not None:
        return z3.BitVecVal(n, W)
    if isinstance(t, str):
        return z3.BitVecVal(int(t), W) if t.isdigit() else atom(t)
    if not dp.is_arith(t):
        return atom(t)
    f, a = t[0], t[1:]
    if f == 'isZero':
        return b2w(tr(a[0]) == 0)
    if f == 'lessThan':
        return b2w(z3.ULT(tr(a[0]), tr(a[1])))
    if f == 'greaterThan':
        return b2w(z3.UGT(tr(a[0]), tr(a[1])))
    if f == 'signedLessThan':
        return b2w(tr(a[0]) < tr(a[1]))
    if f == 'signedGreaterThan':
        return b2w(tr(a[0]) > tr(a[1]))
    if f == 'equal':
        return b2w(tr(a[0]) == tr(a[1]))
    if f == 'bitwiseAnd':
        return tr(a[0]) & tr(a[1])
    if f == 'bitwiseOr':
        return tr(a[0]) | tr(a[1])
    if f == 'bitwiseXor':
        return tr(a[0]) ^ tr(a[1])
    if f == 'bitwiseNot':
        return ~tr(a[0])
    if f == 'add':
        return tr(a[0]) + tr(a[1])
    if f == 'sub':
        return tr(a[0]) - tr(a[1])
    if f == 'mul':
        if dp.num(a[0]) is None and dp.num(a[1]) is None:
            return FMUL(tr(a[0]), tr(a[1]))
        return tr(a[0]) * tr(a[1])
    if f == 'div':
        if dp.num(a[1]) is None:
            return FDIV(tr(a[0]), tr(a[1]))
        return z3.BitVecVal(0, W) if dp.num(a[1]) == 0 else z3.UDiv(tr(a[0]), tr(a[1]))
    if f == 'bitwiseShl':
        return z3.If(z3.ULT(tr(a[0]), 256), tr(a[1]) << tr(a[0]), z3.BitVecVal(0, W))
    if f == 'bitwiseShr':
        return z3.If(z3.ULT(tr(a[0]), 256), z3.LShR(tr(a[1]), tr(a[0])), z3.BitVecVal(0, W))
    raise SystemExit('no translation of ' + f)


def facts(trees):
    out = []
    for h in dp.helpers(trees):
        if h[0] == 'vest':
            y, e, p = tr(dp.strip(dp.parse(h[1]))), tr(dp.strip(dp.parse(h[2]))), h[3]
            out.append(z3.Implies(z3.ULE(e, p), z3.ULE(z3.UDiv(FMUL(y, e), z3.BitVecVal(p, W)), y)))
        elif h[0] == 'seed':
            continue
        else:
            y = tr(dp.strip(dp.parse(h[1])))
            out.append(z3.Implies(y != 0, z3.UGE(FDIV(z3.BitVecVal(dp.MAX, W), y),
                                                 z3.BitVecVal(1 << 160, W))))
    return out


def check(conds, idx, timeout=int(os.environ.get('SCAN_TIMEOUT_MS', '4000'))):
    s = z3.Solver()
    s.set('timeout', timeout)
    trees = [conds[i][3] for i in idx]
    for f in facts([conds[i][4] for i in idx]):
        s.add(f)
    for i in idx:
        v = tr(conds[i][3])
        s.add((v != 0) if conds[i][2] else (v == 0))
    return s.check()


def scan_fn(job):
    """The vacuous and unknown paths of one function, and the rules for them."""
    fn, paths = job
    bad, unk, rules = [], [], []
    for p in paths:
        # the facts that the path theorem proves on the way (`derived`) count as conditions
        raw = [(hd, c, taken) for (hd, c, taken, _) in p.get('derived', [])] + list(p['conds'])
        nder = len(p.get('derived', []))
        conds = [(cn, c, taken, dp.strip(dp.parse(c)), dp.parse(c)) for (cn, c, taken) in raw]
        r = check(conds, range(len(conds)))
        if r == z3.sat:
            continue
        if r != z3.unsat:
            unk.append((fn, p['name'], p['kind']))
            continue
        # the shortest prefix that is unsatisfiable: its last condition is decided
        lo, hi = nder + 1, len(conds)
        while lo < hi:
            mid = (lo + hi) // 2
            if check(conds, range(mid)) == z3.unsat:
                hi = mid
            else:
                lo = mid + 1
        last = lo - 1
        core = list(range(last))
        for i in list(core):
            trial = [j for j in core if j != i] + [last]
            if check(conds, trial) == z3.unsat:
                core.remove(i)
        bad.append((fn, p['name'], p['kind'], [conds[i][:3] for i in core + [last]]))
        amap = {}
        cpat = dp.canon(conds[last][3], amap)
        hp = [[dp.canon(conds[i][3], amap), conds[i][2]] for i in core]
        rules.append(dict(cond=cpat, taken=not conds[last][2], hyps=hp))
    return bad, unk, rules, len(paths)


def main():
    import multiprocessing
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    d = json.load(open(args[0]))
    only = args[1:] or None
    jobs = []
    for fn in sorted(d):
        if not isinstance(d[fn], dict) or 'paths' not in d[fn]:
            continue
        if only and not any(re.fullmatch(o, fn) for o in only):
            continue
        # paths with the same conditions (the stuck twin of a path) are checked once
        seen, ps = set(), []
        for p in d[fn]['paths']:
            k = json.dumps([p['conds'], p.get('derived')])
            if k not in seen:
                seen.add(k)
                ps.append(dict(name=p['name'], kind=p['kind'], conds=p['conds'],
                               derived=p.get('derived', [])))
        jobs.append((fn, ps))
    jobs.sort(key=lambda j: -len(j[1]))
    bad, unk, n, rules, seen = [], [], 0, [], set()
    with multiprocessing.Pool(max(1, multiprocessing.cpu_count() - 2)) as pool:
        for b, u, rs, k in pool.imap_unordered(scan_fn, jobs):
            bad += b
            unk += u
            n += k
            for rule in rs:
                key = json.dumps(rule, sort_keys=True)
                if key not in seen:
                    seen.add(key)
                    rules.append(rule)
    bad.sort()
    unk.sort()
    rules.sort(key=lambda r: json.dumps(r, sort_keys=True))
    print('paths checked: %d, vacuous: %d, unknown: %d, rules: %d' % (n, len(bad), len(unk), len(rules)))
    for fn, name, kind, core in bad[:40]:
        print('VACUOUS %s %s (%s)' % (fn, name, kind))
        for cn, c, taken in core:
            print('    %s %s %s' % (cn, '≠0' if taken else '=0', c[:300]))
    for fn, name, kind in unk:
        print('UNKNOWN %s %s (%s)' % (fn, name, kind))
    root = os.path.dirname(os.path.dirname(os.path.abspath(args[0])))
    json.dump({'vacuous': [b[:3] for b in bad], 'unknown': unk, 'checked': n},
              open(os.path.join(root, 'work', 'vacuity.json'), 'w'), indent=1)
    if '--no-table' not in sys.argv:
        f = os.path.join(root, 'config', 'dead.json')
        old = json.load(open(f)) if os.path.exists(f) else []
        have = {json.dumps(r, sort_keys=True) for r in old}
        new = [r for r in rules if json.dumps(r, sort_keys=True) not in have]
        json.dump(old + new, open(f, 'w'), indent=1)
        print('config/dead.json: %d rules (%d new)' % (len(old) + len(new), len(new)))


if __name__ == '__main__':
    main()

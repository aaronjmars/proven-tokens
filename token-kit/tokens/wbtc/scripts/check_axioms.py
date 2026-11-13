#!/usr/bin/env python3
"""Read a build log and check the axioms test of a token. It fails (exit code 1) when:

- the log is missing or empty, or has no `#print axioms` result at all;
- a theorem depends on an axiom other than propext, Classical.choice and Quot.sound (the list
  of axioms of one theorem may run over several lines of the log: all of them are read);
- the log has a `declaration uses 'sorry'` warning or a `sorryAx`;
- the count of results is not the count of `#print axioms` lines of Test/Axioms.lean (when that
  file is given), so a theorem that did not print is seen;
- the scan of every constant (`AXIOM SCAN OK`, written by Test/Axioms.lean) is not in the log,
  when Test/Axioms.lean has the scan.

Usage: check_axioms.py <build log> [<Root>/Test/Axioms.lean]"""
import re
import sys

STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    try:
        log = open(sys.argv[1], errors='replace').read()
    except OSError as e:
        print('FAIL: cannot read the log:', e)
        return 1
    if not log.strip():
        print('FAIL: the log is empty')
        return 1
    bad = []
    # one result: 'X' depends on axioms: [a, b, c]  (the list may wrap over lines)
    dep = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    free = re.findall(r"'([^']+)' does not depend on any axioms", log)
    used = {}
    for name, body in dep:
        for a in re.split(r'[,\s]+', body.strip()):
            if a:
                used[a] = used.get(a, 0) + 1
                if a not in STANDARD:
                    bad.append(f'{name}: {a}')
    # a result whose list never closes would be missed by the pattern above
    opened = len(re.findall(r'depends on axioms:', log))
    n = len(dep) + len(free)
    print('theorems checked:', n)
    for a in sorted(used):
        print(f'{used[a]:7d} {a}')
    ok = True
    if n == 0:
        print('FAIL: no `#print axioms` result in the log')
        ok = False
    if opened != len(dep):
        print(f'FAIL: {opened - len(dep)} results with a list of axioms that could not be read')
        ok = False
    if bad:
        print('OTHER AXIOMS:')
        for b in sorted(set(bad)):
            print('  ' + b)
        ok = False
    if re.search(r"declaration uses 'sorry'|sorryAx", log):
        print("FAIL: the log has a `declaration uses 'sorry'` warning or a sorryAx")
        ok = False
    if len(sys.argv) > 2:
        src = open(sys.argv[2]).read()
        want = len(re.findall(r'^#print axioms ', src, re.M))
        if want != n:
            print(f'FAIL: Test/Axioms.lean has {want} `#print axioms` lines, the log has {n} results')
            ok = False
        else:
            print(f'count matches Test/Axioms.lean: {want}')
        if 'AXIOM SCAN' in src:
            m = re.search(r'AXIOM SCAN OK: [^\n]*', log)
            if m:
                print(m.group(0))
            else:
                print('FAIL: no `AXIOM SCAN OK` line in the log (the scan of every constant)')
                ok = False
    if 'AXIOM SCAN FAILED' in log:
        print('FAIL: AXIOM SCAN FAILED is in the log')
        ok = False
    if ok:
        print('only standard axioms')
    return 0 if ok else 1


sys.exit(main())

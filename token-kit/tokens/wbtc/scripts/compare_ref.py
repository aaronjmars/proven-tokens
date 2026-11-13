#!/usr/bin/env python3
"""Compare the Lean files of a token project of the kit with a reference project that holds its
own copy of the generic files (the layout before the kit: <Root>/Evm/*.lean in the project).

Two changes are expected in every file and are taken off before the comparison:
- an import of a generic file: `import <Root>.Evm.<File>` is now `import TokenKit.Evm.<File>`;
- the line `open TokenKit [TokenKit.<Sub> ...]`, which the files of the kit layout have and the
  reference has not;
- the path of a generic file in a comment: `<Root>/Evm/<File>.lean` is now `TokenKit/Evm/<File>.lean`.

Prints every other difference as a unified diff, and one line per file. Exit code 1 if any file
differs. Usage: compare_ref.py <token project> <reference project> [--quiet]"""
import difflib
import os
import re
import sys


def norm(text, root):
    out = []
    for line in text.split('\n'):
        if re.match(r'open TokenKit( TokenKit\.\w+)*$', line.strip()):
            continue
        line = re.sub(r'^import (%s|TokenKit)\.Evm\.' % re.escape(root), 'import KIT.Evm.', line)
        line = re.sub(r'\b(%s|TokenKit)/Evm/' % re.escape(root), 'KIT/Evm/', line)
        out.append(line)
    return out


def main():
    new, ref = sys.argv[1], sys.argv[2]
    quiet = '--quiet' in sys.argv
    root = [d for d in os.listdir(new) if d.endswith('Verify') and os.path.isdir(os.path.join(new, d))][0]
    files = []
    for base, _, fs in os.walk(os.path.join(new, root)):
        files += [os.path.relpath(os.path.join(base, f), new) for f in fs if f.endswith('.lean')]
    files.append(root + '.lean')
    same = diff = 0
    for f in sorted(files):
        rp = os.path.join(ref, f)
        if not os.path.exists(rp):
            print('NEW   ', f)
            diff += 1
            continue
        a, b = norm(open(rp).read(), root), norm(open(os.path.join(new, f)).read(), root)
        if a == b:
            same += 1
            continue
        diff += 1
        d = list(difflib.unified_diff(a, b, 'ref/' + f, 'kit/' + f, lineterm='', n=0))
        print('DIFF  ', f, '(%d lines)' % sum(1 for x in d if x[:1] in '+-' and x[:3] not in ('+++', '---')))
        if not quiet:
            print('\n'.join(d))
    gone = []
    for base, _, fs in os.walk(os.path.join(ref, root)):
        for f in fs:
            r = os.path.relpath(os.path.join(base, f), ref)
            if f.endswith('.lean') and r not in files and os.sep + 'Evm' + os.sep not in os.sep + r:
                gone.append(r)
    for r in gone:
        print('GONE  ', r)
    print('files: %d same, %d different, %d only in the reference' % (same, diff, len(gone)))
    sys.exit(1 if diff or gone else 0)


main()

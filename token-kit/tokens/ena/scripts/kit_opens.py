#!/usr/bin/env python3
"""Make the Lean files of a token project see the names of the shared library (`TokenKit`).

The generic files used to be a copy inside every project (`<Root>/Evm`, namespace `<Root>`), so a
file in `namespace <Root>.Readable` saw `<Root>.Readable.log3` with no `open`. In the kit they are
in `TokenKit`, so every project file that imports the kit (directly or through project files) gets,
after each `namespace <Root>...` line, one line

    open TokenKit [TokenKit.<Sub> ...]

`TokenKit.<Sub>` is listed for every namespace `<Sub>` of the kit (Readable, Supply, Witness, Safe,
Ro, Complete) that the file can see through its imports and that it enters or opens under the name
`<Root>.<Sub>`. The line goes after the first `open UsdtVerify` that follows the namespace line,
else before the first `open` line, else right after the namespace line. A file with no
namespace of the project (the axioms test) gets the line before its first `open`.

Also `import <Root>.Evm.<File>` becomes `import TokenKit.Evm.<File>` (for a project that still has
the old layout). Nothing else is changed; a second run changes nothing. `regen.sh` runs this after
the generators; run it by hand after adding a hand-written file.

Usage: kit_opens.py <token project>"""
import os
import re
import sys

# local copy (tokens/ena/scripts): the kit is three folders above this folder
KIT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def imports(text):
    return re.findall(r'^import (\S+)', text, flags=re.M)


def kit_spaces(mod, seen):
    """The namespaces `TokenKit.<Sub>` that the kit module `mod` and its imports declare."""
    if mod in seen:
        return seen[mod]
    seen[mod] = set()
    p = os.path.join(KIT, *mod.split('.')) + '.lean'
    if not os.path.exists(p):
        return seen[mod]
    text = open(p).read()
    subs = set()
    for name in re.findall(r'^namespace (\S+)', text, flags=re.M):
        if name.startswith('TokenKit.'):
            subs.add(name.split('.')[1])
        elif name != 'TokenKit':
            subs.add(name.split('.')[0])
    for m in imports(text):
        if m.startswith('TokenKit.'):
            subs |= kit_spaces(m, seen)
    seen[mod] = subs
    return subs


def file_spaces(mod, proj, root, seen, kseen):
    """None when the project module does not import the kit, else the kit namespaces it sees."""
    if mod in seen:
        return seen[mod]
    seen[mod] = None
    p = os.path.join(proj, *mod.split('.')) + '.lean'
    if not os.path.exists(p):
        return None
    got = None
    for m in imports(open(p).read()):
        if m.startswith(root + '.Evm.'):
            m = 'TokenKit' + m[len(root):]
        if m.startswith('TokenKit.'):
            sub = kit_spaces(m, kseen)
        elif m.startswith(root + '.'):
            sub = file_spaces(m, proj, root, seen, kseen)
        else:
            sub = None
        if sub is not None:
            got = (got or set()) | sub
    seen[mod] = got
    return got


def migrate(text, root, spaces):
    text = re.sub(r'^import %s\.Evm\.' % re.escape(root), 'import TokenKit.Evm.', text, flags=re.M)
    if spaces is None:
        return text
    used = set()
    for line in text.split('\n'):
        if line.startswith('namespace ') or line.startswith('open '):
            used |= set(re.findall(r'\b%s\.(\w+)' % re.escape(root), line))
    want = 'open TokenKit' + ''.join(' TokenKit.' + s for s in sorted(spaces & used))
    lines = [l for l in text.split('\n') if not re.match(r'open TokenKit( TokenKit\.\w+)*$', l)]
    if not any(re.match(r'namespace %s(\.|\s|$)' % re.escape(root), l) for l in lines):
        # a file with no namespace of the project (the axioms test): before its first `open`
        k = next((m for m, l in enumerate(lines) if l.startswith('open ')), None)
        if k is not None:
            lines.insert(k, want)
        return '\n'.join(lines)
    out, i = [], 0
    while i < len(lines):
        line = lines[i]
        out.append(line)
        if re.match(r'namespace %s(\.|\s|$)' % re.escape(root), line):
            j, at, first = i + 1, None, None
            while j < len(lines) and (lines[j].strip() == '' or lines[j].startswith('open ')):
                if lines[j].strip() == 'open UsdtVerify' and at is None:
                    at = j
                if lines[j].startswith('open ') and first is None:
                    first = j
                j += 1
            if at is not None:
                out += lines[i + 1:at + 1]
                out.append(want)
                i = at
            elif first is not None:
                out += lines[i + 1:first]
                out.append(want)
                i = first - 1
            else:
                out.append(want)
        i += 1
    return '\n'.join(out)


def main():
    proj = sys.argv[1]
    root = [d for d in sorted(os.listdir(proj))
            if d.endswith('Verify') and os.path.isdir(os.path.join(proj, d))][0]
    n, seen, kseen = 0, {}, {}
    files = [os.path.join(proj, root + '.lean')]
    for base, _, fs in os.walk(os.path.join(proj, root)):
        files += [os.path.join(base, f) for f in sorted(fs) if f.endswith('.lean')]
    for p in files:
        old = open(p).read()
        mod = os.path.relpath(p, proj)[:-5].replace(os.sep, '.')
        new = migrate(old, root, file_spaces(mod, proj, root, seen, kseen))
        if new != old:
            open(p, 'w').write(new)
            n += 1
    print('kit_opens:', proj, ':', n, 'files changed')


main()

"""Shapes of branch conditions, shared by vacuity_scan.py (which finds the branches that the
earlier conditions of a path decide) and by gen_paths.py (`paths.dead_table`, which proves each
such branch with the tactic `dead_omega` of OndoVerify/Ondo/Arith.lean and walks one side only).

A condition is a Lean term as gen_paths.py prints it. Its shape (`canon`) is the term with the
reads of the storage dropped (`readSlot S c k` is `S`) and every subterm that is not arithmetic
(a storage word, a word of the call data, a variable) replaced by `?i`, numbered by first
occurrence. Two conditions with the same shape under one numbering talk about the same words."""
import re

TOK = re.compile(r'\(|\)|[^\s()]+')
ARITH = {'isZero', 'lessThan', 'greaterThan', 'equal', 'bitwiseAnd', 'bitwiseOr', 'bitwiseXor',
         'bitwiseNot', 'add', 'sub', 'mul', 'div', 'signedLessThan', 'signedGreaterThan',
         'bitwiseShl', 'bitwiseShr'}
M96 = (1 << 96) - 1
MAX = (1 << 256) - 1


def parse(s):
    toks = TOK.findall(s)
    pos = 0

    def rd():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t != '(':
            return t
        out = []
        while toks[pos] != ')':
            out.append(rd())
        pos += 1
        return out
    out = []
    while pos < len(toks):
        out.append(rd())
    return out[0] if len(out) == 1 else out


def flat(t):
    return t if isinstance(t, str) else '(' + ' '.join(flat(x) for x in t) + ')'


def num(t):
    """The value of a numeral `(n : U256)`, else None."""
    if isinstance(t, list) and len(t) == 3 and t[1] == ':' and isinstance(t[0], str) and t[0].isdigit():
        return int(t[0])
    return None


def strip(t):
    if isinstance(t, str):
        return t
    t = [strip(x) for x in t]
    if t and t[0] in ('readSlot', 'Named.readSlot') and len(t) == 4:
        return t[1]
    return t


def is_arith(t):
    return isinstance(t, list) and t and isinstance(t[0], str) and t[0] in ARITH


def canon(t, amap):
    """The shape of the stripped term `t`; `amap` (atom text -> number) is extended."""
    if num(t) is not None:
        return str(num(t))
    if is_arith(t):
        return '(' + t[0] + ' ' + ' '.join(canon(x, amap) for x in t[1:]) + ')'
    k = flat(t)
    if k not in amap:
        amap[k] = len(amap)
    return '?%d' % amap[k]


def masked96(t):
    return (is_arith(t) and t[0] == 'bitwiseAnd' and (num(t[1]) == M96 or num(t[2]) == M96))


def helpers(trees):
    """The facts that are not linear, for the terms of `trees` (unstripped): a list of
    ('vest', Y, E, P) for a subterm `div (mul Y E) P` (`P` a numeral below 2^64, `Y` under the
    mask of 96 bits), ('seed', Y, E, P) for `div (mul 2 (div (mul Y E) P)) 3` and ('dmax', Y)
    for `div MAX Y`. One per shape."""
    out, seen = [], set()

    def go(t):
        if not isinstance(t, list):
            return
        for x in t:
            go(x)
        if is_arith(t) and t[0] == 'div':
            a, b = t[1], t[2]
            p = num(b)
            if (p is not None and 0 < p < (1 << 64) and is_arith(a) and a[0] == 'mul'
                    and num(a[1]) is None and masked96(a[1])):
                k = ('vest', flat(strip(a[1])), flat(strip(a[2])), p)
                if k not in seen:
                    seen.add(k)
                    out.append(('vest', flat(a[1]), flat(a[2]), p))
            # two thirds of such a quotient: `div (mul 2 (div (mul Y E) P)) 3`
            if (p == 3 and is_arith(a) and a[0] == 'mul' and num(a[1]) == 2 and is_arith(a[2])
                    and a[2][0] == 'div'):
                q, v = num(a[2][2]), a[2][1]
                if (q is not None and 0 < q < (1 << 64) and is_arith(v) and v[0] == 'mul'
                        and masked96(v[1])):
                    k = ('seed', flat(strip(v[1])), flat(strip(v[2])), q)
                    if k not in seen:
                        seen.add(k)
                        out.append(('seed', flat(v[1]), flat(v[2]), q))
            if num(a) == MAX and masked96(b):
                k = ('dmax', flat(strip(b)))
                if k not in seen:
                    seen.add(k)
                    out.append(('dmax', flat(b)))
    for t in trees:
        go(t)
    return out

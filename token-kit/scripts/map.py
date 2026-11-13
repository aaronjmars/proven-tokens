#!/usr/bin/env python3
"""Print the selector table of the runtime of a token and its jump destinations as Markdown.
The signatures are those of the configuration (`functions`, `readonly_loops` and the optional
list `other_signatures`), checked against the selectors found in the bytecode; a selector with
no known signature prints `?`.

Usage: map.py <config/token.json>"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokenlib  # noqa: E402
from disasm import disasm  # noqa: E402
from keccak import keccak256  # noqa: E402

tok = tokenlib.load()
SIGS = ([f['sig'] for f in tok.cfg['functions']] + [f['sig'] for f in tok.cfg.get('readonly_loops', [])]
        + tok.cfg.get('other_signatures', []))
NAMES = {keccak256(s.encode())[:4].hex(): s for s in SIGS}
done = {f['index'] for f in tok.funcs}
loops = {f['index'] for f in tok.loops}

ins = list(disasm(tok.code))
print("| index | entry pc | selector | signature | destination | covered by |")
print("|---|---|---|---|---|---|")
k = 0
for i in range(len(ins) - 4):
    a, b, c, d, e = ins[i:i + 5]
    if (a[2], b[2], c[2], d[2], e[2]) == ("DUP1", "PUSH4", "EQ", "PUSH2", "JUMPI"):
        how = 'paths' if k in done else 'read-only loop' if k in loops else 'NOT covered'
        print(f"| {k} | {a[0]} | 0x{b[3]} | {NAMES.get(b[3], '?')} | {int(d[3], 16)} (0x{d[3]}) | {how} |")
        k += 1
dests = [pc for pc, op, name, _ in ins if name == "JUMPDEST"]
print()
print(f"Instructions: {len(ins)}; JUMPDESTs at an opcode boundary: {len(dests)}.")

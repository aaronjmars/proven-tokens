"""The per-token configuration shared by the generators.

The generators live in the kit (<kit>/scripts) and write into the project of the token: the
folder that holds config/<token>.json (<kit>/tokens/<token>). The generic Lean files are the
library `TokenKit` of the kit (<kit>/TokenKit/Evm); a generated file imports them as
`TokenKit.Evm.<File>` and opens the namespace `TokenKit`.

Everything about one token comes from one JSON file (config/<token>.json): the path of the
runtime bytecode, the Lean root namespace and folder, the list of functions (name and ABI
signature), the numbers of the hand-written dispatcher lemma, the slot layout and the readable
descriptions. The selector of a function is computed from its signature (keccak256), and its
index and destination in the selector table are read from the bytecode: nothing is typed twice.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from keccak import keccak256  # noqa: E402


class Token:
    def __init__(self, path):
        self.path = os.path.abspath(path)
        self.root_dir = os.path.dirname(os.path.dirname(self.path))
        # the kit: this folder is <kit>/scripts; the shared Lean library is <kit>/TokenKit
        self.kit_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        self.kit_lib = os.path.join(self.kit_dir, 'TokenKit')
        self.cfg = json.load(open(self.path))
        c = self.cfg
        # `min_fork` (ENA: "shapella", for PUSH0): the fork bound of every generated theorem, in
        # place of Berlin. Every generator writes `.berlin <= fork`; with the key, the text of
        # each Lean file is rewritten as it is written (see `fork_open`).
        self.min_fork = c.get('min_fork')
        if self.min_fork:
            install_fork(self.min_fork)
        self.name = c['token']
        self.root = c['lean_root']                 # Lean root namespace, e.g. ShibVerify
        self.dir = c['lean_dir']                   # folder under the root, e.g. Shib
        self.mod = f'{self.root}.{self.dir}'       # module prefix, e.g. ShibVerify.Shib
        self.hex_path = self.abs(c['hex'])
        self.paths_json = self.abs(c['paths_json'])
        os.makedirs(os.path.dirname(self.paths_json), exist_ok=True)
        self.lean_dir = self.abs(os.path.join(self.root, self.dir))
        self.code = bytes.fromhex(open(self.hex_path).read().strip().removeprefix('0x'))
        self.table = self.read_table()             # [(selector, destination)] in table order
        d = c['dispatch']
        # `"mode": "walk"` (optimized code): gen_paths.py walks the dispatcher from pc 0, so there
        # is no price of the prelude or of a table entry to give
        self.walk = d.get('mode') == 'walk'
        # the logic mode (`"paths": {"logic": true}`, implied by the mode `walk`): block lemmas
        # and paths over EthLib's Logic.StepG and completeness over runFrame, for code that runs
        # opcodes outside the simulated set of usdt-verify (SHL, SHR, SLT, SGT, XOR)
        self.logic = bool(c.get('paths', {}).get('logic', self.walk))
        if self.walk:
            self.prelude_gas, self.entry_gas = d.get('prelude_gas', 0), d.get('entry_gas', 0)
        else:
            self.prelude_gas, self.entry_gas = d['prelude_gas'], d['entry_gas']
        self.memory_words = d['memory_words']
        self.funcs = [self.entry(f) for f in c['functions']]
        self.loops = [self.entry(f) for f in c.get('readonly_loops', [])]
        self.slots = c.get('slots', {})
        # optional: a payable fallback (two ways in: short call data, unknown selector), the
        # code after an opcode with no rule (`stops`, `segments`), and whether a successful run
        # says nothing of the size of the call data (`explicit_size`).
        # `stops`, `segments`, `explicit_size` and `"frame": true` on a function each WEAKEN
        # what is generated; the head of gen_paths.py says what each one weakens and where it
        # is used, and kit-status.json (`fix_round.5.switches`) lists them.
        self.fallbacks = c.get('fallbacks', [])
        self.segments = [dict(s, kind='segment') for s in c.get('segments', [])]
        self.stops = c.get('stops', [])
        # `prefix_functions`: functions that only gen_paths.py handles (paths from pc 0 to a
        # stop, with their completeness); the other generators do not see them, and the
        # hand-written files of the token carry them on (USDD: permit, up to its STATICCALL)
        self.prefixes = [self.entry(f) for f in c.get('prefix_functions', [])]
        self.explicit_size = d.get('explicit_size', False)

    def abs(self, p):
        return p if os.path.isabs(p) else os.path.join(self.root_dir, p)

    def read_table(self):
        """The selector table: every DUP1 PUSH4 EQ PUSH2 JUMPI in the bytecode, in order."""
        code, out, pc = self.code, [], 0
        while pc < len(code):
            op = code[pc]
            if (op == 0x80 and code[pc + 1:pc + 2] == b'\x63' and code[pc + 6:pc + 8] == b'\x14\x61'
                    and code[pc + 10:pc + 11] == b'\x57'):
                out.append((int.from_bytes(code[pc + 2:pc + 6], 'big'),
                            int.from_bytes(code[pc + 8:pc + 10], 'big')))
                pc += 11
                continue
            pc += 1 + (op - 0x5f if 0x60 <= op <= 0x7f else 0)
        return out

    def entry(self, f):
        """(name, selector, table index, destination, entry gas) of a function of the config."""
        sel = int.from_bytes(keccak256(f['sig'].encode())[:4], 'big')
        idx = [i for i, (s, _) in enumerate(self.table) if s == sel]
        if len(idx) != 1:
            raise SystemExit(f'{f["sig"]}: selector 0x{sel:08x} is not once in the table')
        i = idx[0]
        return dict(f, selector=sel, index=i, dest=self.table[i][1],
                    entry_cost=self.prelude_gas + self.entry_gas * (i + 1))


def load(argv=None):
    argv = sys.argv if argv is None else argv
    if len(argv) < 2:
        raise SystemExit(f'usage: {os.path.basename(argv[0])} <config/token.json>')
    return Token(argv[1])


def install_fork(fork):
    """`min_fork`: from now on, a Lean file that a generator writes gets the hypothesis
    `.<fork> <= fork` in place of `.berlin <= fork` and `from <Fork>` in place of `from Berlin`
    in its doc text. A rule of the library that asks for Berlin gets `(toBerlin hfork)` from the
    generator itself (gen_paths.py, gen_loops.py)."""
    import builtins
    real = builtins.open
    cap = fork[0].upper() + fork[1:]

    class Out:
        def __init__(self, f):
            self.f = f

        def write(self, text):
            return self.f.write(text.replace('.berlin \u2264 fork', '.%s \u2264 fork' % fork)
                                .replace('rom Berlin', 'rom %s' % cap))

        def __enter__(self):
            return self

        def __exit__(self, *a):
            self.f.close()

        def __getattr__(self, name):
            return getattr(self.f, name)

    def fork_open(path, mode='r', *a, **k):
        f = real(path, mode, *a, **k)
        if 'w' in mode and 'b' not in mode and str(path).endswith('.lean'):
            return Out(f)
        return f
    builtins.open = fork_open

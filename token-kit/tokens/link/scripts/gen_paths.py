#!/usr/bin/env python3
"""Generate the Lean proofs of every path of the functions of a token from its runtime bytecode.

The script runs the bytecode symbolically from each function entry. It cuts the code into
blocks (straight-line runs of instructions), states one lemma per block over the opcode rules,
and one theorem per path (entry to RETURN, STOP, REVERT, INVALID or a stuck SSTORE) that chains the lemmas.
It also emits the completeness theorem of each function: a case split on every JUMPI condition.

Nothing the script computes is trusted: Lean checks every lemma against `CODE`.

A branch whose condition is, as a term, the condition of an earlier branch of the same path is
not a new case: the earlier hypothesis decides it. The script follows the decided side only, so
it never states a path whose conditions contradict each other (`pruned` in paths.json counts
these branches). With `"paths": {"decide_equivalent": true}` in the configuration, a condition
that equals an earlier one after ISZERO pairs and reads of slots are taken off is decided too
(the macro `decided_by` of Evm/Rules.lean proves it from the earlier hypothesis).

Options of the configuration (all optional; without them the output is what it was):

- `dispatch.memory_words`: the third word is the free memory pointer after the prelude (128, or
  96 for Solidity before 0.4.22); the word a function returns or logs is written there.
- `dispatch.min_size`: the least size of the call data in the hypothesis `hsize` of `enter`
  (default 4), and `dispatch.size_proof`: the line of `ok_<fn>` that proves it.
- `prune: "normalized"`: a branch is also decided by an earlier branch when the two conditions
  are the same up to ISZERO chains, GT against LT with the operands swapped, and reads of the
  state (`decided`, TokenKit/Evm/Prune.lean).
- `dead_branches`: branches that no run takes for a reason that is not syntactic (the second
  check of a SafeMath add). Each names a function, the pc of the block, which visit of that
  block on the path, the side that runs, and the tactic that proves the side from the earlier
  conditions. `paths_imports` lists the modules that hold those tactics.
- `paths.dead_rules`: a list of rules that decide a branch from its shape alone, with a tactic
  of TokenKit/Evm/Opt06.lean (`sub_after_ge`: the check of a SafeMath sub after an explicit
  `require` on the same word; `caller_mask`: the caller against its own masked word). The side
  that no run takes is not walked, so no path with contradictory conditions is stated.
- a function with `"frame": true` may reach a CALL: its path stops there, as a theorem to the
  frame before the CALL (`<fn>_p<i>` of kind `frame`), and no `ok_<fn>` is generated.
  WEAKENS: this is the one switch that drops a completeness theorem. For such a function there
  is no generated statement that every successful run is one of the listed paths, no generated
  invariant theorem (gen_supply.py leaves its selector as a hypothesis of `supply_preserved`)
  and no generated witness (gen_sanity.py). The configuration must name the hand-written
  theorems that take their place (`frame_theorems`, checked by gen_axioms.py). Used by: BNB
  `withdrawEther` (hand-written Bnb/Withdraw.lean, Bnb/Seq.lean, Bnb/Sanity/Withdraw.lean).
- `stops` (a list of pcs) and `segments`: the path of a function ends at the frame of a listed
  pc (an opcode with no rule here: BALANCE, CALL) as a theorem of kind `at`, and a segment
  starts again after it. WEAKENS: `ok_<fn>` of such a function says that a successful run
  REACHES the middle frame, not how it ends; the generated invariant file leaves the function
  out (gen_solvent.py prints its name) and the proof across the opcode is hand-written. A
  segment that starts in the middle takes what the frame holds there as hypotheses (for WETH:
  `hstatic` on `ok_withdrawTail`). Used by: WETH `totalSupply` (BALANCE at pc 1648) and
  `withdraw` (CALL at pc 2724), hand-written Weth/Balance.lean and Weth/Withdraw.lean.
- `dispatch.explicit_size`: WEAKENS: every per-function theorem takes the hypothesis
  `hsize : 4 <= message.data.size` instead of proving it from the run (with a payable fallback a
  successful run says nothing of the size of the call data). It is closed at the top: the
  fallback theorems cover the runs with less than 4 bytes. Used by: WETH.

- `dispatch.mode: "walk"` (code compiled with the optimizer): there is no hand-written `enter`
  lemma. The path of a function starts at pc 0 with an empty stack and an empty memory and runs
  through the dispatcher like any other code: the call value check is a branch of the path, and
  the comparisons of the selector (GT, EQ) and of the size of the call data are decided by the
  hypotheses `hsel` and `hsize` (a `have` in the path theorem). A return address that a caller
  pushes is a numeral of the path stack, so a block shared by several functions gets one lemma
  per return address and a JUMP to a word of the stack is a JUMP to a numeral. The fallbacks
  (`fallbacks` of kind `value`, `short`, `other`) are walked from pc 0 too; the completeness of
  the dispatcher (Complete/Dispatch.lean, gen_dispatch.py) is proved from their `ok_` theorems.
- `paths.raw_memory: "across_blocks"`: a memory with a write that is not aligned (a revert
  string: `Error(string)` after the 4 bytes of its selector) may cross a block boundary. The
  next block lemma then takes the memory as a variable with its size (`hms`) and, when it is
  still known, the word at 64 (`hfp`). Without the option such a boundary stops the generator.

Opcodes added for optimized code (no finished token has them, so their files do not change):
SHL, SHR, SLT, SGT, OR, XOR (rule `bin3K`, TokenKit/Evm/Opt.lean), LOG3 of no bytes (`log3ZK`),
and `SHR 224` of the first word of the call data, folded to the selector (`shr_selector`).

Everything about the token comes from the configuration file (scripts/tokenlib.py).

Usage: gen_paths.py <config/token.json> [function,function...]
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tokenlib  # noqa: E402

M256 = 1 << 256
TGT = ('v', 'message.currentTarget')

# ---------------------------------------------------------------- terms


def C(n):
    return ('c', n % M256)


def V(s):
    return ('v', s)


def A(f, *args):
    return ('a', f, tuple(args))


def isc(t):
    return t[0] == 'c'


def pr(t):
    if t[0] == 'c':
        return f'({t[1]} : U256)'
    if t[0] == 'v':
        return t[1]
    if t[0] == 'l':
        return '[' + ', '.join(pr(a) for a in t[1]) + ']'
    return '(' + t[1] + ' ' + ' '.join(pr(a) for a in t[2]) + ')'


def subst(t, m):
    if t[0] == 'c':
        return t
    if t[0] == 'v':
        return m.get(t[1], t)
    if t[0] == 'l':
        return ('l', tuple(subst(a, m) for a in t[1]))
    return ('a', t[1], tuple(subst(a, m) for a in t[2]))


def strip_reads(t):
    """The term with every `storageAt (readSlot S ..) ..` read from `S`."""
    if t[0] == 'l':
        return ('l', tuple(strip_reads(a) for a in t[1]))
    if t[0] != 'a':
        return t
    if t[1] == 'storageAt':
        s0 = t[2][0]
        while s0[0] == 'a' and s0[1] == 'readSlot':
            s0 = s0[2][0]
        return A('storageAt', strip_reads(s0), *[strip_reads(x) for x in t[2][1:]])
    return A(t[1], *[strip_reads(x) for x in t[2]])


def swap_gt(t):
    if t[0] == 'l':
        return ('l', tuple(swap_gt(a) for a in t[1]))
    if t[0] != 'a':
        return t
    args = [swap_gt(x) for x in t[2]]
    if t[1] == 'greaterThan':
        return A('lessThan', args[1], args[0])
    return A(t[1], *args)


def norm(c):
    """(atom, flip): `c ≠ 0` holds exactly when `atom ≠ 0` does, negated if `flip`."""
    flip = False
    while c[0] == 'a' and c[1] == 'isZero':
        c = c[2][0]
        flip = not flip
    return swap_gt(strip_reads(c)), flip


BIN = {
    0x01: ('add', 'instruction_add', lambda a, b: a + b),
    0x02: ('mul', '(instruction_of_stackOnlyStep rfl)', lambda a, b: a * b),
    0x03: ('sub', 'instruction_sub', lambda a, b: a - b),
    0x04: ('div', '(instruction_of_stackOnlyStep rfl)', lambda a, b: 0 if b == 0 else a // b),
    0x10: ('lessThan', '(instruction_of_stackOnlyStep rfl)', lambda a, b: int(a < b)),
    0x11: ('greaterThan', '(instruction_of_stackOnlyStep rfl)', lambda a, b: int(a > b)),
    0x14: ('equal', 'instruction_eq', lambda a, b: int(a == b)),
    0x16: ('bitwiseAnd', '(instruction_of_stackOnlyStep rfl)', lambda a, b: a & b),
}
def _signed(a):
    return a - M256 if a >= 1 << 255 else a


# opcodes of optimized code: the rule `bin3K` (TokenKit/Evm/Opt.lean), which takes `hfork`
BIN3 = {
    0x12: ('signedLessThan', lambda a, b: int(_signed(a) < _signed(b))),
    0x13: ('signedGreaterThan', lambda a, b: int(_signed(a) > _signed(b))),
    0x17: ('bitwiseOr', lambda a, b: a | b),
    0x18: ('bitwiseXor', lambda a, b: a ^ b),
    0x1b: ('bitwiseShl', lambda a, b: (b << a) % M256 if a < 256 else 0),
    0x1c: ('bitwiseShr', lambda a, b: b >> a if a < 256 else 0),
}
SELT = ('v', '(BitVec.ofNat 256 (selector message.data))')
UN = {
    0x15: ('isZero', 'instruction_iszero', lambda a: int(a == 0)),
    0x19: ('bitwiseNot', '(instruction_of_stackOnlyStep rfl)', lambda a: M256 - 1 - a),
}


def memcost(size):
    w = size // 32
    return 3 * w + w * w // 512


def ext(size, o, k):
    """(cost, expandBy) of extendMemory size [(o, k)]."""
    if k == 0:
        return 0, 0
    before = (size + 31) // 32 * 32
    after = (o + k + 31) // 32 * 32
    if after <= before:
        return 0, 0
    return memcost(after) - memcost(before), after - before


# ---------------------------------------------------------------- code

def load(code):
    ins = {}
    pc = 0
    while pc < len(code):
        op = code[pc]
        if 0x60 <= op <= 0x7f:
            n = op - 0x5f
            ins[pc] = (op, int.from_bytes(code[pc + 1:pc + 1 + n], 'big'), n)
            pc += 1 + n
        else:
            ins[pc] = (op, None, 0)
            pc += 1
    return code, ins


def norm_cond(t, taken):
    """(core, nonzero): `t != 0` (taken) or `t = 0` as a fact about a term that is no ISZERO."""
    t = strip_reads(t)
    while t[0] == 'a' and t[1] == 'isZero':
        t, taken = t[2][0], not taken
    return t, taken


def decided(t):
    """The value of a condition that EQ of a word with itself decides (ISZERO over it), or None."""
    if t[0] == 'c':
        return t[1]
    if t[0] == 'a' and t[1] == 'equal' and t[2][0] == t[2][1]:
        return 1
    if t[0] == 'a' and t[1] == 'isZero':
        v = decided(t[2][0])
        return None if v is None else int(v == 0)
    return None


def mentions(t, x):
    if t == x:
        return True
    if t[0] == 'a':
        return any(mentions(a, x) for a in t[2])
    if t[0] == 'l':
        return any(mentions(a, x) for a in t[1])
    return False


def evalc(t):
    """The value of a closed term over the stack opcodes, or None."""
    if t[0] == 'c':
        return t[1]
    if t[0] != 'a':
        return None
    vs = [evalc(a) for a in t[2]]
    if any(v is None for v in vs):
        return None
    for tab in (BIN, UN):
        for (f, _, ev) in tab.values():
            if f == t[1]:
                return ev(*vs) % M256
    for (f, ev) in BIN3.values():
        if f == t[1]:
            return ev(*vs) % M256
    return None


class NeedDir(Exception):
    pass


class Fatal(Exception):
    pass


MAXLEN = 30


def hacc_proof(st):
    if st == V('state'):
        return 'hacc'
    if st[0] == 'a' and st[1] == 'readSlot':
        return f'(hasAccount_readSlot {hacc_proof(st[2][0])})'
    if st[0] == 'a' and st[1] == 'writeSlot':
        return f'(hasAccount_writeSlot {hacc_proof(st[2][0])})'
    raise Fatal('state shape ' + pr(st))


def hbad_proof(st):
    if st == V('state'):
        return 'hbad'
    if st[0] == 'a' and st[1] == 'readSlot':
        return f'(bad_readSlot {hbad_proof(st[2][0])})'
    raise Fatal('bad after a write ' + pr(st))


class Block:
    """One run of a block from `pc` on the path state; builds the lemma text."""

    RET = 128          # the free memory pointer after the prelude: where the code writes a word
    FRAME = False      # stop the path at a CALL
    NAMED = False      # `paths.memory_lemmas = "named"`: the lemmas named after the offset
                       # (memW_ext96, memW_write96, memW_read96, size_memW4) where they apply
    RAWX = False       # `paths.raw_memory = "across_blocks"`: a raw memory may cross a boundary
    LOGIC = False      # the logic mode: the lemmas are over EthLib's Logic.StepG
    RAWW = False       # `paths.raw_words = true`: a raw memory keeps the words it is known to
                       # hold (offset -> value, proof); reads, hashes and logs of a raw memory

    def named_word(self, o, nw):
        """Whether the read of the last word, at `o`, of a memory of `nw` words has a named
        lemma `memW_read<o>`: the SHIB shape (128, five words) always, the shape of the free
        memory pointer in the named mode."""
        if (o, nw) == (128, 5):
            return True
        return self.NAMED and o == self.RET and nw == self.RET // 32 + 1

    def __init__(self, ins, pc, pstack, pmem, direction=None, bad=False, stops=frozenset()):
        self.ins, self.pc0, self.pstack, self.pmem = ins, pc, pstack, pmem
        self.stops = stops
        self.direction, self.bad = direction, bad
        self.stack, self.in_terms = [], []
        self.mem = None            # None (untouched) | ['W', [terms]] | ['R', term, size, szp, fpp, fpv]
        self.mem_in = None
        self.raw_in = None         # (size, fpv or None) when the block reads a raw memory it got
        self.words_in = {}         # offset -> value: the known words of the raw memory it got
        self.state, self.sub = V('state'), V('substate')
        self.cconst, self.cterms = 0, []
        self.needs = set()
        self.lines = []
        self.cond = None           # (term, taken) for a JUMPI on a condition that is no numeral
        self.end = None            # ('at', pc) | ('halt', rev, outstr) | ('stuck',)
        self.has_sstore = False
        self.pushes = False
        self.run()

    # stack
    def need(self, n):
        while len(self.stack) < n:
            i = len(self.in_terms)
            if i >= len(self.pstack):
                raise Fatal(f'stack underflow at block {self.pc0}')
            p = self.pstack[i]
            t = p if isc(p) else V(f'x{i}')
            self.stack.append(t)
            self.in_terms.append(t)

    def pop(self):
        self.need(1)
        return self.stack.pop(0)

    def push(self, t):
        self.stack.insert(0, t)

    def const(self, t, what):
        if not isc(t):
            raise Fatal(f'{what} is no numeral at block {self.pc0}: {pr(t)}')
        return t[1]

    # memory
    def touch(self):
        if self.mem is None and isinstance(self.pmem, dict):
            # a raw memory from the block before: a variable with its size and its word at 64
            fpv = self.pmem['fpv']
            if fpv is not None and not isc(fpv):
                fpv = V('mfp')
            self.raw_in = (self.pmem['size'], fpv)
            words = {}
            for o, (v, _) in sorted(self.pmem.get('words', {}).items()):
                v = v if isc(v) else V(f'mw{o}')
                self.words_in[o] = v
                words[o] = (v, f'hw{o}')
            self.mem = ['R', V('mem'), self.pmem['size'], 'hms',
                        None if fpv is None else 'hfp', fpv, words]
            return
        if self.mem is None:
            ws = [p if isc(p) else V(f'm{i}') for i, p in enumerate(self.pmem)]
            self.mem = ['W', ws]
            self.mem_in = list(ws)

    def mem_term(self):
        if self.mem is None:
            return 'mem'
        return pr(self.mem_tree())

    def mem_tree(self):
        if self.mem[0] == 'W':
            return A('memW', ('l', tuple(self.mem[1])))
        return self.mem[1]

    def szp(self):
        if self.mem[0] == 'W':
            n = len(self.mem[1])
            if n not in (3, 5) and not (self.NAMED and n == 4):
                return f'(size_memWn (n := {32 * n}) _ rfl)', 32 * n
            return f'(size_memW{n} ' + ' '.join('_' * n) + ')', 32 * n
        return self.mem[3], self.mem[2]

    def to_raw(self):
        if self.mem[0] == 'W':
            ws = self.mem[1]
            if len(ws) < 3:
                raise Fatal('raw memory from a short memory')
            p, size = self.szp()
            words = {}
            if self.RAWW:
                words = {32 * i: (w, f'(memW_load {i} (by rfl) (by rfl) (by rfl))')
                         for i, w in enumerate(ws) if i != 2}
            self.mem = ['R', self.mem_tree(), size, p, '(memW_load64 ' + ' '.join('_' * 4) + ')', ws[2],
                        words]

    def gas(self):
        if not self.cterms:
            return str(self.cconst)
        return '(' + ' + '.join([str(self.cconst)] + [pr(t) for t in self.cterms]) + ')'

    def L(self, s):
        self.lines.append(s)

    def run(self):
        ins = self.ins
        pc = self.pc0
        count = 0
        CF = '(by code_fact) (by code_fact)'
        while True:
            op, arg, n = ins[pc]
            raw = self.mem is not None and self.mem[0] == 'R'
            if count > 0 and (op == 0x5b or pc in self.stops or (count >= MAXLEN and not raw)):
                if raw and not self.RAWX:
                    raise Fatal(f'block boundary at {pc} with a revert string in memory')
                self.end = ('at', pc)
                return
            count += 1
            if 0x60 <= op <= 0x7f:
                self.L(f'step pushR {n} ({arg} : U256)')
                self.L(f'at_pc {pc + 1 + n}')
                self.push(C(arg))
                self.cconst += 3
                self.pushes = True
            elif 0x80 <= op <= 0x8f:
                k = op - 0x7f
                self.need(k)
                self.L(f'step dupR {k - 1}')
                self.push(self.stack[k - 1])
                self.cconst += 3
                self.pushes = True
            elif 0x90 <= op <= 0x9f:
                k = op - 0x8f
                self.need(k + 1)
                self.L(f'step swap{k}K {CF} (by gas_ok)')
                self.stack[0], self.stack[k] = self.stack[k], self.stack[0]
                self.cconst += 3
            elif op in BIN:
                f, lem, ev = BIN[op]
                a, b = self.pop(), self.pop()
                self.L(f'step binR 0x{op:02x} {lem}')
                cost = 5 if op in (0x02, 0x04) else 3
                self.cconst += cost
                if isc(a) and isc(b):
                    r = C(ev(a[1], b[1]))
                    self.L(f'step foldK (y := {pr(r)}) (by decide +kernel)')
                elif op == 0x16 and {a, b} == {C(0xffffffff), A(
                        'div', V('(loadWord message.data 0 32)'), C(1 << 224))}:
                    # LINK local (solc 0.4): the selector is the first word of the call data
                    # divided by 2^224 and masked to 32 bits
                    r = SELT
                    lem = 'and_div_selector' if a == C(0xffffffff) else 'div_and_selector'
                    self.L(f'step foldK (y := {pr(r)}) ({lem} _)')
                else:
                    r = A(f, a, b)
                self.push(r)
            elif op in BIN3:
                f, ev = BIN3[op]
                a, b = self.pop(), self.pop()
                self.needs.add('hfork')
                if self.LOGIC:
                    self.L(f'step bin3L {CF} (byte := 0x{op:02x}) rfl (Nat.le_trans (by decide) '
                           f'hfork) (instruction_of_stackOnlyStep rfl) rfl (by gas_ok)')
                elif op == 0x17:
                    self.L(f'step bin3K {CF} (byte := 0x{op:02x}) rfl (Nat.le_trans (by decide) '
                           f'hfork) (instruction_of_stackOnlyStep rfl) rfl (by decide) (by gas_ok)')
                else:
                    raise Fatal(f'opcode 0x{op:02x} at {pc} is outside the simulated set: '
                                f'set paths.logic')
                self.cconst += 3
                if isc(a) and isc(b):
                    r = C(ev(a[1], b[1]))
                    self.L(f'step foldK (y := {pr(r)}) (by decide +kernel)')
                elif op == 0x1c and a == C(224) and b == V('(loadWord message.data 0 32)'):
                    # the selector: the first word of the call data shifted right by 224 bits
                    r = SELT
                    self.L(f'step foldK (y := {pr(r)}) (shr_selector _)')
                else:
                    r = A(f, a, b)
                self.push(r)
            elif op in UN:
                f, lem, ev = UN[op]
                a = self.pop()
                self.L(f'step unR 0x{op:02x} {lem}')
                self.cconst += 3
                if isc(a):
                    r = C(ev(a[1]))
                    self.L(f'step foldK (y := {pr(r)}) (by decide +kernel)')
                else:
                    r = A(f, a)
                self.push(r)
            elif op == 0x0a:
                a, b = self.pop(), self.pop()
                e = self.const(b, 'exponent')
                eb = (e.bit_length() + 7) // 8
                self.needs.add('hfork')
                self.L(f'step expK hfork {CF} (e := {eb}) (by decide +kernel) (by gas_ok)')
                self.cconst += 10 + 50 * eb
                if isc(a):
                    r = C(pow(a[1], e, M256))
                    self.L(f'step foldK (y := {pr(r)}) (by decide +kernel)')
                else:
                    r = A('Evm.exp', a, b)
                self.push(r)
            elif op == 0x50:
                self.pop()
                self.L('step popR')
                self.cconst += 2
            elif op == 0x5b:
                self.L('step jumpdestR')
                self.cconst += 1
            elif op == 0x33:
                self.L(f'step Gas.callerG {CF} (by gas_ok) (by stk_ok)')
                self.push(V('message.caller.toU256'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x42 and self.RAWW and self.LOGIC:
                self.L(f'step timestampL {CF} (by gas_ok) (by stk_ok)')
                self.push(V('message.blockEnv.timestamp'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x46 and self.LOGIC:
                # CHAINID (USDE local rule `chainidL`, UsdeVerify/Usde/Lib.lean)
                self.needs.add('hfork')
                self.L(f'step chainidL hfork {CF} (by gas_ok) (by stk_ok)')
                self.push(V('(BitVec.ofNat 256 message.blockEnv.chainId.toNat)'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x30 and self.LOGIC:
                # ADDRESS (`addressL`, TokenKit/Evm/Logic.lean)
                self.L(f'step addressL {CF} (by gas_ok) (by stk_ok)')
                self.push(V('message.currentTarget.toU256'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x34:
                self.L(f'step Gas.callvalueG {CF} (by gas_ok) (by stk_ok)')
                self.push(V('message.value'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x36:
                self.L(f'step Gas.calldatasizeG {CF} (by gas_ok) (by stk_ok)')
                self.push(V('(BitVec.ofNat 256 message.data.size)'))
                self.cconst += 2
                self.pushes = True
            elif op == 0x35:
                o = self.const(self.pop(), 'calldata offset')
                self.L(f'step calldataloadK {CF} (o := {o}) (by decide +kernel) (by gas_ok)')
                self.push(V(f'(loadWord message.data {o} 32)'))
                self.cconst += 3
            elif op == 0x51:
                o = self.const(self.pop(), 'MLOAD offset')
                self.touch()
                p, size = self.szp()
                if self.mem[0] == 'W' and (o != 64 or len(self.mem[1]) < 3):
                    # any aligned word inside a memory of words
                    if o % 32 or o // 32 >= len(self.mem[1]):
                        raise Fatal(f'MLOAD at {o}, pc {pc}')
                    v = self.mem[1][o // 32]
                    self.L(f'step mloadK {CF} {p} (o := {o}) (by decide +kernel) (by decide) '
                           f'(memW_load {o // 32} rfl rfl rfl) (by gas_ok)')
                    self.push(v)
                    self.cconst += 3
                    pc += 1 + n
                    continue
                if o != 64 and self.mem[0] == 'R' and o in self.mem[6]:
                    # a known word of a raw memory
                    v, hv = self.mem[6][o]
                    self.L(f'step mloadK {CF} {p} (o := {o}) (by decide +kernel) (by decide) {hv} (by gas_ok)')
                    self.push(v)
                    self.cconst += 3
                    pc += 1 + n
                    continue
                if o != 64:
                    raise Fatal(f'MLOAD at {o}, pc {pc}')
                if self.mem[0] == 'W':
                    v = self.mem[1][2]
                    hv = '(memW_load64 ' + ' '.join('_' * 4) + ')'
                else:
                    v, hv = self.mem[5], self.mem[4]
                    if hv is None:
                        raise Fatal('free pointer lost')
                self.L(f'step mloadK {CF} {p} (o := 64) (by decide +kernel) (by decide) {hv} (by gas_ok)')
                self.push(v)
                self.cconst += 3
            elif op == 0x52:
                o = self.const(self.pop(), 'MSTORE offset')
                v = self.pop()
                self.touch()
                p, size = self.szp()
                c, grow = ext(size, o, 32)
                hm = None
                if self.mem[0] == 'W':
                    ws = self.mem[1]
                    if o == 0:
                        hm, ws2 = '(memW_write0 _ _ _)', [v] + ws[1:]
                    elif o == 32:
                        hm, ws2 = '(memW_write32 _ _ _ _)', [ws[0], v] + ws[2:]
                    elif o == 128 and len(ws) == 3:
                        hm, ws2 = '(memW_ext128 _ _ _ _)', ws + [C(0), v]
                    elif o == 128 and len(ws) == 5:
                        hm, ws2 = '(memW_write128 _ _ _ _ _ _)', ws[:4] + [v]
                    elif self.NAMED and o == self.RET and len(ws) == 3:
                        hm = f'(memW_ext{self.RET} _ _ _ _)'
                        ws2 = ws + [C(0)] * (self.RET // 32 - 3) + [v]
                    elif self.NAMED and o == self.RET and len(ws) == self.RET // 32 + 1:
                        hm = f'(memW_write{self.RET} ' + ' '.join('_' * (len(ws) + 1)) + ')'
                        ws2 = ws[:-1] + [v]
                    elif o % 32 == 0 and o <= 32 * 64:
                        # any aligned word: set the word number o / 32, zero words up to it
                        i = o // 32
                        ws2 = ws + [C(0)] * (i + 1 - len(ws))
                        ws2[i] = v
                        hm = f'(memW_set {i} rfl rfl rfl rfl)'
                if hm is not None:
                    self.mem = ['W', ws2]
                else:
                    self.to_raw()
                    _, base, size, p, fpp, fpv, words = self.mem
                    term = A('memoryWrite', A('memoryExtend', base, V(str(grow))), V(str(o)),
                             A('wordBytes', v))
                    szp2 = f'(size_rawW {p} (by decide))'
                    fp2 = None
                    if fpp is not None and o >= 96:
                        fp2 = f'(load64_rawW {fpp} {p} (by decide) (by decide) (by decide))'
                    words2 = {}
                    if self.RAWW:
                        keep = lambda pa: (f'(load_rawW {pa} {p} (by decide) (by decide) '
                                           f'(by decide))')
                        self_ = f'(load_rawW_self {p} (by decide))'
                        if o == 64:
                            fp2, fpv = self_, v
                        elif fpp is not None and o + 32 <= 64:
                            fp2 = keep(fpp)
                        for a, (va, pa) in words.items():
                            if a + 32 <= o or o + 32 <= a:
                                words2[a] = (va, keep(pa))
                        if o != 64:
                            words2[o] = (v, self_)
                    self.mem = ['R', term, size + grow, szp2, fp2, fpv, words2]
                    hm = 'rfl'
                self.L(f'step mstoreK {CF} {p} (c := {c}) (n := {grow}) (by decide +kernel) '
                       f'(o := {o}) (by decide +kernel) {hm} (by gas_ok)')
                self.cconst += 3 + c
            elif op == 0x20:
                o = self.const(self.pop(), 'SHA3 offset')
                k = self.const(self.pop(), 'SHA3 size')
                self.touch()
                if self.RAWW and ((o, k) != (0, 64) or self.mem[0] != 'W'):
                    p, size = self.szp()
                    if o + k > size or k == 0:
                        raise Fatal(f'SHA3 {o} {k} at {pc}: outside the memory')
                    kc = 30 + 6 * ((k + 31) // 32)
                    dk = '(by first | decide +kernel | rfl)'
                    side = (f'{CF} {p} (o := {o}) {dk} (k := {k}) '
                            f'{dk} (by decide) (c := {kc}) (by decide +kernel)')
                    if self.mem[0] == 'W':
                        ws = self.mem[1]
                        if o % 32 or k % 32:
                            raise Fatal(f'SHA3 {o} {k} at {pc}: not on words')
                        # the hash of whole words of a memory of words
                        out = ws[o // 32:(o + k) // 32]
                        outl = '[' + ', '.join(pr(w) for w in out) + ']'
                        self.L(f'step keccakK {side} (memW_readWords (out := {outl}) {o // 32} '
                               f'rfl rfl rfl rfl) (by gas_ok)')
                        self.push(A('keccak', A('memW', ('l', tuple(out)))))
                    elif (o, k) == (0, 64) and 0 in self.mem[6] and 32 in self.mem[6]:
                        # the slot of a mapping entry, from the two known words of a raw memory
                        (a, pa), (b_, pb) = self.mem[6][0], self.mem[6][32]
                        self.L(f'step keccakMapK {CF} {p} (by decide) (read0_raw {pa} {pb} {p} '
                               f'(by decide)) (by gas_ok)')
                        self.push(A('mapSlot', a, b_))
                    else:
                        # the hash of bytes of a raw memory, as a term over that memory
                        self.L(f'step keccakK {side} rfl (by gas_ok)')
                        self.push(A('keccak', A('memoryReadBytes', self.mem[1], V(str(o)),
                                                V(str(k)))))
                    self.cconst += kc
                    pc += 1 + n
                    continue
                if (o, k) != (0, 64) or self.mem[0] != 'W':
                    raise Fatal(f'SHA3 {o} {k} at {pc}')
                p, size = self.szp()
                ws = self.mem[1]
                self.L(f'step keccakMapK {CF} {p} (by decide) (memW_read0 _ _ _) (by gas_ok)')
                self.push(A('mapSlot', ws[0], ws[1]))
                self.cconst += 42
            elif op == 0x54:
                key = self.pop()
                self.needs.add('hfork')
                self.L(f'step sloadK hfork {CF} (by gas_ok)')
                self.push(A('storageAt', self.state, TGT, key))
                self.cterms.append(A('slotCost', A('coldIn', self.sub, TGT, key)))
                self.state = A('readSlot', self.state, TGT, key)
                self.sub = A('accessSlot', self.sub, TGT, key)
            elif op == 0x55:
                key, new = self.pop(), self.pop()
                if self.bad is True:
                    self.L(f'exact Gas.sstoreStuckW {CF} {hbad_proof(self.state)}')
                    self.end = ('stuck',)
                    return
                self.has_sstore = True
                self.needs |= {'hfork', 'hstatic', 'hacc'}
                self.L(f'step sstoreK hfork {CF} hstatic {hacc_proof(self.state)} (by gas_ok) (by gas_ok)')
                orig = A('originalAt', self.state, TGT, key)
                cur = A('storageAt', self.state, TGT, key)
                self.cterms.append(A('Gas.writeCost', V('fork'), orig, cur, new,
                                     A('coldIn', self.sub, TGT, key)))
                self.sub = A('storeSub', V('fork'), self.sub, TGT, key, orig, cur, new)
                self.state = A('writeSlot', self.state, TGT, key, new)
            elif op in (0xa2, 0xa3) and self.bad == 'log':
                # the variant of a block for a static frame: its first LOG fails
                self.L(f'exact logStaticStuck (byte := 0x{op:02x}) (n := {op - 0xa0}) {CF} rfl (by decide) hbad')
                self.end = ('stuck',)
                return
            elif op in (0xa2, 0xa3):
                nt = op - 0xa0
                o = self.const(self.pop(), 'LOG offset')
                k = self.const(self.pop(), 'LOG size')
                ts = [self.pop() for _ in range(nt)]
                if k == 0 and nt == 3:
                    # no data: any offset, any memory
                    self.needs.add('hstatic')
                    self.L(f'step log3ZK {CF} hstatic (by gas_ok)')
                    self.sub = A('logSub', self.sub, TGT, *ts, V('ByteArray.empty'))
                    self.cconst += 1500
                    pc += 1 + n
                    continue
                self.touch()
                if self.mem[0] == 'R' and k == 32 and (o in self.mem[6] or (
                        self.RAWW and o == 64 and self.mem[4] is not None)):
                    # one known word of a raw memory
                    v, pa = self.mem[6][o] if o != 64 else (self.mem[5], self.mem[4])
                    p, size = self.szp()
                    self.needs.add('hstatic')
                    c = 375 + 375 * nt + 8 * 32
                    self.L(f'step log{nt}K {CF} hstatic {p} (o := {o}) (by decide +kernel) (k := 32) '
                           f'(by decide +kernel) (by decide) (c := {c}) (by decide +kernel) '
                           f'(readWord_raw {pa} {p} (by decide)) (by gas_ok)')
                    self.sub = A('logSub' if nt == 3 else f'logSub{nt}', self.sub, TGT, *ts,
                                 A('wordBytes', v))
                    self.cconst += c
                    pc += 1 + n
                    continue
                if self.mem[0] != 'W' or k != 32 or o % 32 or o // 32 >= len(self.mem[1]):
                    raise Fatal(f'LOG{nt} {o} {k} at {pc}')
                nw = len(self.mem[1])
                if self.named_word(o, nw):
                    hd = f'(memW_read{o} ' + ' '.join('_' * nw) + ')'
                else:
                    hd = f'(memW_readWord {o // 32} rfl rfl rfl)'
                p, size = self.szp()
                self.needs.add('hstatic')
                c = 375 + 375 * nt + 8 * 32
                self.L(f'step log{nt}K {CF} hstatic {p} (o := {o}) (by decide +kernel) (k := 32) '
                       f'(by decide +kernel) (by decide) (c := {c}) (by decide +kernel) '
                       f'{hd} (by gas_ok)')
                self.sub = A('logSub' if nt == 3 else f'logSub{nt}', self.sub, TGT, *ts,
                             A('wordBytes', self.mem[1][o // 32]))
                self.cconst += c
            elif op == 0xf1 and self.FRAME and count > 1:
                self.end = ('frame', pc)
                return
            elif op == 0x56:
                d = self.const(self.pop(), 'jump destination')
                self.L('step jumpR')
                self.cconst += 8
                self.end = ('at', d)
                return
            elif op == 0x57:
                d = self.const(self.pop(), 'jump destination')
                cond = self.pop()
                self.cconst += 10
                if isc(cond):
                    taken = cond[1] != 0
                    hc = '(by decide +kernel)'
                else:
                    if self.direction is None:
                        raise NeedDir()
                    taken = self.direction
                    self.cond = (cond, taken)
                    hc = 'hc'
                if taken:
                    self.L(f'step jumpiR {hc}')
                    self.end = ('at', d)
                else:
                    self.L(f'step jumpi0R {hc}')
                    self.end = ('at', pc + 1)
                return
            elif op in (0xf3, 0xfd):
                o = self.const(self.pop(), 'halt offset')
                k = self.const(self.pop(), 'halt size')
                rev = op == 0xfd
                self.L(f'step Gas.reshapeG (g\' := gas - {self.gas()}) rfl rfl (by gas_ok)')
                if rev:
                    self.needs.add('hfork')
                if k == 0:
                    if not rev:
                        raise Fatal('empty RETURN')
                    self.L(f'exact revert0K hfork {CF}')
                    self.end = ('halt', True, V('ByteArray.empty'))
                    return
                self.touch()
                p, size = self.szp()
                rule = 'revertK hfork' if rev else 'returnK'
                if self.mem[0] == 'W':
                    ws = self.mem[1]
                    i = o // 32
                    if (o % 32 == 0 and 0 < k < 32 and i < len(ws)) and rev:
                        # a custom error of Solidity 0.8: the first bytes of one word (USDE local)
                        hd = 'rfl'
                        out = A('memoryReadBytes', self.mem_tree(), V(str(o)), V(str(k)))
                    elif o % 32 or k % 32 or i + k // 32 > len(ws):
                        raise Fatal(f'halt {o} {k} at {pc}')
                    elif k == 32 and self.named_word(o, len(ws)):
                        hd = f'(memW_read{o} ' + ' '.join('_' * len(ws)) + ')'
                        out = A('wordBytes', ws[i])
                    elif k == 32:
                        hd = f'(memW_readWord {i} rfl rfl rfl)'
                        out = A('wordBytes', ws[i])
                    else:
                        # several words: the output is a memory of words
                        hd = f'(memW_readWords {i} rfl rfl rfl rfl)'
                        out = A('memW', ('l', tuple(ws[i:i + k // 32])))
                else:
                    hd = 'rfl'
                    out = A('memoryReadBytes', self.mem[1], V(str(o)), V(str(k)))
                self.L(f'exact {rule} {CF} {p} (o := {o}) (by decide +kernel) (k := {k}) '
                       f'(by decide +kernel) (by decide) {hd}')
                self.end = ('halt', rev, out)
                return
            elif op == 0x00:
                self.L(f'step Gas.reshapeG (g\' := gas - {self.gas()}) rfl rfl (by gas_ok)')
                self.L(f'exact Gas.stopG {CF}')
                self.end = ('halt', False, V('ByteArray.empty'))
                return
            elif op == 0xfe:
                # INVALID: the frame ends with an error, whatever gas is left
                self.L(f'exact Gas.invalid_feG {CF}')
                self.end = ('fault',)
                return
            else:
                raise Fatal(f'opcode 0x{op:02x} at {pc}')
            pc += 1 + n

    # ------------------------------------------------------------ lemma text
    def key(self):
        return (self.pc0, self.direction if self.cond else None, self.bad if self.end == ('stuck',) else False,
                tuple(pr(t) for t in self.in_terms),
                None if self.mem_in is None else tuple(pr(t) for t in self.mem_in)) + (
                    () if self.raw_in is None else
                    ((self.raw_in[0], None if self.raw_in[1] is None else pr(self.raw_in[1])),)) + (
                        (tuple((o, pr(self.words_in[o])) for o in self.words_used()),)
                        if self.words_in else ())

    def words_used(self):
        """The known words of the raw memory it got that the proof of the block reads."""
        text = '\n'.join(self.lines)
        return [o for o in sorted(self.words_in) if re.search(rf'\bhw{o}\b', text)]

    def lemma(self, name):
        xs = [t[1] for t in self.in_terms if t[0] == 'v']
        ms = [t[1] for t in (self.mem_in or []) if t[0] == 'v']
        if self.raw_in is not None and self.raw_in[1] is not None and not isc(self.raw_in[1]):
            ms.append('mfp')
        ms += [f'mw{o}' for o in self.words_used() if not isc(self.words_in[o])]
        b = []
        if xs or ms:
            b.append('{' + ' '.join(xs + ms) + ' : U256}')
        b.append('{rest : List U256}')
        if self.mem_in is None:
            b.append('{mem : ByteArray}')
        b.append('{gas : Nat} {state : State.TransactionState} {substate : Substate}')
        hyps = []
        stuck = self.end == ('stuck',)
        if 'hfork' in self.needs:
            hyps.append('(hfork : .berlin ≤ fork)')
        if self.raw_in is not None:
            b.append('{msz : Nat}')
            hyps.append('(hms : mem.size = msz)')
            hyps.append(f'(hmsz : msz = {self.raw_in[0]})')
            if self.raw_in[1] is not None:
                hyps.append(f'(hfp : loadWord (memoryReadBytes mem 64 32) 0 32 = {pr(self.raw_in[1])})')
            for o in self.words_used():
                hyps.append(f'(hw{o} : loadWord (memoryReadBytes mem {o} 32) 0 32 = '
                            f'{pr(self.words_in[o])})')
        if stuck and self.bad == 'log':
            hyps.append('(hbad : message.isStatic = true)')
        elif stuck:
            hyps.append('(hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)')
        else:
            if 'hstatic' in self.needs:
                hyps.append('(hstatic : message.isStatic = false)')
            if 'hacc' in self.needs:
                hyps.append('(hacc : hasAccount state message.currentTarget)')
        if self.cond:
            hyps.append(f'(hc : {pr(self.cond[0])} {"≠" if self.cond[1] else "="} 0)')
        if self.pushes:
            hyps.append('(hrest : rest.length ≤ 900)')
        if self.has_sstore:
            hyps.append(f'(hg : {self.gas()} + 2300 < gas)')
        else:
            hyps.append(f'(hg : {self.gas()} ≤ gas)')
        pre_stack = ' :: '.join([pr(t) for t in self.in_terms] + ['rest'])
        if self.mem_in is None:
            pre_mem = 'mem'
        else:
            pre_mem = '(memW [' + ', '.join(pr(w) for w in self.mem_in) + '])'
        pre = f'(At CODE message {self.pc0} ({pre_stack}) {pre_mem} gas state substate)'
        if stuck:
            concl = f'Gas.HoareG fork {pre} Gas.Stuck'
        elif self.end[0] in ('at', 'frame'):
            post_stack = ' :: '.join([pr(t) for t in self.stack] + ['rest'])
            concl = (f'Gas.HoareG fork {pre}\n      (At CODE message {self.end[1]} ({post_stack}) '
                     f'{self.mem_term()} (gas - {self.gas()}) {pr(self.state)} {pr(self.sub)})')
        elif self.end[0] == 'fault':
            concl = (f'Gas.SpecG fork {pre}\n      (Faulted (.invalidOpcode 0xfe) '
                     f'{pr(self.state)} {pr(self.sub)})')
        else:
            concl = (f'Gas.SpecG fork {pre}\n      (Halted {"true" if self.end[1] else "false"} '
                     f'{pr(self.end[2])} (gas - {self.gas()}) {pr(self.state)} {pr(self.sub)})')
        out = [f'theorem {name} ' + ' '.join(b)]
        for h in hyps:
            out.append('    ' + h)
        out[-1] += ' :'
        out.append('    ' + concl + ' := by')
        if self.raw_in is not None:
            out.append('  subst hmsz')
        for line in self.lines:
            out.append('  ' + line)
        if self.end[0] in ('at', 'frame'):
            out.append('  exact restate (by decide) rfl rfl (by gas_ok) rfl rfl')
        if self.LOGIC:
            # the rules are over the StepG of usdt-verify or over Logic.StepG; the tactic `step`
            # chains both in a goal over Logic.StepG, and the last rule is lifted by name
            k = len(out) - len(self.lines) - (1 if self.end[0] in ('at', 'frame') else 0) - 1
            if self.raw_in is not None:
                k -= 1
            out[k] = (out[k].replace('Gas.HoareG', 'Logic.HoareG').replace('Gas.SpecG', 'Logic.SpecG')
                      .replace('Gas.Stuck', 'Logic.Stuck'))
            if not out[-1].startswith('  exact '):
                raise Fatal(f'logic mode: the last line of {name}')
            lift = 'stuckL' if stuck else 'hoareL' if self.end[0] in ('at', 'frame') else 'specL'
            out[-1] = f'  exact {lift} ({out[-1][8:]})'
        return '\n'.join(out) + '\n'

    def args(self, cname, pstate, pmem=None):
        """The explicit arguments of the lemma at the path level."""
        a = []
        stuck = self.end == ('stuck',)
        if 'hfork' in self.needs:
            a.append('hfork')
        if self.raw_in is not None:
            a.append(pmem['szp'])
            a.append('(by rfl)')
            if self.raw_in[1] is not None:
                a.append(pmem['fpp'])
            for o in self.words_used():
                a.append(pmem['words'][o][1])
        if stuck and self.bad == 'log':
            a.append('hstat')
        elif stuck:
            a.append(hbad_proof(pstate))
        else:
            if 'hstatic' in self.needs:
                a.append('hstatic')
            if 'hacc' in self.needs:
                a.append(hacc_proof(pstate))
        if self.cond:
            a.append(cname)
        if self.pushes:
            a.append('(by simp)')
        a.append('(by omega)')
        return ' '.join(a)


# ---------------------------------------------------------------- paths

class Gen:
    def __init__(self, ins, tok):
        self.ins = ins
        self.tok = tok
        self.pruned = []       # (function, pc, hypothesis) of each branch decided by an earlier one
        self.cache = {}        # key -> name
        self.stops = frozenset(tok.stops)
        self.lemmas = []       # (name, text)
        self.count = {}
        d = tok.cfg['dispatch']
        self.min_size = d.get('min_size', 4)
        self.size_proof = d.get(
            'size_proof', "obtain ⟨hsize, -, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok"
            if tok.logic else "obtain ⟨hsize, -, -⟩ := ends_ok_dispatch hfork hsize' start hrun hok")
        self.prune_norm = tok.cfg.get('prune') == 'normalized'
        self.dead = {(x['function'], x['pc'], x['visit']): x
                     for x in tok.cfg.get('dead_branches', [])}
        self.dead_used = set()
        Block.RET = tok.memory_words[2]
        Block.NAMED = tok.cfg.get('paths', {}).get('memory_lemmas') == 'named'
        Block.RAWX = tok.cfg.get('paths', {}).get('raw_memory') == 'across_blocks'
        Block.RAWW = bool(tok.cfg.get('paths', {}).get('raw_words'))
        Block.LOGIC = self.logic = tok.logic
        self.walk_mode = d.get('mode') == 'walk'
        # mode `walk`: the fallback paths come before Complete/Dispatch.lean, so the lemma on a
        # revert is the one of the library (TokenKit/Evm/Opt.lean)
        self.rev_err = 'reverted_error' if self.walk_mode else 'halted_true_error'
        self.facts = {}

    def block(self, pc, pstack, pmem, direction, bad):
        b = Block(self.ins, pc, pstack, pmem, direction, bad, self.stops)
        k = b.key()
        if k not in self.cache:
            i = self.count.get(pc, 0)
            self.count[pc] = i + 1
            name = f'b{pc}_{i}'
            self.cache[k] = name
            self.lemmas.append((name, b.lemma(name)))
        return b, self.cache[k]

    def function(self, f):
        kind = f.get('kind')
        self.fname, self.kind = f['name'], kind
        self.post_def = bool(f.get('post_def'))
        self.paths = []
        Block.FRAME = bool(f.get('frame'))
        self.rf = kind == 'segment'    # completeness over runFrame (a segment, or a path to a stop)
        term = lambda w: C(w) if isinstance(w, int) else V(w)
        SEL = V('(BitVec.ofNat 256 (selector message.data))')
        HF, H4, H256 = ('(hfork : .berlin ≤ fork)',
                        f'(hsize : {self.min_size} ≤ message.data.size)',
                        "(hsize' : message.data.size < 2 ^ 256)")
        mem = [C(w) for w in self.tok.memory_words]
        self.pre = '(At CODE message 0 [] .empty gas state substate)'
        self.oklead = []
        self.facts = {}
        if self.walk_mode and kind in (None, 'short', 'other', 'value'):
            # optimized code: the path starts at pc 0 and runs through the dispatcher
            dest, entry_cost, line, stack, mem = 0, 0, None, [], []
            if kind is None:
                sel = f['selector']
                hsel = f'(hsel : selector message.data = 0x{sel:08x})'
                self.hy0, self.call0 = [HF, H4, H256, hsel], ["hfork", "hsize", "hsize'", "hsel"]
                self.okhy = [H256, hsel]
                self.oklead = [self.size_proof]
                self.facts = dict(size=True, sel=sel)
            elif kind == 'short':
                hs = f'(hsize : message.data.size < {self.min_size})'
                self.hy0, self.call0, self.okhy = [HF, hs], ['hfork', 'hsize'], [hs]
                self.facts = dict(size=False)
            elif kind == 'other':
                hsel = '(hsel : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)'
                self.hy0, self.call0 = [HF, H4, H256, hsel], ["hfork", "hsize", "hsize'", "hsel"]
                self.okhy = [H4, H256, hsel]
                self.facts = dict(size=True, other=True)
            else:
                hv = '(hv : message.value ≠ 0)'
                self.hy0, self.call0, self.okhy = [HF, hv], ['hfork', 'hv'], [hv]
                self.facts = dict(value=True)
        elif kind is None:
            sel, idx, dest = f['selector'], f['index'], f['dest']
            entry_cost = f['entry_cost']
            hsel = f'(hsel : selector message.data = 0x{sel:08x})'
            self.hy0, self.call0 = [HF, H4, H256, hsel], ["hfork", "hsize", "hsize'", "hsel"]
            if self.tok.explicit_size:
                self.okhy = [H4, H256, hsel]
            else:
                self.okhy = [H256, hsel]
                self.oklead = [self.size_proof]
            stack = [SEL]
            line = (f'step enter hsize hsize\' ⟨{idx}, by decide⟩ (key := 0x{sel:08x}) (dest := {dest}) '
                    f'(N := {entry_cost}) (by decide) (by decide) (by decide) hsel (by omega)')
        elif kind == 'short':
            # fewer than 4 bytes of call data: the fallback, with an empty stack
            dest, entry_cost = f['dest'], f['entry_cost']
            hs = '(hsize : message.data.size < 4)'
            self.hy0, self.call0, self.okhy = [HF, hs], ['hfork', 'hsize'], [hs]
            stack = []
            line = 'step enterShort hsize (by omega)'
        elif kind == 'other':
            # a selector that is no key of the table: the fallback, with the selector on the stack
            dest, entry_cost = f['dest'], f['entry_cost']
            hsel = '(hsel : BitVec.ofNat 256 (selector message.data) ∉ ENTRIES.map Prod.fst)'
            self.hy0, self.call0 = [HF, H4, H256, hsel], ["hfork", "hsize", "hsize'", "hsel"]
            self.okhy = [H4, H256, hsel]
            stack = [SEL]
            line = "step enterOther hsize hsize' hsel (by omega)"
        elif kind == 'segment':
            # the code from a given pc on, with a given stack and memory (after a stop)
            dest, entry_cost, line = f['pc'], 0, None
            stack = [term(w) for w in f['stack']]
            mem = [term(w) for w in f.get('mem', self.tok.memory_words)]
            vs = [t[1] for t in stack + mem if t[0] == 'v']
            bind = ['{' + ' '.join(vs) + ' : U256}'] if vs else []
            # `static: false`: the frame may write (the segment logs with no SSTORE before)
            hs = ['(hstatic : message.isStatic = false)'] if f.get('static') is False else []
            self.hy0, self.call0, self.okhy = bind + [HF] + hs, ['hfork'] + ['hstatic'] * len(hs), hs
            self.okbind = bind
            self.pre = (f'(At CODE message {dest} [' + ', '.join(pr(t) for t in stack) + '] (memW ['
                        + ', '.join(pr(t) for t in mem) + ']) gas state substate)')
            if f.get('raw_mem'):
                # the segment starts with a raw memory `mem`: its size, its word at 64 and the
                # other words it is known to hold are hypotheses (`paths.raw_words`)
                rm = f['raw_mem']
                words = {int(o): (term(w), f'hmem_w{o}') for o, w in rm.get('words', {}).items()}
                mem = dict(term=V('mem'), size=rm['size'], szp='hmem_size', fpp='hmem_fp',
                           fpv=term(rm['fp']), words=words)
                vs = [t[1] for t in stack + [w for w, _ in words.values()] if t[0] == 'v']
                vs = list(dict.fromkeys(vs))
                self.okvars = vs
                bind = ['{' + ' '.join(vs) + ' : U256}'] if vs else []
                bind.append('{mem : ByteArray}')
                mh = [f'(hmem_size : mem.size = {rm["size"]})',
                      f'(hmem_fp : loadWord (memoryReadBytes mem 64 32) 0 32 = {pr(mem["fpv"])})']
                mh += [f'(hmem_w{o} : loadWord (memoryReadBytes mem {o} 32) 0 32 = {pr(w)})'
                       for o, (w, _) in sorted(words.items())]
                mc = ['hmem_size', 'hmem_fp'] + [f'hmem_w{o}' for o in sorted(words)]
                self.hy0 = bind + [HF] + hs + mh
                self.call0 = ['hfork'] + ['hstatic'] * len(hs) + mc
                self.okhy = hs + mh
                self.okbind = bind
                self.pre = (f'(At CODE message {dest} [' + ', '.join(pr(t) for t in stack)
                            + '] mem gas state substate)')
        else:
            raise Fatal(f'kind {kind}')
        st = dict(pc=dest, stack=stack,
                  mem=mem, state=V('state'), sub=V('substate'),
                  cconst=entry_cost, cterms=[], hyps=[], lines=[], wrote=False, nc=0,
                  good=False, visits={}, nd=0)
        if line is not None:
            st['lines'].append(line)
        return self.walk(st, first=True)

    def total(self, st):
        if not st['cterms']:
            return str(st['cconst'])
        return '(' + ' + '.join([str(st['cconst'])] + [pr(t) for t in st['cterms']]) + ')'

    def env(self, st, b):
        """The values of the variables of the block lemma on the path state."""
        m = {f'x{i}': st['stack'][i] for i in range(len(b.in_terms))}
        for i, w in enumerate(st['mem'] if isinstance(st['mem'], list) else []):
            m[f'm{i}'] = w
        if isinstance(st['mem'], dict):
            m['mem'] = st['mem']['term']
            if st['mem']['fpv'] is not None:
                m['mfp'] = st['mem']['fpv']
            for o, (v, _) in st['mem'].get('words', {}).items():
                m[f'mw{o}'] = v
        m['state'] = st['state']
        m['substate'] = st['sub']
        return m

    def entry_fact(self, cond):
        """(taken, tactic) when a hypothesis on the call decides the condition (mode `walk`)."""
        F = self.facts
        if not F:
            return None
        if cond == A('isZero', V('(BitVec.ofNat 256 message.data.size)')) and 'size' in F:
            # LINK local (solc 0.4): the dispatcher tests CALLDATASIZE == 0
            if F['size']:
                return False, "exact size_isZero_zero hsize hsize'"
            return True, 'exact size_isZero_ne hsize'
        if cond == A('lessThan', V('(BitVec.ofNat 256 message.data.size)'), C(4)) and 'size' in F:
            if F['size']:
                return False, "exact size_lt4_zero hsize hsize'"
            return True, 'exact size_lt4_ne hsize'
        if F.get('value') and cond == A('isZero', V('message.value')):
            return False, 'exact isZero_eq_zero_iff.mpr hv'
        if 'sel' in F and mentions(cond, SELT):
            v = evalc(subst(cond, {SELT[1]: C(F['sel'])}))
            if v is not None:
                return v != 0, 'rw [hsel]; decide +kernel'
        if (F.get('other') and cond[0] == 'a' and cond[1] == 'equal' and isc(cond[2][0])
                and cond[2][1] == SELT):
            return False, 'exact equal_key_zero hsel (by decide +kernel)'
        if (F.get('other') and cond[0] == 'a' and cond[1] == 'equal' and isc(cond[2][1])
                and cond[2][0] == SELT):
            # LINK local: the first entry of the table compares in the other order
            return False, 'exact equal_key_zero_r hsel (by decide +kernel)'
        return None

    def dead_rule(self, cond, hyps):
        """(taken, tactic, name) when a rule of `paths.dead_rules` decides the condition: a
        branch that no run takes, for a reason that holds for every state (no fact about keccak).

        - `sub_after_ge`: the check `x - a <= x` of a SafeMath sub (old Solidity with the
          optimizer: ISZERO (GT (SUB x a) x)) after an explicit `require(a <= x)` on the same
          word `x` (the same term once the recorded reads are dropped; a write in between makes
          it another term, and then the branch stays).
        - `caller_mask`: `msg.sender == address(msg.sender)`: EQ of the caller with its own
          masked word."""
        rules = self.tok.cfg.get('paths', {}).get('dead_rules', [])
        if 'sub_after_ge' in rules and cond[0] == 'a' and cond[1] == 'isZero':
            g = cond[2][0]
            if (g[0] == 'a' and g[1] == 'greaterThan' and g[2][0][0] == 'a'
                    and g[2][0][1] == 'sub' and g[2][0][2][0] == g[2][1]):
                x, a = strip_reads(g[2][1]), strip_reads(g[2][0][2][1])
                want = A('isZero', A('greaterThan', a, x))
                for (cn, c, taken) in hyps:
                    if taken and strip_reads(c) == want:
                        return True, f'sub_checked {cn}', 'sub_after_ge ' + cn
        if 'caller_mask' in rules and cond[0] == 'a' and cond[1] == 'equal':
            cl = V('message.caller.toU256')
            mk = C((1 << 160) - 1)
            if cond[2][0] == cl and cond[2][1] in (A('bitwiseAnd', cl, mk), A('bitwiseAnd', mk, cl)):
                return True, 'caller_masked', 'caller_mask'
        return None

    def derived(self, st, pc, cond, taken, tactic):
        """Follow the one side of a branch that an earlier fact decides, with the condition
        proved by `tactic` in a `have` of the path theorem."""
        st = dict(st)
        st['nd'] = st['nd'] + 1
        hd = f'hd{st["nd"]}'
        st['dv'] = list(st.get('dv', [])) + [(hd, pr(cond), taken, tactic)]
        bd, nd = self.block(pc, st['stack'], st['mem'], taken, False)
        line = f'have {hd} : {pr(cond)} {"≠" if taken else "="} 0 := by {tactic}'
        sd = self.apply(st, bd, nd, reuse=hd, pre=line)
        return self.after(st, sd, bd)

    def apply(self, st, b, name, reuse=None, pre=None):
        """The path state after the block. `reuse` names an earlier hypothesis that is the
        condition of the block: then no new hypothesis is added."""
        m = self.env(st, b)
        n = dict(st)
        n['hyps'] = list(st['hyps'])
        n['lines'] = list(st['lines']) + ([pre] if pre else [])
        n['cterms'] = list(st['cterms']) + [subst(t, m) for t in b.cterms]
        n['cconst'] = st['cconst'] + b.cconst
        cname = None
        if b.cond and reuse is not None:
            cname = reuse
        elif b.cond:
            n['nc'] = st['nc'] + 1
            cname = f'hc{n["nc"]}'
            n['hyps'].append((cname, subst(b.cond[0], m), b.cond[1]))
        if b.has_sstore and not st['good']:
            n['good'] = True
        n['wrote'] = st['wrote'] or b.has_sstore
        n['state'] = subst(b.state, m)
        n['sub'] = subst(b.sub, m)
        n['stack'] = [subst(t, m) for t in b.stack] + st['stack'][len(b.in_terms):]
        if b.mem is not None and b.mem[0] == 'W':
            n['mem'] = [subst(t, m) for t in b.mem[1]]
        elif b.mem is not None and b.mem[0] == 'R' and b.end[0] == 'at':
            # a raw memory that crosses the block boundary: its term, its size, and the proofs
            # of the size and of the word at 64 for the next block, in the words of the path
            def lift(pf):
                if pf is None:
                    return None
                pf = pf.replace('_ rfl)', '_ (by rfl))')
                if isinstance(st['mem'], dict):
                    pf = re.sub(r'\bhms\b', lambda _: st['mem']['szp'], pf)
                    if st['mem']['fpp'] is not None:
                        pf = re.sub(r'\bhfp\b', lambda _: st['mem']['fpp'], pf)
                    pw = st['mem'].get('words', {})
                    if pw:
                        pf = re.sub(r'\bhw(\d+)\b', lambda x: pw[int(x.group(1))][1], pf)
                return pf
            n['mem'] = dict(term=subst(b.mem[1], m), size=b.mem[2], szp=lift(b.mem[3]),
                            fpp=lift(b.mem[4]),
                            fpv=None if b.mem[4] is None else subst(b.mem[5], m))
            if b.mem[6]:
                n['mem']['words'] = {o: (subst(v, m), lift(pa)) for o, (v, pa) in b.mem[6].items()}
        n['args'] = f'{name} {b.args(cname, st["state"], st["mem"])}'
        n['m'] = m
        if b.end[0] == 'at':
            n['pc'] = b.end[1]
        return n

    def walk(self, st, first=False):
        """Returns the decision tree under `st`."""
        if st['pc'] in self.stops and not first:
            return self.leaf_at(st)
        try:
            b, name = self.block(st['pc'], st['stack'], st['mem'], None, False)
        except NeedDir:
            probe = Block(self.ins, st['pc'], st['stack'], st['mem'], False, False, self.stops)
            cond = subst(probe.cond[0], self.env(st, probe))
            st = dict(st)
            st['visits'] = dict(st['visits'])
            visit = st['visits'][st['pc']] = st['visits'].get(st['pc'], 0) + 1
            ef = self.entry_fact(cond)
            if ef is not None:
                # decided by a hypothesis on the call (its selector, the size of its data)
                self.pruned.append((self.fname, st['pc'], 'entry'))
                return self.derived(st, st['pc'], cond, ef[0], ef[1])
            dec = decided(cond)
            if dec is not None:
                # EQ of a word with itself decides the branch: only that side can run
                self.pruned.append((self.fname, st['pc'], 'equal_self'))
                bd, nd = self.block(st['pc'], st['stack'], st['mem'], dec != 0, False)
                sd = self.apply(st, bd, nd, reuse='(by rw [equal_self]; decide +kernel)')
                return self.after(st, sd, bd)
            for (cn, c, taken) in st['hyps'] + st.get('known', []):
                if c == cond:
                    # decided by an earlier branch of this path: only that side can run
                    self.pruned.append((self.fname, st['pc'], cn))
                    bd, nd = self.block(st['pc'], st['stack'], st['mem'], taken, False)
                    sd = self.apply(st, bd, nd, reuse=cn)
                    return self.after(st, sd, bd)
            if self.tok.cfg.get('paths', {}).get('decide_equivalent'):
                # the same after ISZERO pairs and reads of slots are taken off: also decided
                core, pol = norm_cond(cond, True)
                for (cn, c, taken) in st['hyps']:
                    core2, pol2 = norm_cond(c, taken)
                    if core2 == core:
                        d = pol == pol2
                        self.pruned.append((self.fname, st['pc'], cn))
                        bd, nd = self.block(st['pc'], st['stack'], st['mem'], d, False)
                        sd = self.apply(st, bd, nd, reuse=f'(decided_by {cn})')
                        return self.after(st, sd, bd)
            if self.prune_norm:
                atom, flip = norm(cond)
                for (cn, c, taken) in st['hyps'] + st.get('known', []):
                    a2, f2 = norm(c)
                    if a2 == atom:
                        self.pruned.append((self.fname, st['pc'], cn))
                        return self.derived(st, st['pc'], cond, (taken != f2) != flip,
                                            f'decided {cn}')
            dr = self.dead_rule(cond, st['hyps'])
            if dr is not None:
                self.pruned.append((self.fname, st['pc'], dr[2]))
                # the fact is known from here on: a later test of it in another shape is decided
                st['known'] = list(st.get('known', [])) + [(f'hd{st["nd"] + 1}', cond, dr[0])]
                return self.derived(st, st['pc'], cond, dr[0], dr[1])
            dk = (self.fname, st['pc'], visit)
            if os.environ.get('GEN_PATHS_TRACE'):
                # a debugging aid: every branch that no earlier fact decides
                print('branch', dk, pr(cond)[:300], file=sys.stderr)
            if dk in self.dead:
                self.dead_used.add(dk)
                x = self.dead[dk]
                self.pruned.append((self.fname, st['pc'], x['by']))
                return self.derived(st, st['pc'], cond, x['side'] == 'taken', x['by'])
            b0, n0 = self.block(st['pc'], st['stack'], st['mem'], False, False)
            b1, n1 = self.block(st['pc'], st['stack'], st['mem'], True, False)
            s0, s1 = self.apply(st, b0, n0), self.apply(st, b1, n1)
            cond = s0['hyps'][-1][1]
            return ('branch', s0['hyps'][-1][0], cond, self.after(st, s0, b0), self.after(st, s1, b1))
        n = self.apply(st, b, name)
        return self.after(st, n, b)

    def after(self, st, n, b):
        tree_bad = None
        if (not st['good'] and not b.has_sstore and 'hstatic' in b.needs
                and not st.get('static_alt')):
            # a LOG before the first SSTORE of the path: the stuck variant of the path (static
            # frame or no account) needs the case of a static frame apart, where this LOG fails
            if b.cond:
                raise Fatal(f'LOG before the first SSTORE in a block with a condition at {st["pc"]}')
            bl, nl = self.block(st['pc'], st['stack'], st['mem'], None, 'log')
            sl = self.apply(st, bl, nl)
            n['static_alt'] = sl['lines'] + [f'exact {sl["args"]}']
        if b.has_sstore and not st['good']:
            bb, nb = self.block(st['pc'], st['stack'], st['mem'],
                                b.direction if b.cond else None, True)
            # the stuck variant has the same condition (if any) before the SSTORE
            sb = self.apply(st, bb, nb)
            tree_bad = self.leaf(st, sb, bb, stuck=True)
        if b.end[0] == 'at':
            n['lines'].append(f'step {n["args"]}')
            sub = self.walk(n)
        elif b.end[0] == 'frame':
            sub = self.frame_leaf(st, n, b)
        else:
            sub = self.leaf(st, n, b, stuck=False)
        if tree_bad is not None:
            return ('sstore', tree_bad, sub)
        return sub

    def frame_leaf(self, st, n, b):
        """A path that stops at the frame before a CALL."""
        i = len(self.paths)
        name = f'{self.fname}_p{i}'
        hy, call = list(self.hy0), list(self.call0)
        if n['good']:
            hy += ['(hstatic : message.isStatic = false)',
                   '(hacc : hasAccount state message.currentTarget)']
            call += ['hstatic', 'hacc']
        for (cn, cond, taken) in n['hyps']:
            hy.append(f'({cn} : {pr(cond)} {"≠" if taken else "="} 0)')
            call.append(cn)
        tot = self.total(n)
        hy.append(f'{{gas : Nat}} (hg : {tot} ≤ gas)')
        m = n['m']
        stack = ' :: '.join([pr(subst(t, m)) for t in b.stack]
                            + [pr(t) for t in st['stack'][len(b.in_terms):]] + ['[]'])
        mem = pr(A('memW', ('l', tuple(n['mem']))))
        concl = (f'Gas.HoareG fork (At CODE message 0 [] .empty gas state substate)\n'
                 f'      (At CODE message {b.end[1]} ({stack}) {mem} (gas - {tot}) '
                 f'{pr(n["state"])} {pr(n["sub"])})')
        text = [f'theorem {name}'] + ['    ' + h for h in hy]
        text[-1] += ' :'
        text.append('    ' + concl + ' := by')
        text += ['  ' + line for line in n['lines']]
        text.append(f'  exact Gas.Triple.seqL ({n["args"]}) (restate rfl rfl rfl (by omega) rfl rfl)')
        self.paths.append(dict(
            name=name, kind='frame', text='\n'.join(text) + '\n', call=call, bound=tot,
            conds=[(cn, pr(c), t) for (cn, c, t) in n['hyps']], good=n['good'],
            wrote=n['wrote'], pc=b.end[1], cost=tot, stack=stack, mem=mem,
            state=pr(n['state']), sub=pr(n['sub'])))
        return ('leaf', i)

    def leaf_at(self, n):
        """A path that reaches a stop: a theorem to the frame at the stop, not to a halt."""
        self.rf = True
        i = len(self.paths)
        name = f'{self.fname}_p{i}'
        hy, call = list(self.hy0), list(self.call0)
        if n['good']:
            hy.append('(hstatic : message.isStatic = false)')
            hy.append('(hacc : hasAccount state message.currentTarget)')
            call += ['hstatic', 'hacc']
        for (cn, cond, taken) in n['hyps']:
            hy.append(f'({cn} : {pr(cond)} {"≠" if taken else "="} 0)')
            call.append(cn)
        tot = self.total(n)
        if n['wrote']:
            bound = f'{tot} + 2301'
            hy.append(f'{{gas : Nat}} (hg : {tot} + 2300 < gas)')
        else:
            bound = tot
            hy.append(f'{{gas : Nat}} (hg : {tot} ≤ gas)')
        if not isinstance(n['mem'], list) and not Block.RAWW:
            raise Fatal('stop with a raw memory')
        stack = '[' + ', '.join(pr(t) for t in n['stack']) + ']'
        memfacts = None
        if isinstance(n['mem'], list):
            mem = '(memW [' + ', '.join(pr(t) for t in n['mem']) + '])'
        else:
            # a raw memory at the stop: its term, and a theorem `<path>_mem` with its size and
            # the words it is known to hold
            R = n['mem']
            mem = pr(R['term'])
            facts = [(f'({mem}).size = {R["size"]}', R['szp'])]
            if R['fpp'] is not None:
                facts.append((f'loadWord (memoryReadBytes {mem} 64 32) 0 32 = {pr(R["fpv"])}',
                              R['fpp']))
            for o, (v, pa) in sorted(R.get('words', {}).items()):
                facts.append((f'loadWord (memoryReadBytes {mem} {o} 32) 0 32 = {pr(v)}', pa))
            bind = [h for h in hy if h.startswith('{') and 'gas' not in h]
            memfacts = (f'theorem {name}_mem ' + ' '.join(bind) + ' :\n    '
                        + ' ∧\n    '.join('(' + f + ')' for f, _ in facts) + ' :=\n  ⟨'
                        + ',\n   '.join(pa for _, pa in facts) + '⟩\n')
        frame = f'{n["pc"]} {stack} {mem} (gas - {tot}) {pr(n["state"])} {pr(n["sub"])}'
        text = [f'theorem {name}'] + ['    ' + h for h in hy]
        text[-1] += ' :'
        if self.logic:
            text.append(f'    Logic.HoareG fork {self.pre}\n      (At CODE message {frame}) := by')
            text += ['  ' + line for line in n['lines']]
            text.append('  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)')
        else:
            text.append(f'    Gas.HoareG fork {self.pre}\n      (At CODE message {frame}) := by')
            text += ['  ' + line for line in n['lines']]
            text.append('  exact restate rfl rfl rfl (by omega) rfl rfl')
        if memfacts is not None:
            text += ['', memfacts.rstrip('\n')]
        self.paths.append(dict(
            name=name, kind='at', text='\n'.join(text) + '\n', call=call, bound=bound,
            conds=[(cn, pr(c), t) for (cn, c, t) in n['hyps']], good=n['good'],
            wrote=n['wrote'], cost=tot, pc=n['pc'], stack=[pr(t) for t in n['stack']],
            mem=[pr(t) for t in n['mem']] if isinstance(n['mem'], list) else mem,
            state=pr(n['state']), sub=pr(n['sub']),
            frame=frame.replace(f'(gas - {tot})', '{GAS}')))
        return ('leaf', i)

    def leaf(self, st, n, b, stuck):
        i = len(self.paths)
        name = f'{self.fname}_p{i}'
        hy = list(self.hy0)
        call = list(self.call0)
        if stuck:
            hy.append('(hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)')
            call.append('hbad')
        elif n['good']:
            hy.append('(hstatic : message.isStatic = false)')
            hy.append('(hacc : hasAccount state message.currentTarget)')
            call += ['hstatic', 'hacc']
        for (cn, cond, taken) in n['hyps']:
            hy.append(f'({cn} : {pr(cond)} {"≠" if taken else "="} 0)')
            call.append(cn)
        tot = self.total(n)
        pre = self.pre
        if stuck:
            # the gas before the block that sticks, plus that block's prefix
            bound = tot
            hy.append(f'{{gas : Nat}} (hg : {bound} ≤ gas)')
            concl = f'Gas.HoareG fork {pre} Gas.Stuck'
            if self.logic:
                concl = f'Logic.HoareG fork {pre} Logic.Stuck'
            last = f'exact {n["args"]}'
            kind = 'stuck'
            info = {}
        else:
            if n['wrote']:
                bound = f'{tot} + 2301'
                hy.append(f'{{gas : Nat}} (hg : {tot} + 2300 < gas)')
            else:
                bound = tot
                hy.append(f'{{gas : Nat}} (hg : {tot} ≤ gas)')
            if b.end[0] == 'fault':
                concl = (f'Gas.SpecG fork {pre}\n      (Faulted (.invalidOpcode 0xfe) '
                         f'{pr(n["state"])} {pr(n["sub"])})')
                last = f'exact {n["args"]}'
                kind = 'invalid'
                info = dict(state=pr(n['state']), sub=pr(n['sub']))
            else:
                rev = b.end[1]
                out = pr(subst(b.end[2], n['m']))
                concl = (f'Gas.SpecG fork {pre}\n      (Halted {"true" if rev else "false"} {out} '
                         f'(gas - {tot}) {pr(n["state"])} {pr(n["sub"])})')
                last = f'exact haltGas ({n["args"]}) (by omega)'
                if self.logic:
                    last = f'exact haltGasL ({n["args"]}) (by omega)'
                kind = 'revert' if rev else 'ok'
                info = dict(out=out, cost=tot, state=pr(n['state']), sub=pr(n['sub']))
        if self.logic:
            concl = concl.replace('Gas.SpecG', 'Logic.SpecG')
        text = [f'theorem {name}'] + ['    ' + h for h in hy]
        text[-1] += ' :'
        text.append('    ' + concl + ' := by')
        if stuck and n.get('static_alt'):
            text += ['  rcases Bool.eq_false_or_eq_true message.isStatic with hstat | hstatic']
            alt = ['  ' + line for line in n['static_alt']]
            text += ['  · ' + alt[0][2:]] + ['  ' + line for line in alt[1:]]
        text += ['  ' + line for line in n['lines']]
        text.append('  ' + last)
        self.paths.append(dict(
            name=name, kind=kind, text='\n'.join(text) + '\n', call=call, bound=bound,
            conds=[(cn, pr(c), t) for (cn, c, t) in n['hyps']], good=n['good'] and not stuck,
            wrote=n['wrote'], **({'derived': n['dv']} if n.get('dv') else {}), **info))
        return ('leaf', i)

    # ------------------------------------------------------------ completeness
    def complete(self, tree):
        if any(p['kind'] == 'frame' for p in self.paths):
            return None
        oks = [i for i, p in enumerate(self.paths) if p['kind'] in ('ok', 'at')]
        rf = self.rf
        lg = self.logic
        RUN = 'Evm.runFrame (step fork) (step_decreases fork) bound runChild'
        hrun = 'hrun' if lg else '(Ends.run hrun)' if rf else 'hrun'
        # the lemmas of the logic mode (TokenKit/Evm/SafeL.lean), over runs `EndsL`
        no_ok, ok_ex, hB = ('no_okLE', 'ok_exactLE', '') if lg else ('no_okE', 'ok_exactE', ' (by omega)')
        no_stuck = 'no_ok_stuckLE' if lg else 'Gas.no_ok_stuckE'
        disj = []
        for i in oks:
            p = self.paths[i]
            parts = [f'{c} {"≠" if t else "="} 0' for (_, c, t) in p['conds']]
            if p['good']:
                parts += ['message.isStatic = false', 'hasAccount state message.currentTarget']
            if p['kind'] == 'at' and lg:
                parts += [f'{p["cost"]} ≤ gas',
                          '∃ z : Evm fork Nat,\n          '
                          f'At CODE message {p["frame"].replace("{GAS}", "(gas - " + p["cost"] + ")")} z ∧\n          '
                          'EndsL runChild z s']
            elif p['kind'] == 'at':
                parts += [f'{p["cost"]} ≤ gas',
                          '∃ (z : Evm fork Nat) (w : GasMeter.gasHeld z.gas ≤ bound),\n          '
                          f'At CODE message {p["frame"].replace("{GAS}", "(gas - " + p["cost"] + ")")} z ∧\n          '
                          f'{RUN} z w = .ok s']
            else:
                parts += [f'{p["cost"]} ≤ gas', f's.output = {p["out"]}',
                          f's.gas = gas - {p["cost"]}',
                          f's.state = {p["state"]}', f's.substate = {p["sub"]}']
            disj.append('(' + ' ∧\n        '.join(parts) + ')')
        lines = []

        def inj(i):
            k = oks.index(i)
            if len(oks) == 1:
                return '{}'
            s = '{}'
            if k < len(oks) - 1:
                s = '(Or.inl {})'
            for _ in range(k):
                s = f'(Or.inr {s})'
            return s

        def emit(t, ind):
            pad = '  ' * ind
            if t[0] == 'branch':
                _, cn, cond, t0, t1 = t
                lines.append(f'{pad}by_cases {cn} : {pr(cond)} = 0')
                lines.append(f'{pad}·')
                emit(t0, ind + 1)
                lines.append(f'{pad}·')
                emit(t1, ind + 1)
            elif t[0] == 'sstore':
                _, tb, tg = t
                pb = self.paths[tb[1]]
                lines.append(f'{pad}by_cases hgood : ¬(message.isStatic = false ∧ '
                             f'hasAccount state message.currentTarget)')
                callb = ' '.join('(Gas.bad_of_not hgood)' if c == 'hbad' else c for c in pb['call'])
                lines.append(f'{pad}· exact ({no_stuck} (B := {pb["bound"]}) (fun g hg => '
                             f'{pb["name"]} {callb} hg) start {hrun} hok).elim')
                lines.append(f'{pad}obtain ⟨hstatic, hacc⟩ := Classical.not_not.mp hgood')
                emit(tg, ind)
            else:
                p = self.paths[t[1]]
                call = ' '.join(p['call'])
                if p['kind'] == 'invalid':
                    lines.append(f'{pad}exact ({no_ok} (B := {p["bound"]}) (fun g hg => {p["name"]} '
                                 f'{call} (by omega)) (fun _ e h => faulted_error e h) '
                                 f'start {hrun} hok).elim')
                elif p['kind'] == 'revert':
                    lines.append(f'{pad}exact ({no_ok} (B := {p["bound"]}) (fun g hg => {p["name"]} '
                                 f'{call} (by omega)) (fun _ e h => {self.rev_err} e h) '
                                 f'start {hrun} hok).elim')
                elif p['kind'] == 'at' and lg:
                    lines.append(f'{pad}obtain ⟨hcg, z, hz, hzr⟩ := ok_splitLE '
                                 f'(B := {p["bound"]}) (c := {p["cost"]}) (by omega) '
                                 f'(fun g hg => {p["name"]} {call} (by omega)) start hrun hok')
                    parts = [cn for (cn, _, _) in p['conds']]
                    if p['good']:
                        parts += ['hstatic', 'hacc']
                    parts += ['hcg', 'z', 'hz', 'hzr']
                    lines.append(f'{pad}exact ' + inj(t[1]).format('⟨' + ', '.join(parts) + '⟩'))
                elif p['kind'] == 'at':
                    lines.append(f'{pad}obtain ⟨hcg, z, w, hz, hzr⟩ := ok_split '
                                 f'(B := {p["bound"]}) (c := {p["cost"]}) (by omega) '
                                 f'(fun g hg => {p["name"]} {call} (by omega)) start within hrun hok')
                    parts = [cn for (cn, _, _) in p['conds']]
                    if p['good']:
                        parts += ['hstatic', 'hacc']
                    parts += ['hcg', 'z', 'w', 'hz', 'hzr']
                    lines.append(f'{pad}exact ' + inj(t[1]).format('⟨' + ', '.join(parts) + '⟩'))
                else:
                    lines.append(f'{pad}obtain ⟨hcg, -, ho, hgas, hst, hss⟩ := {ok_ex} '
                                 f'(B := {p["bound"]}) (cost := {p["cost"]}){hB} '
                                 f'(fun g hg => {p["name"]} {call} (by omega)) start {hrun} hok')
                    parts = [cn for (cn, _, _) in p['conds']]
                    if p['good']:
                        parts += ['hstatic', 'hacc']
                    parts += ['hcg', 'ho', 'hgas', 'hst', 'hss']
                    lines.append(f'{pad}exact ' + inj(t[1]).format('⟨' + ', '.join(parts) + '⟩'))

        emit(tree, 1)
        if not oks:
            disj = ['False']
        head = ([f'theorem ok_{self.fname} ' + ''.join(b + ' ' for b in getattr(self, 'okbind', [])
                                                       if self.kind == 'segment')
                 + '(hfork : .berlin ≤ fork)']
                + ['    ' + h for h in self.okhy])
        if lg:
            head += ['    {gas : Nat} {evm s : Evm fork Nat}',
                     f'    (start : At {self.pre[4:-1]} evm)',
                     '    (hrun : EndsL runChild evm s) (hok : s.error = none) :']
        elif rf:
            head += ['    {gas bound : Nat} {runChild : MessageRunner fork Nat bound} '
                     '{evm s : Evm fork Nat}',
                     f'    (start : At {self.pre[4:-1]} evm)',
                     '    (within : GasMeter.gasHeld evm.gas ≤ bound)',
                     f'    (hrun : {RUN} evm within = .ok s) (hok : s.error = none) :']
        else:
            head += ['    {gas : Nat} {evm s : Evm fork Nat}',
                     '    (start : At CODE message 0 [] .empty gas state substate evm)',
                     '    (hrun : Ends fork evm s) (hok : s.error = none) :']
        head += ['    ' + ' ∨\n      '.join(disj) + ' := by'] + ['  ' + x for x in self.oklead]
        out = '\n'.join(head + lines) + '\n'
        if self.kind == 'segment' and self.post_def and lg:
            # `post_def` of a segment: the conclusion of `ok_<segment>` as a predicate, so that a
            # hand-written theorem across the opcode before the segment can state it
            vs = ' '.join(getattr(self, 'okvars', []))
            vb = f' ({vs} : U256)' if vs else ''
            n = self.fname
            out += (f'\n/-- The conclusion of `ok_{n}`, as a predicate of the state, the substate '
                    f'and the gas of the\nframe at the start of the segment and of the frame `s` '
                    f'that ends the run. -/\n'
                    f'def {n}_ends (fork : Fork) (message : Message fork) '
                    f'(state : State.TransactionState)\n    (substate : Substate) (gas : Nat) '
                    f'(s : Evm fork Nat){vb} : Prop :=\n    '
                    + ' ∨\n      '.join(disj) + '\n\n'
                    + f'/-- `ok_{n}`, stated with `{n}_ends`. -/\n'
                    + head[0].replace(f'theorem ok_{n} ', f'theorem ok_{n}_ends ') + '\n'
                    + '\n'.join(head[1:-1 - len(self.oklead)]) + '\n'
                    + f'    {n}_ends fork message state substate gas s {vs} :=\n'
                    + f'  ok_{n} ' + ' '.join(self.call0) + ' start hrun hok\n')
        return out


HEADER = '''{imports}

/-!
# {title}

Generated by `scripts/gen_paths.py` from the runtime bytecode; do not edit. Lean checks every
statement against `CODE`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

namespace {root}.{ns}

open UsdtVerify
open TokenKit
open {root}

open EthLib.Base (Fork U256)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {{fork : Fork}} {{message : Message fork}}

'''


def main():
    tok = tokenlib.load()
    only = sys.argv[2].split(',') if len(sys.argv) > 2 else None
    outdir = os.path.join(tok.lean_dir, 'Gen')
    R, MOD = tok.root, tok.mod
    code, ins = load(tok.code)
    g = Gen(ins, tok)
    os.makedirs(outdir, exist_ok=True)
    summary = {}
    ptexts = {}
    rfs = set()
    # mode `walk`: a function of `readonly_loops` gets the path from pc 0 to its entry in the
    # table (`<fn>Entry`), where gen_loops.py takes over
    entries = ([dict(f, name=f['name'] + 'Entry', entry_of=f['name']) for f in tok.loops]
               if g.walk_mode else [])
    for f in tok.funcs + tok.fallbacks + tok.segments + getattr(tok, 'prefixes', []) + entries:
        fname = f['name']
        if only and fname not in only:
            continue
        g.stops = frozenset(tok.stops) | ({f['dest']} if 'entry_of' in f else set())
        tree = g.function(f)
        comp = g.complete(tree)
        ptexts[fname] = (list(g.paths), comp)
        if g.rf:
            rfs.add(fname)
        head = (dict(selector=f'0x{f["selector"]:08x}', index=f['index']) if 'kind' not in f
                else dict(kind=f['kind']))
        summary[fname] = dict(head, paths=[
            {k: v for k, v in p.items() if k != 'text'} for p in g.paths])
    # block lemmas, in chunks
    CH = 40
    chunks = [g.lemmas[i:i + CH] for i in range(0, len(g.lemmas), CH)]
    for old in os.listdir(outdir):
        if old.endswith('.lean') and (old[0] == 'B' or old[0] == 'P'):
            os.remove(os.path.join(outdir, old))
    bimports = []
    for i, ch in enumerate(chunks):
        mod = f'B{i}'
        bimports.append(f'import {MOD}.Gen.{mod}')
        with open(os.path.join(outdir, mod + '.lean'), 'w') as f:
            f.write(HEADER.format(imports=''.join(f'import {m}\n' for m in tok.cfg.get('paths', {}).get('block_imports', [])) +
                                          ('import TokenKit.Evm.RawMem\n' if Block.RAWW else '') +
                                          (f'import TokenKit.Evm.SafeL\nimport TokenKit.Evm.Prune\n'
                                           f'import TokenKit.Evm.Stack\n'
                                           f'import {MOD}.Map' if g.walk_mode
                                           else f'import {MOD}.Enter'), root=R,
                                  title=f'Block lemmas of {tok.name}, part {i}', ns='Blocks'))
            for name, text in ch:
                f.write(text + '\n')
            f.write(f'end {R}.Blocks\n')
    mods = [f'B{i}' for i in range(len(chunks))]
    for fname, (paths, comp) in ptexts.items():
        mod = 'P' + fname[0].upper() + fname[1:]
        mods.append(mod)
        # mode `walk`: the paths of a fallback come before the completeness of the dispatcher
        early = g.walk_mode and fname in [x['name'] for x in tok.fallbacks]
        with open(os.path.join(outdir, mod + '.lean'), 'w') as f:
            f.write(HEADER.format(
                imports='\n'.join(bimports + ['import UsdtVerify.Evm.Exact']
                                  + (['import UsdtVerify.Evm.Split'] if fname in rfs else [])
                                  + ([] if early else [f'import {MOD}.Complete.Dispatch'])
                                  + [f'import {m}' for m in tok.cfg.get('paths_imports', [])]),
                root=R,
                title=f'The paths of {fname} and their completeness', ns='Paths'))
            f.write(f'open {R}.Blocks {"" if early else R + ".Complete "}UsdtVerify.Complete UsdtVerify.Gas'
                    f'{" TokenKit.Complete" if tok.logic else ""}\n\n')
            f.write('variable {state : State.TransactionState} {substate : Substate}\n\n')
            if tok.logic:
                f.write('variable {bound : Nat} {runChild : MessageRunner fork Nat bound}\n\n')
            for p in paths:
                f.write(p['text'] + '\n')
            if comp is not None:
                f.write(comp + '\n')
            f.write(f'end {R}.Paths\n')
    with open(os.path.join(tok.lean_dir, 'Gen.lean'), 'w') as f:
        f.write('\n'.join(f'import {MOD}.Gen.{m}' for m in mods) + '\n')
    summary['_blocks'] = len(g.lemmas)
    summary['_pruned'] = [dict(function=a, pc=b, decided_by=c) for a, b, c in g.pruned]
    json.dump(summary, open(tok.paths_json, 'w'), indent=1)
    for fname, (paths, _) in ptexts.items():
        kinds = [p['kind'] for p in paths]
        print(fname, len(paths), 'paths:', {k: kinds.count(k) for k in sorted(set(kinds))})
    print('blocks', len(g.lemmas), 'pruned branches', len(g.pruned))
    for k in g.dead:
        if k not in g.dead_used and (only is None or k[0] in only):
            print('dead branch not met:', k, file=sys.stderr)


if __name__ == '__main__':
    main()

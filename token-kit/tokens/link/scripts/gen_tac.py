"""Generate the block lemmas of transferAndCall (LinkVerify/Link/Tac/Blocks*.lean).

Each block is a straight run of the bytecode. The walk keeps the stack as Lean terms, the
memory as a term over the memory `mem` of the block start, its size, the words it is known to
hold, and the natural number of each offset on the stack. It prints, for each block:

- `def <name>Mem`: the memory at the end of the block;
- `theorem <name>_mem`: the size of that memory and the words it holds;
- `theorem <name>`: the triple of the block.

Usage: python3 gen_tac.py <disassembly> <out dir>
"""
import re
import os
import sys
from tacsym import Walk, load_dis, lit, tm

MASK = (1 << 160) - 1
TGT = "message.currentTarget"
T1 = 100389287136786176327247604509743168900146139575972864366142685224231313322991
T2 = 102029017914606134723578916497158998599466540794523729785997104939909681925142
SYMS = ["F", "W", "N", "K", "R", "S", "S'", "S0", "S1", "S2"]


class Lin:
    """A natural number as a sum of symbols and a constant."""

    def __init__(self, d=None, k=0):
        self.d = {s: c for s, c in (d or {}).items() if c != 0}
        self.k = k

    def __add__(self, o):
        d = dict(self.d)
        for s, c in o.d.items():
            d[s] = d.get(s, 0) + c
        return Lin(d, self.k + o.k)

    def __sub__(self, o):
        d = dict(self.d)
        for s, c in o.d.items():
            d[s] = d.get(s, 0) - c
        return Lin(d, self.k - o.k)

    def key(self):
        return (tuple(sorted(self.d.items())), self.k)

    def __eq__(self, o):
        return isinstance(o, Lin) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def __str__(self):
        pos, neg = [], []
        for s in sorted(self.d, key=lambda x: SYMS.index(x)):
            c = self.d[s]
            t = s if abs(c) == 1 else "%d * %s" % (abs(c), s)
            (pos if c > 0 else neg).append(t)
        if self.k > 0 or not pos:
            pos.append(str(max(self.k, 0)))
        out = " + ".join(pos)
        for t in neg:
            out += " - " + t
        if self.k < 0:
            out += " - %d" % (-self.k)
        return out


def L(s=None, k=0):
    return Lin({s: 1} if s else {}, k)


def lb(x):
    """A lower bound of `x`, from F >= 128, R <= N and the other symbols >= 0."""
    d, k = dict(x.d), x.k
    r = d.pop("R", 0)
    if r < 0:
        if d.get("N", 0) < -r:
            return None
        d["N"] = d["N"] + r
    for s, c in d.items():
        if c < 0:
            return None
        if s == "F":
            k += 128 * c
    return k


def disjoint(a, o):
    """Whether the words at the offsets `a` and `o` are known not to overlap."""
    x, y = lb(o - a), lb(a - o)
    return (x is not None and x >= 32) or (y is not None and y >= 32)



def split_term(t):
    """The head and the arguments of the application `(f a b ...)`."""
    if not (t.startswith("(") and t.endswith(")")):
        return None
    out, depth, cur = [], 0, ""
    for ch in t[1:-1]:
        if ch == " " and depth == 0:
            out.append(cur)
            cur = ""
            continue
        depth += ch == "("
        depth -= ch == ")"
        cur += ch
    out.append(cur)
    return out


def abstract(stack):
    """Replace the entries that mention the state or the memory by variables."""
    out, seen = [], {}
    for t in stack:
        if isinstance(t, str) and re.search(r"\b(state|substate|mem|c)\b", t):
            if t not in seen:
                seen[t] = "x%d" % len(seen)
            t = seen[t]
        out.append(t)
    return out


class Blk(Walk):
    def __init__(self, ops, pc, stack, mem="mem", sz=None, hs="hsz", words=None, nat=None,
                 st="state", ss="substate", newsz=None, inb=(), folds=None, renat=None,
                 canon=()):
        super().__init__(ops, pc, stack)
        self.mem0 = mem
        self.mem = mem
        self.sz = sz
        self.hs = hs
        self.words = dict(words or {})  # Lin -> (word, fact)
        self.nat = dict(nat or {})  # term -> (Lin, proof)
        self.st0, self.ss0 = st, ss
        self.st, self.ss = st, ss
        self.n = 0
        self.facts = []
        self.hyps = []  # (name, statement)
        self.hacc = "hacc"
        self.has_sstore = False
        self.newsz = dict(newsz or {})
        self.inb = set(inb)
        self.folds = dict(folds or {})
        self.renat = dict(renat or {})
        self.canon = set(canon)
        self.codeword = None

    def fresh(self, p):
        self.n += 1
        return "%s%d" % (p, self.n)

    def fact(self, line):
        self.emit(line)
        self.facts.append("  " + line)

    def natof(self, t):
        if isinstance(t, int):
            return Lin(k=t), "(show (%d : U256).toNat = %d by decide)" % (t, t)
        if t in self.nat:
            return self.nat[t]
        m = re.fullmatch(r"\((\d+) : U256\)", t)
        if m:
            return Lin(k=int(m.group(1))), "(show (%s : U256).toNat = %s by decide)" % (m.group(1), m.group(1))
        p = split_term(t)
        if p and p[0] in ("add", "sub") and len(p) == 3:
            na, nb = self.natof(p[1]), self.natof(p[2])
            if na and nb:
                h = self.fresh("hn")
                lin = na[0] + nb[0] if p[0] == "add" else na[0] - nb[0]
                self.fact("have %s : %s.toNat = %s := (toNat_%s' (x := %s) (y := %s) %s %s (by omega)).trans (by omega)" % (
                    h, t, lin, p[0], na[0], nb[0], na[1], nb[1]))
                self.nat[t] = (lin, h)
                return self.nat[t]
        return None

    def after(self, pc):
        if pc in self.folds:
            new, proof = self.folds[pc]
            self.fold(new, proof)
        if pc in self.renat:
            t = self.stack[0]
            h = self.fresh("hn")
            self.fact("have %s : %s.toNat = %s := by omega" % (h, t, self.renat[pc]))
            self.nat[t] = (self.renat[pc], h)
        if pc in self.canon:
            t = self.stack[0]
            lin, h = self.natof(t)
            new = "(BitVec.ofNat 256 (%s))" % lin
            self.fold(new, "ofNat_of_toNat %s" % h)
            h2 = self.fresh("hn")
            self.fact("have %s : %s.toNat = %s := (congrArg BitVec.toNat (ofNat_of_toNat %s)).symm.trans %s" % (
                h2, new, lin, h, h))
            self.nat[new] = (lin, h2)

    def step(self, taken=None, hyp=None):
        pc = self.pc
        name, _ = self.ops[pc]
        st = self.stack
        if name in ("ADD", "SUB") and len(st) >= 2:
            a, b = st[0], st[1]
            na, nb = self.natof(a), self.natof(b)
            ok = super().step(taken, hyp)
            if na and nb and not (isinstance(a, int) and isinstance(b, int)):
                res = st[0]
                h = self.fresh("hn")
                if name == "ADD":
                    lin = na[0] + nb[0]
                    lem = "toNat_add'"
                else:
                    lin = na[0] - nb[0]
                    lem = "toNat_sub'"
                self.fact("have %s : %s.toNat = %s := (%s (x := %s) (y := %s) %s %s (by omega)).trans (by omega)" % (
                    h, res, lin, lem, na[0], nb[0], na[1], nb[1]))
                self.nat[res] = (lin, h)
        elif name == "JUMPI":
            cond = st[1]
            ok = super().step(taken, hyp)
            self.hyps.append((hyp, "%s %s 0" % (tm(cond), "≠" if taken else "=")))
        else:
            ok = super().step(taken, hyp)
        if ok:
            self.after(pc)
        return ok

    # --- memory ---------------------------------------------------------------------------

    def mload(self):
        t = self.stack[0]
        e, p = self.natof(t)
        if e in self.words:
            w, f = self.words[e]
        else:
            w, f = "(loadWord (memoryReadBytes %s (%s) 32) 0 32)" % (self.mem, e), "rfl"
        self.emit("step mloadK (by code_fact) (by code_fact) %s (o := %s) %s (by omega) %s (by gas_ok)"
                  % (self.hs, e, p, f))
        self.stack[0] = w
        self.gas += 3
        self.pc += 1

    def mstore(self):
        pc = self.pc
        t, v0 = self.stack.pop(0), self.stack.pop(0)
        e, p = self.natof(t)
        need = Lin(e.d, (e.k + 32 + 31) // 32 * 32)
        if pc in self.newsz:
            newsz = self.newsz[pc]
        elif pc in self.inb or (lb(self.sz - need) is not None and lb(self.sz - need) >= 0):
            newsz = self.sz
        elif lb(need - self.sz) is not None and lb(need - self.sz) >= 0:
            newsz = need
        else:
            raise Exception("size at %d: %s in %s" % (pc, e, self.sz))
        v = tm(v0)
        self.emit("step mstoreS (by code_fact) (by code_fact) %s (by omega) (o := %s) %s (sz' := %s) (by omega) (by gas_ok)"
                  % (self.hs, e, p, newsz))
        args = "(v := %s) (o := %s) (sz' := %s)" % (v, e, newsz)
        words = {}
        for a, (w, f) in self.words.items():
            if disjoint(a, e):
                h = self.fresh("hw")
                self.fact("have %s := load_wr_ne %s %s %s (by omega) (by omega) (by omega) (by omega)"
                          % (h, args, f, self.hs))
                words[a] = (w, h)
        h = self.fresh("hw")
        self.fact("have %s := load_wr_self %s %s (by omega) (by omega)" % (h, args, self.hs))
        words[e] = (v0, h)
        hs = self.fresh("hs")
        self.fact("have %s := size_wr %s %s (by omega) (by omega)" % (hs, args, self.hs))
        self.mem = "(memoryWrite (memoryExtend %s (%s - (%s))) (%s) (wordBytes %s))" % (
            self.mem, newsz, self.sz, e, v)
        if not (newsz == self.sz):
            self.gsym.append("(memoryGasCost (%s) - memoryGasCost (%s))" % (newsz, self.sz))
        self.words, self.hs, self.sz = words, hs, newsz
        self.gas += 3
        self.pc += 1

    def calldataload(self):
        t = self.stack[0]
        n = self.natof(t)
        if n:
            o, p = str(n[0]), n[1]
        else:
            o, p = "%s.toNat" % tm(t), "rfl"
        self.emit("step calldataloadK (by code_fact) (by code_fact) (o := %s) %s (by gas_ok)" % (o, p))
        self.stack[0] = "(loadWord message.data %s 32)" % o
        self.gas += 3
        self.pc += 1

    def calldatacopy(self):
        pc = self.pc
        dst, off, size = (self.stack.pop(0) for _ in range(3))
        e, p = self.natof(dst)
        k, pk = self.natof(size)
        assert e == self.sz, (e, self.sz)
        newsz = self.newsz[pc]
        ext = "(%s + 31) / 32 * 32" % k
        self.emit("step calldatacopyS (by code_fact) (by code_fact) %s (by omega) %s %s (by gas_ok)"
                  % (self.hs, p, pk))
        args = "(data := message.data) (f := %s.toNat) (k := %s)" % (tm(off), k)
        words = {}
        for a, (w, f) in self.words.items():
            h = self.fresh("hw")
            self.fact("have %s := load_cp %s %s %s (by omega)" % (h, args, f, self.hs))
            words[a] = (w, h)
        hs = self.fresh("hs")
        self.fact("have %s := (size_cp %s %s).trans (show %s + %s = %s by omega)" % (
            hs, args, self.hs, self.sz, ext, newsz))
        self.gsym.append("3 * ((%s + 31) / 32)" % k)
        self.gsym.append("(memoryGasCost (%s + %s) - memoryGasCost %s)" % (self.sz, ext, self.sz))
        self.mem = "(memoryWrite (memoryExtend %s (%s)) (%s) (copied message.data %s.toNat (%s)))" % (
            self.mem, ext, self.sz, tm(off), k)
        self.words, self.hs, self.sz = words, hs, newsz
        self.gas += 3
        self.pc += 1

    def sha3(self):
        a, b = self.stack.pop(0), self.stack.pop(0)
        assert a == 0 and b == 64, (a, b)
        w0, f0 = self.words[Lin(k=0)]
        w1, f1 = self.words[Lin(k=32)]
        self.emit("step keccakMapK (by code_fact) (by code_fact) %s (by omega) (read0_raw %s %s %s (by omega)) (by gas_ok)"
                  % (self.hs, f0, f1, self.hs))
        self.stack.insert(0, "(mapSlot %s %s)" % (tm(w0), tm(w1)))
        self.gas += 42
        self.pc += 1

    # --- storage, logs, accounts ----------------------------------------------------------

    def sload(self):
        key = self.stack[0]
        self.emit("step sloadK hfork (by code_fact) (by code_fact) (by gas_ok)")
        self.stack[0] = "(storageAt %s %s %s)" % (self.st, TGT, key)
        self.gsym.append("(slotCost (coldIn %s %s %s))" % (self.ss, TGT, key))
        self.hacc = "(hasAccount_readSlot %s)" % self.hacc
        self.st, self.ss = ("(readSlot %s %s %s)" % (self.st, TGT, key),
                            "(accessSlot %s %s %s)" % (self.ss, TGT, key))
        self.pc += 1

    def sstore(self):
        key, new = self.stack.pop(0), tm(self.stack.pop(0))
        self.emit("step sstoreK hfork (by code_fact) (by code_fact) hstatic %s (by gas_ok) (by gas_ok)"
                  % self.hacc)
        orig = "(originalAt %s %s %s)" % (self.st, TGT, key)
        cur = "(storageAt %s %s %s)" % (self.st, TGT, key)
        self.gsym.append("(Gas.writeCost fork %s %s %s (coldIn %s %s %s))" % (
            orig, cur, new, self.ss, TGT, key))
        self.hacc = "(hasAccount_writeSlot %s)" % self.hacc
        self.st, self.ss = ("(writeSlot %s %s %s %s)" % (self.st, TGT, key, new),
                            "(storeSub fork %s %s %s %s %s %s)" % (self.ss, TGT, key, orig, cur, new))
        self.has_sstore = True
        self.pc += 1

    def log3(self):
        s, z = self.stack.pop(0), self.stack.pop(0)
        t1, t2, t3 = (tm(self.stack.pop(0)) for _ in range(3))
        e, p = self.natof(s)
        k, pk = self.natof(z)
        if e in self.words and k == Lin(k=32):
            w, f = self.words[e]
            d = "(wordBytes %s)" % tm(w)
            hd = "(readWord_raw %s %s (by omega))" % (f, self.hs)
        else:
            d = "(memoryReadBytes %s (%s) (%s))" % (self.mem, e, k)
            hd = "rfl"
        self.emit("step log3K (by code_fact) (by code_fact) hstatic %s (o := %s) %s (k := %s) %s (by omega) (c := 1500 + 8 * (%s)) (logCost3 %s) %s (by gas_ok)"
                  % (self.hs, e, p, k, pk, k, pk, hd))
        self.gsym.append("(1500 + 8 * (%s))" % k)
        self.ss = "(logSub %s %s %s %s %s %s)" % (self.ss, TGT, t1, t2, t3, d)
        self.logdata = d
        self.pc += 1

    def extcodesize(self):
        w = tm(self.stack[0])
        self.emit("step extcodesizeL hfork (by code_fact) (by code_fact) hcode (by gas_ok)")
        self.stack[0] = "(BitVec.ofNat 256 c.size)"
        self.gsym.append("(externalBaseCost fork (coldAccount %s (toAddressMasked %s)))" % (self.ss, w))
        self.codeword, self.codest = w, self.st
        self.st, self.ss = ("(%s.recordAccountRead (toAddressMasked %s))" % (self.st, w),
                            "(accessAccount %s (toAddressMasked %s))" % (self.ss, w))
        self.pc += 1

    def exp1(self):
        """EXP of 256 to an exponent from 1 to 31."""
        a, b = self.stack.pop(0), self.stack.pop(0)
        e, p = self.natof(b)
        self.emit("step expK hfork (by code_fact) (by code_fact) (e := 1) (exponentBytes_one %s (by omega) (by omega)) (by gas_ok)" % p)
        self.stack.insert(0, "(Evm.exp %s %s)" % (tm(a), tm(b)))
        self.gas += 60
        self.pc += 1

    def ret(self):
        """The end at a RETURN of one known word."""
        e, p = self.natof(self.stack[0])
        k, pk = self.natof(self.stack[1])
        w, f = self.words[e]
        assert k == Lin(k=32)
        line = "returnK (by code_fact) (by code_fact) %s (o := %s) (k := 32) %s %s (by omega) (readWord_raw %s %s (by omega))" % (
            self.hs, e, p, pk, f, self.hs)
        return ("halt", "false", "(wordBytes %s)" % tm(w), line)

    def go(self, stop=(), branches=None):
        """Walk to a pc of `stop`, a JUMPI with no branch given, or an opcode with no rule."""
        table = {"MLOAD": self.mload, "MSTORE": self.mstore, "CALLDATALOAD": self.calldataload,
                 "CALLDATACOPY": self.calldatacopy, "SHA3": self.sha3, "SLOAD": self.sload,
                 "SSTORE": self.sstore, "LOG3": self.log3, "EXTCODESIZE": self.extcodesize,
                 "EXP": self.exp1}
        while True:
            self.run(stop=stop, branches=branches)
            pc = self.pc
            name = self.ops[pc][0]
            if pc in stop or name not in table:
                return self
            table[name]()
            self.after(pc)

    # --- output ---------------------------------------------------------------------------

    def cost(self):
        return " + ".join([str(self.gas)] + self.gsym)

    def stk(self, stack=None):
        return "[" + ", ".join(tm(x) for x in (self.stack if stack is None else stack)) + "]"


VARS = [("x0", "U256"), ("x1", "U256"), ("x2", "U256"), ("x3", "U256"), ("to", "U256"), ("value", "U256"), ("L", "U256"), ("fpw", "U256"), ("sel", "U256"),
        ("i", "U256"), ("flag", "U256"), ("c", "ByteArray"), ("mem", "ByteArray"),
        ("state", "State.TransactionState"), ("substate", "Substate"),
        ("F", "Nat"), ("N", "Nat"), ("W", "Nat"), ("K", "Nat"), ("R", "Nat"), ("S", "Nat"),
        ("S'", "Nat"), ("S0", "Nat"), ("S1", "Nat"), ("S2", "Nat")]


def uses(text, v):
    return re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(v), text) is not None


def binders(text):
    """The implicit binders of the variables that `text` mentions."""
    out = []
    for v, t in VARS:
        if uses(text, v):
            out.append("{%s : %s}" % (v, t))
    return " ".join(out)


def defsig(body):
    """The explicit binders of a def with this body, and the arguments to apply it to."""
    bs, args = [], []
    if uses(body, "fork"):
        bs.append("(fork : Fork)")
        args.append("fork")
    elif uses(body, "message"):
        bs.append("{fork : Fork}")
    if uses(body, "message"):
        bs.append("(message : Message fork)")
        args.append("message")
    for v, t in VARS:
        if uses(body, v):
            bs.append("(%s : %s)" % (v, t))
            args.append(v)
    return " ".join(bs), " ".join(args)


def hname(h):
    return h[1:].split(" ")[0]


def hstmt(h):
    return h[len(hname(h)) + 4:-1]


def sub(text, m):
    """Replace the variables of `m` in `text`, in one pass."""
    if isinstance(text, int):
        return text
    keys = sorted(m, key=len, reverse=True)
    if not keys:
        return text
    pat = r"(?<![\w.'])(%s)(?![\w'])" % "|".join(re.escape(k) for k in keys)
    return re.sub(pat, lambda x: m[x.group(1)], text)


class Out:
    def __init__(self, title, imp):
        self.s = HEAD % (imp, title)
        self.info = {}

    def define(self, name, doc, typ, body):
        bs, args = defsig(body)
        self.s += "/-- %s -/\ndef %s %s : %s :=\n  %s\n\n" % (doc, name, bs, typ, body)
        return "(%s %s)" % (name, args) if args else name

    def block(self, name, b, hyps, end):
        """Print the defs, the memory facts and the triple of the block `b`.

        end: ("at",) | ("halt", rev, out, line) | ("stuck",) | ("fault",)
        """
        cost = b.cost()
        hyps = list(hyps)
        if b.codeword is not None:
            hyps.append("(hcode : %s.getCode (%s.getAccount (toAddressMasked %s)).codeHash = .ok c)" % (
                b.codest, b.codest, b.codeword))
        conds = ["(%s : %s)" % (n, s) for n, s in b.hyps]
        hy = hyps + conds
        stack0, pc0 = b.trace[0][2], b.trace[0][0]
        memterm, stterm, ssterm, costterm = b.mem, b.st, b.ss, cost
        if b.mem != b.mem0:
            memterm = self.define(name + "Mem", "The memory after the block `%s`." % name,
                                  "ByteArray", b.mem)
            outs = ["%s.size = %s" % (memterm, b.sz)]
            pf = [b.hs]
            for a, (w, f) in b.words.items():
                outs.append("loadWord (memoryReadBytes %s (%s) 32) 0 32 = %s" % (memterm, a, tm(w)))
                pf.append(f)
            fh = [h for h in hyps if h[1:].split(" ")[0] not in ("hfork", "hstatic", "hacc", "hcode")]
            txt = " ".join(fh + outs)
            self.s += "theorem %s_mem %s\n    %s :\n    %s := by\n" % (
                name, binders(txt), "\n    ".join(fh), " ∧\n    ".join(outs))
            self.s += "\n".join(b.facts) + "\n"
            self.s += "  exact ⟨%s⟩\n\n" % ", ".join(pf)
            self.info[name + "_mem"] = (fh, [str(a) for a in b.words])
        if end[0] in ("at", "halt"):
            if b.st != b.st0:
                stterm = self.define(name + "St", "The state after the block `%s`." % name,
                                     "State.TransactionState", b.st)
            if b.ss != b.ss0:
                ssterm = self.define(name + "Ss", "The substate after the block `%s`." % name,
                                     "Substate", b.ss)
            costterm = self.define(name + "Cost", "The gas of the block `%s`." % name, "Nat", cost)
        pre = "At CODE message %d %s %s gas %s %s" % (pc0, b.stk(stack0), b.mem0, b.st0, b.ss0)

        def stmt(raw):
            m, s, x, g = (b.mem, b.st, b.ss, cost) if raw else (memterm, stterm, ssterm, costterm)
            hg = "(hg : %s + 2300 < gas)" % g if b.has_sstore else "(hg : %s ≤ gas)" % g
            if end[0] == "at":
                concl = "Logic.HoareG fork (%s)\n      (At CODE message %d %s %s (gas - (%s)) %s %s)" % (
                    pre, b.pc, b.stk(), m, g, s, x)
            elif end[0] == "halt":
                concl = "Logic.SpecG fork (%s)\n      (Halted %s %s (gas - (%s)) %s %s)" % (
                    pre, end[1], end[2], g, s, x)
            elif end[0] == "fault":
                concl = "Logic.SpecG fork (%s)\n      (Faulted (.invalidOpcode 0xfe) %s %s)" % (
                    pre, b.st, b.ss)
            else:
                concl = "Logic.HoareG fork (%s) Logic.Stuck" % pre
            txt = " ".join(hy) + concl + hg
            return "%s\n    %s\n    {gas : Nat} %s :\n    %s" % (
                binders(txt), "\n    ".join(hy), hg, concl)

        simple = end[0] in ("fault", "stuck")
        self.s += "theorem %s%s %s := by\n" % (name, "" if simple else "_raw", stmt(True))
        self.s += "\n".join(b.lines) + "\n"
        if end[0] == "at":
            self.s += "  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)\n\n"
        elif end[0] == "halt":
            self.s += "  exact haltGasL (specL (%s)) (by gas_ok)\n\n" % end[3]
        elif end[0] == "fault":
            self.s += "  exact specL (Gas.invalid_feG (by code_fact) (by code_fact))\n\n"
        else:
            self.s += "  exact stuckL (Gas.sstoreStuckW (by code_fact) (by code_fact) hbad)\n\n"
        if not simple:
            names = [h[1:].split(" ")[0] for h in hy]
            self.s += "theorem %s %s :=\n  %s_raw %s hg\n\n" % (name, stmt(False), name, " ".join(names))
        mf = None
        if b.mem != b.mem0:
            mf = dict(hyps=[hname(h) for h in self.info[name + "_mem"][0]],
                      keys=self.info[name + "_mem"][1])
        self.info[name] = dict(name=name, hyps=[(hname(h), hstmt(h)) for h in hy], mem=memterm,
                               st=stterm, ss=ssterm, cost=costterm, stack0=list(stack0),
                               stack=list(b.stack), pc0=pc0, pc=b.pc, sstore=b.has_sstore,
                               end=end[:3], gas=b.gas, hacc=b.hacc, memfacts=mf,
                               raw_st=b.st, raw_ss=b.ss, raw_mem=b.mem)
        print(name, b.pc, b.ops[b.pc][0], b.stk()[:600])
        return self.info[name]

    def write(self, path):
        self.s += "end LinkVerify.Tac\n"
        assert "\u2014" not in self.s and "\u2013" not in self.s
        open(path, "w").write(self.s)


HEAD = '''import %s

/-!
# %s

Generated by `scripts/gen_tac.py` from the runtime bytecode; do not edit. Lean checks every
statement against `CODE`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxRecDepth 8192

namespace LinkVerify.Tac

open UsdtVerify
open TokenKit
open LinkVerify

open EthLib.Base (Fork U256 Address toAddressMasked)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

'''


def stk(stack):
    return "[" + ", ".join(tm(x) for x in stack) + "]"


def loop(o, info, idx, D, DW, D32):
    """The copy loop `idx`, by induction from its body `lb<idx>` and its exit `lx<idx>`."""
    lb, lx = info["lb%d" % idx], info["lx%d" % idx]
    cb, ce = lb["gas"], lx["gas"]
    n = "lp%d" % idx
    lbm = "lb%dMem" % idx
    rest = ", ".join(tm(x) for x in lb["stack0"][1:])
    xs = stk(lx["stack"])
    pc0, pcx = lb["pc0"], lx["pc"]
    Sk = lambda k: "max S0 (F + %d + 32 * %s)" % (D, k)
    m = {"hi": "hi", "hK": "(show 32 * k %% 32 = 0 by omega)".replace("%%", "%"),
         "hKW": "(show 32 * k + 32 ≤ W by omega)", "hsz": "hs", "hSm": "(by omega)",
         "hSF": "(by omega)",
         "hS'": "(show %s = max (%s) (F + 32 * k + %d) by omega)" % (Sk("(k + 1)"), Sk("k"), D32),
         "hc": "hc"}
    args = " ".join(m.get(h, h) for h, _ in lb["hyps"])
    margs = " ".join(m.get(h, h) for h in lb["memfacts"]["hyps"])
    ctx = "\n    ".join(CTXN + ["(hS0m : S0 % 32 = 0)", "(hS0F : F + %d ≤ S0)" % D])
    cost = lambda nn, k0, k1: "%s * %d + %d + (memoryGasCost (%s) - memoryGasCost (%s))" % (
        nn, cb, ce, Sk(k1), Sk(k0))
    pre = "At CODE message %d (i :: [%s]) mem gas state substate" % (pc0, rest)
    txt = ctx + xs + "[%s]" % rest + " state substate"
    o.s += """/-- The memory after `n` more rounds of the copy loop %(idx)d, from the round `k`. -/
def %(n)sMem (F S0 : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, m => m
  | n + 1, k, m => %(n)sMem F S0 n (k + 1)
      (%(lbm)s m F (32 * k) (%(sk)s) (%(sk1)s))

/-- The size of the memory after the copy loop %(idx)d, and the bytes it leaves. -/
theorem %(n)s_mem {F S0 : Nat} (hFm : F %% 32 = 0) (hS0m : S0 %% 32 = 0) :
    ∀ (n k : Nat) (m : ByteArray), m.size = %(sk)s →
      (%(n)sMem F S0 n k m).size = %(skn)s ∧
      ∀ a j, a + j ≤ F + %(DW)d + 32 * k →
        memoryReadBytes (%(n)sMem F S0 n k m) a j = memoryReadBytes m a j := by
  intro n
  induction n with
  | zero =>
    intro k m hs
    exact ⟨hs, fun _ _ _ => rfl⟩
  | succ n ih =>
    intro k m hs
    have hb : (%(lbm)s m F (32 * k) (%(sk)s) (%(sk1)s)).size = %(sk1)s :=
      size_wr hs (by omega) (by omega)
    obtain ⟨h1, h2⟩ := ih (k + 1) _ hb
    refine ⟨h1.trans (show %(sk1n)s = %(skn1)s by omega), fun a j ha => ?_⟩
    exact (h2 a j (by omega)).trans
      (read_wr_ne hs (by omega) (by omega) (by omega) (Or.inl (by omega)))

/-- The copy loop %(idx)d: `n` more rounds from the round `k`, then the exit. -/
theorem %(n)s %(binders)s
    %(ctx)s :
    ∀ (n k : Nat) (i : U256) (mem : ByteArray) (gas : Nat), i.toNat = 32 * k → 32 * (k + n) = W →
      mem.size = %(sk)s →
      %(cost)s ≤ gas →
      Logic.HoareG fork (%(pre)s)
        (At CODE message %(pcx)d %(xs)s (%(n)sMem F S0 n k mem)
          (gas - (%(cost)s)) state substate) := by
  intro n
  induction n with
  | zero =>
    intro k i mem gas hi hk hs hg
    have hc : isZero (lessThan i L) ≠ 0 := lt_cond_stop hi hL (by omega)
    step lx%(idx)d hc (by simp only [lx%(idx)dCost]; omega)
    exact hoareL (restate rfl rfl rfl
      (by simp only [Nat.add_zero, Nat.sub_self, lx%(idx)dCost]; try omega) rfl rfl)
  | succ n ih =>
    intro k i mem gas hi hk hs hg
    have hc : isZero (lessThan i L) = 0 := lt_cond_go hi hL (by omega)
    have hm1 := memoryGasCost_mono (show %(sk)s ≤ %(sk1)s by omega)
    have hm2 := memoryGasCost_mono (show %(sk1)s ≤ %(sk1n)s by omega)
    have e : %(skn1)s = %(sk1n)s := by omega
    rw [e] at hg ⊢
    have hi' : (add (32 : U256) i).toNat = 32 * (k + 1) :=
      (toNat_add' (show (32 : U256).toNat = 32 by decide) hi (by omega)).trans (by omega)
    have hs' := (lb%(idx)d_mem (i := i) %(margs)s).1
    step lb%(idx)d %(args)s (by simp only [lb%(idx)dCost]; omega)
    refine Gas.Triple.seqL (ih (k + 1) _ _ _ hi' (by omega) hs'
      (by simp only [lb%(idx)dCost]; omega)) ?_
    exact hoareL (restate rfl rfl rfl (by simp only [lb%(idx)dCost]; omega) rfl rfl)

""" % dict(idx=idx, n=n, lbm=lbm, sk=Sk("k"), sk1=Sk("(k + 1)"), skn=Sk("(k + n)"),
           sk1n=Sk("(k + 1 + n)"), skn1=Sk("(k + (n + 1))"), DW=DW, binders=binders(txt),
           ctx=ctx, cost=cost("n", "k", "(k + n)"), pre=pre, pcx=pcx, xs=xs, args=args,
           margs=margs)
    # the whole loop, from the round 0
    c = "cp%d" % idx
    hy = CTXN + ["(hsz : mem.size = S)", "(hSm : S % 32 = 0)", "(hSa : F + %d ≤ S)" % D,
                 "(hSb : S ≤ F + W + %d)" % D]
    costt = "W / 32 * %d + %d + (memoryGasCost (F + W + %d) - memoryGasCost S)" % (cb, ce, D)
    pre = "At CODE message %d %s mem gas state substate" % (pc0, stk([0] + lb["stack0"][1:]))
    txt = " ".join(hy) + pre + xs
    e1 = "max S (F + %d + 32 * (0 + W / 32))" % D
    e2 = "max S (F + %d + 32 * 0)" % D
    o.s += """/-- The memory after the copy loop %(idx)d. -/
def %(c)sMem (mem : ByteArray) (F W S : Nat) : ByteArray := %(n)sMem F S (W / 32) 0 mem

/-- The gas of the copy loop %(idx)d. -/
def %(c)sCost (F W S : Nat) : Nat :=
  %(costt)s

theorem %(c)s_mem {L fpw : U256} {mem : ByteArray} {F N W S : Nat}
    (hF0 : 128 ≤ F) (hFm : F %% 32 = 0) (hW : W = (N + 31) / 32 * 32)
    (hsz : mem.size = S) (hSm : S %% 32 = 0) (hSa : F + %(D)d ≤ S) (hSb : S ≤ F + W + %(D)d)
    (h64 : loadWord (memoryReadBytes mem 64 32) 0 32 = fpw)
    (h96 : loadWord (memoryReadBytes mem 96 32) 0 32 = L) :
    (%(c)sMem mem F W S).size = F + W + %(D)d ∧
    loadWord (memoryReadBytes (%(c)sMem mem F W S) 64 32) 0 32 = fpw ∧
    loadWord (memoryReadBytes (%(c)sMem mem F W S) 96 32) 0 32 = L := by
  obtain ⟨h1, h2⟩ := %(n)s_mem hFm hSm (W / 32) 0 mem
    (show mem.size = %(e2)s by rw [hsz]; omega)
  refine ⟨h1.trans (by omega), ?_, ?_⟩
  · show loadWord (memoryReadBytes (%(n)sMem F S (W / 32) 0 mem) 64 32) 0 32 = fpw
    rw [h2 64 32 (by omega)]
    exact h64
  · show loadWord (memoryReadBytes (%(n)sMem F S (W / 32) 0 mem) 96 32) 0 32 = L
    rw [h2 96 32 (by omega)]
    exact h96

/-- The copy loop %(idx)d, from its first round to its exit. -/
theorem %(c)s %(binders)s
    %(hy)s
    {gas : Nat} (hg : %(c)sCost F W S ≤ gas) :
    Logic.HoareG fork (%(pre)s)
      (At CODE message %(pcx)d %(xs)s (%(c)sMem mem F W S) (gas - (%(c)sCost F W S)) state substate) := by
  have e1 : %(e1)s = F + W + %(D)d := by omega
  have e2 : %(e2)s = S := by omega
  have ec : %(c)sCost F W S = W / 32 * %(cb)d + %(ce)d +
      (memoryGasCost (%(e1)s) - memoryGasCost (%(e2)s)) := by
    simp only [%(c)sCost, e1, e2]
  rw [ec] at hg ⊢
  exact %(n)s hF hFm hFb hF0 hL hW hNF hSm hSa (W / 32) 0 (0 : U256) mem gas (by decide)
    (by omega) (by rw [e2]; exact hsz) hg

""" % dict(idx=idx, n=n, c=c, costt=costt, D=D, e1=e1, e2=e2, binders=binders(txt),
           hy="\n    ".join(hy), pre=pre, pcx=pcx, xs=xs, cb=cb, ce=ce)
    info[c] = dict(name=c, hyps=[(hname(h), hstmt(h)) for h in hy], mem="(%sMem mem F W S)" % c,
                   st="state", ss="substate", cost="(%sCost F W S)" % c,
                   stack0=[0] + lb["stack0"][1:], stack=list(lx["stack"]), pc0=pc0, pc=pcx,
                   sstore=False, end=("at",), gas=0, hacc="hacc", raw_st="state",
                   raw_ss="substate", raw_mem="(%sMem mem F W S)" % c,
                   memfacts=dict(hyps=["hF0", "hFm", "hW", "hsz", "hSm", "hSa", "hSb", "h64", "h96"],
                                 keys=["64", "96"]))


def unify(o, info, name, vn, vm):
    """One block for the two variants `vn` (the length is a multiple of 32) and `vm`."""
    a, b = info[vn], info[vm]
    RM = {"R": "(N % 32)"}
    hy = [(h, t) for h, t in a["hyps"] if h not in ("hN0", "hc")]
    names = [h for h, _ in hy]
    hy = [(h, t) for h, t in b["hyps"] if h in ("hfork", "hstatic", "hacc") and h not in names] + hy
    terms, eqs, raw = {}, [], {}
    for k, typ in (("mem", "ByteArray"), ("st", "State.TransactionState"), ("ss", "Substate"),
                   ("cost", "Nat")):
        ta, tb = a[k], sub(b[k], RM)
        if ta == tb or (k in ("st", "ss") and a["raw_" + k] == sub(b["raw_" + k], RM)):
            terms[k] = ta
            raw[k] = a.get("raw_" + k)
            continue
        dn = name + {"mem": "Mem", "st": "St", "ss": "Ss", "cost": "Cost"}[k]
        if k == "ss":
            ua = a["raw_ss"].replace("(memoryReadBytes %s " % a["raw_mem"],
                                     "(memoryReadBytes %s " % terms["mem"])
            ub = sub(b["raw_ss"], RM).replace("(memoryReadBytes %s " % sub(b["raw_mem"], RM),
                                              "(memoryReadBytes %s " % terms["mem"])
            assert ua == ub and ua != a["raw_ss"], name
            terms[k] = o.define(dn, "The substate after the block `%s`." % name, typ, ua)
            raw[k] = ua
            mn = name + "Mem"
            eqs.append((terms[k], ta, tb,
                        "(by simp only [%s, %s, if_pos h0] <;> rfl)" % (dn, mn),
                        "(by simp only [%s, %s, if_neg h0] <;> rfl)" % (dn, mn)))
            continue
        terms[k] = o.define(dn, "The %s after the block `%s`: with no padding when the length is a multiple of 32." % (
            {"mem": "memory", "st": "state", "ss": "substate", "cost": "gas"}[k], name), typ,
            "if N %% 32 = 0 then %s else %s" % (ta, tb))
        raw[k] = terms[k]
        eqs.append((terms[k], ta, tb, "if_pos h0", "if_neg h0"))
    assert a["stack"] == b["stack"] and a["stack0"] == b["stack0"]
    pre = "At CODE message %d %s mem gas state substate" % (a["pc0"], stk(a["stack0"]))
    post = "At CODE message %d %s %s (gas - (%s)) %s %s" % (
        a["pc"], stk(a["stack"]), terms["mem"], terms["cost"], terms["st"], terms["ss"])
    hys = ["(%s : %s)" % x for x in hy]
    txt = " ".join(hys) + pre + post
    ma = {"hN0": "h0", "hc": "hc"}
    mb = {"hR": "(and31_toNat hL)", "hRN": "rfl", "hR0": "(Nat.pos_of_ne_zero h0)", "hc": "hc"}
    rw = lambda i: "simp only [%s]" % ", ".join(
        "show %s = %s from %s" % (e[0], e[1 + i], e[3 + i]) for e in eqs)
    o.s += """theorem %(name)s %(binders)s
    %(hys)s
    {gas : Nat} (hg : %(cost)s ≤ gas) :
    Logic.HoareG fork (%(pre)s)
      (%(post)s) := by
  by_cases h0 : N %% 32 = 0
  · have hc : isZero (bitwiseAnd (31 : U256) L) ≠ 0 := isZero_of_toNat ((and31_toNat hL).trans h0)
    %(rwa)s at hg ⊢
    exact %(vn)s %(argsa)s hg
  · have hc : isZero (bitwiseAnd (31 : U256) L) = 0 :=
      isZero_of_toNat_pos (and31_toNat hL) (Nat.pos_of_ne_zero h0)
    %(rwb)s at hg ⊢
    exact %(vm)s (R := N %% 32) %(argsb)s hg

""" % dict(name=name, binders=binders(txt), hys="\n    ".join(hys), cost=terms["cost"], pre=pre,
           post=post, rwa=rw(0), rwb=rw(1), vn=vn, vm=vm,
           argsa=" ".join(ma.get(h, h) for h, _ in a["hyps"]),
           argsb=" ".join(mb.get(h, h) for h, _ in b["hyps"]))
    # the facts of the memory
    fh = [h for h in hys if hname(h) not in ("hfork", "hstatic", "hacc", "hcode", "hc2")]
    mt = terms["mem"]
    outs = ["%s.size = %s" % (mt, hstmt([h for h in hys if hname(h) == "hsz"][0]).split(" = ")[1]),
            "loadWord (memoryReadBytes %s 64 32) 0 32 = fpw" % mt,
            "loadWord (memoryReadBytes %s 96 32) 0 32 = L" % mt]

    def facts(v, mp, extra):
        mf = v["memfacts"]
        if mf is None:
            return "exact ⟨hsz, h64, h96⟩"
        pat = ["hs"] + [{"64": "ha", "96": "hb"}.get(k, "_") for k in mf["keys"]]
        return "obtain ⟨%s⟩ := %s_mem %s%s\n    exact ⟨hs, ha, hb⟩" % (
            ", ".join(pat), v["name"], extra, " ".join(mp.get(h, h) for h in mf["hyps"]))
    memeq = [e for e in eqs if e[0] == mt]
    if memeq:
        t, ta, tb = memeq[0][:3]
        o.s += """theorem %(name)s_mem %(binders)s
    %(fh)s :
    %(outs)s := by
  by_cases h0 : N %% 32 = 0
  · rw [show %(t)s = %(ta)s from if_pos h0]
    %(fa)s
  · rw [show %(t)s = %(tb)s from if_neg h0]
    %(fb)s

""" % dict(name=name, binders=binders(" ".join(fh + outs)), fh="\n    ".join(fh),
           outs=" ∧\n    ".join(outs), t=t, ta=ta, tb=tb, fa=facts(a, ma, ""),
           fb=facts(b, mb, "(R := N % 32) "))
        mf = dict(hyps=[hname(h) for h in fh], keys=["64", "96"])
    else:
        mf = None
    info[name] = dict(name=name, hyps=hy, mem=terms["mem"], st=terms["st"], ss=terms["ss"],
                      cost=terms["cost"], stack0=a["stack0"], stack=a["stack"], pc0=a["pc0"],
                      pc=a["pc"], sstore=False, end=("at",), gas=0, hacc="hacc", memfacts=mf,
                      raw_st=raw["st"], raw_ss=raw["ss"], raw_mem=terms["mem"])



PCTX = {"hfork": ".berlin ≤ fork", "hstatic": "message.isStatic = false",
        "hacc": "hasAccount state message.currentTarget",
        "hL": "(tacLen message).toNat = N", "hF": "(tacFpw (tacLen message)).toNat = F",
        "hFe": "F = W + 128", "hW": "W = (N + 31) / 32 * 32", "hN": "N < 2 ^ 64",
        "hcode": "state.getCode (state.getAccount (toAddressMasked (tacTo message))).codeHash = .ok c"}
PORDER = ["hfork", "hstatic", "hacc", "hL", "hF", "hFe", "hW", "hN", "hcode"]
DERIVED = ["hFm", "hFb", "hF0", "hNF"]
GIVEN = {"hS1": "rfl", "hS2": "rfl", "hSm": "(by omega)", "hSa": "(by omega)", "hSb": "(by omega)"}
GV = {"to": "(tacTo message)", "value": "(tacValue message)", "L": "(tacLen message)",
      "fpw": "(tacFpw (tacLen message))"}
MEMW = "(memW [(0 : U256), (0 : U256), (96 : U256)])"
CODELEMS = ["getCode_writeSlot", "getAccount_writeSlot", "getAccount_readSlot", "getCode_readSlot",
"getAccount_rar", "getCode_rar", "toAddressMasked_mask'"]
TACV = {"F": "(tacF message)", "N": "(tacN message)", "W": "(tacW message)"}


def path(o, info, name, doc, units, over=None, size=None):
    """The triple of a whole path from the entry of the function at 530."""
    over = over or {}
    cur = dict(stack=["sel"], mem=MEMW, st="state", ss="substate", hsz=None, h64=None,
               h96=None, hacc="hacc", rst="state", rss="substate", rstack=["sel"])
    used = {"hL", "hF", "hFe", "hW", "hN"}
    conds, lines, costs, olines = [], [], [], []
    sstore = False
    for ui, (un, vm) in enumerate(units):
        u = info[un]
        k = ui + 1
        last = ui == len(units) - 1
        m = dict(GV)
        m.update(vm)
        assert len(u["stack0"]) == len(cur["stack"]), un
        for pos, t in enumerate(u["stack0"]):
            if isinstance(t, str) and re.fullmatch(r"x\d", t):
                m[t] = tm(cur["stack"][pos])
        m.update(mem=cur["mem"], state=cur["st"], substate=cur["ss"])
        for pos, t in enumerate(u["stack0"]):
            assert sub(tm(t), m) == tm(cur["stack"][pos]), (un, pos, t, cur["stack"][pos])
        mr = dict(m)
        for pos, t in enumerate(u["stack0"]):
            if isinstance(t, str) and re.fullmatch(r"x\d", t):
                mr[t] = tm(cur["rstack"][pos])
        mr.update(state=cur["rst"], substate=cur["rss"])

        def arg(h, t, facts=False):
            if h in ("hsz", "h64", "h96"):
                return cur[h]
            if h == "hacc":
                used.add(h)
                if cur["st"] == "state":
                    return "hacc"
                return "(show hasAccount %s message.currentTarget from %s)" % (cur["st"], cur["hacc"])
            if h == "hcode":
                used.add(h)
                nm = "hcode%d" % k
                defs = sorted(set(re.findall(r"\b(\w+St)\b", cur["st"])))
                lines.append("  have %s : %s := by\n    simpa only [%s] using hcode" % (
                    nm, sub(t, m), ", ".join(defs + CODELEMS)))
                return nm
            if h in PCTX:
                used.add(h)
                return h
            if h in DERIVED:
                return h
            if h in GIVEN:
                return GIVEN[h]
            if (un, h) in over:
                return over[(un, h)]
            assert not facts, (un, h)
            nm = "%s_%s" % (h, un)
            conds.append((nm, sub(t, mr)))
            return "(show %s from %s)" % (sub(t, m), nm)
        args = " ".join(arg(h, t) for h, t in u["hyps"])
        named = "".join("(%s := %s) " % (v, t) for v, t in vm.items())
        sstore = sstore or u["sstore"]
        costs.append(sub(u["cost"], m))
        kind = u["end"][0]
        if not last or kind == "at":
            assert kind == "at", un
            lines.append("  step %s %s%s (by omega)" % (un, named, args))
        elif kind == "halt":
            lines.append("  exact haltGasL (%s %s%s (by omega)) (by omega)" % (un, named, args))
        else:
            lines.append("  exact %s %s%s (by omega)" % (un, named, args))
        if u["memfacts"] and (not last or kind == "at"):
            mf = u["memfacts"]
            hs_, a_, b_ = "hsz%d" % k, "h64_%d" % k, "h96_%d" % k
            pat = [hs_] + [{"64": a_, "96": b_}.get(x, "_") for x in mf["keys"]]
            byname = dict(u["hyps"])
            margs = " ".join(arg(h, byname.get(h, ""), True) for h in mf["hyps"])
            ol = "  obtain ⟨%s⟩ := %s_mem %s%s" % (", ".join(pat), un, named, margs)
            olines.append(ol)
            if not last:
                lines.insert(len(lines) - 1, ol)
            newh = dict(hsz=hs_, h64=a_, h96=b_)
        else:
            newh = {}
        cur = dict(stack=[sub(t, m) for t in u["stack"]], mem=sub(u["mem"], m),
                   st=sub(u["st"], m), ss=sub(u["ss"], m),
                   hsz=newh.get("hsz", cur["hsz"]), h64=newh.get("h64", cur["h64"]),
                   h96=newh.get("h96", cur["h96"]),
                   hacc=sub(u["hacc"], {"hacc": cur["hacc"]}),
                   rst=sub(u["raw_st"], mr), rss=sub(u["raw_ss"], mr),
                   rstack=[sub(t, mr) for t in u["stack"]])
    u = info[units[-1][0]]
    kind = u["end"][0]
    pc = u["pc"]
    cn = name[0].lower() + name[1:]
    costt = o.define(cn + "Cost", "The gas of the path `%s`." % name, "Nat", " + ".join(costs))
    stt, sst, memt = cur["st"], cur["ss"], cur["mem"]
    assert kind != "at" or cur["rstack"] == cur["stack"], name
    if kind != "stuck":
        if stt != "state":
            stt = o.define(cn + "St", "The state at the end of the path `%s`." % name,
                           "State.TransactionState", cur["rst"])
        if sst != "substate":
            sst = o.define(cn + "Ss", "The substate at the end of the path `%s`." % name,
                           "Substate", cur["rss"])
    if kind == "at":
        memt = o.define(cn + "Mem", "The memory at the end of the path `%s`." % name,
                        "ByteArray", cur["mem"])
    hg = "(hg : %s + 2300 < gas)" % costt if sstore else "(hg : %s ≤ gas)" % costt
    pre = "At CODE message 530 [sel] %s gas state substate" % MEMW
    if kind == "at":
        concl = "Logic.HoareG fork (%s)\n      (At CODE message %d %s %s (gas - (%s)) %s %s)" % (
            pre, pc, stk(cur["stack"]), memt, costt, stt, sst)
        lines.append("  exact hoareL (restate rfl rfl rfl (by omega) rfl rfl)")
    elif kind == "halt":
        concl = "Logic.SpecG fork (%s)\n      (Halted %s %s (gas - (%s)) %s %s)" % (
            pre, u["end"][1], sub(u["end"][2], m), costt, stt, sst)
    elif kind == "fault":
        concl = "Logic.SpecG fork (%s)\n      (Faulted (.invalidOpcode 0xfe) %s %s)" % (pre, stt, sst)
    else:
        concl = "Logic.HoareG fork (%s) Logic.Stuck" % pre
    hy = [(h, PCTX[h]) for h in PORDER if h in used] + conds
    hys = ["(%s : %s)" % x for x in hy]
    txt = " ".join(hys) + concl + hg
    o.s += "/-- %s Stated for the numbers `F`, `N`, `W` of the length. -/\n" % doc
    o.s += "theorem %s_gen %s\n    %s\n    {gas : Nat} %s :\n    %s := by\n" % (
        name, binders(txt), "\n    ".join(hys), hg, concl)
    o.s += "  have hFm : F % 32 = 0 := by omega\n  have hFb : F < 2 ^ 128 := by omega\n"
    o.s += "  have hF0 : 128 ≤ F := by omega\n  have hNF : W + 128 ≤ F := by omega\n"
    o.s += "  simp only [%sCost] at hg%s\n" % (cn, " ⊢" if kind in ("at", "halt") else "")
    o.s += "\n".join(lines) + "\n\n"
    # the same for the numbers of the message
    skip = ("hL", "hF", "hFe", "hW")
    hys2 = ["(%s : %s)" % (h, sub(t, TACV)) for h, t in hy if h not in skip]
    hg2, concl2 = sub(hg, TACV), sub(concl, TACV)
    txt = " ".join(hys2) + concl2 + hg2
    give = {"hL": "rfl", "hF": "(tacFpw_toNat rfl hN)", "hFe": "rfl", "hW": "rfl"}
    o.s += "/-- %s -/\n" % doc
    o.s += "theorem %s %s\n    %s\n    {gas : Nat} %s :\n    %s :=\n" % (
        name, binders(txt), "\n    ".join(hys2), hg2, concl2)
    o.s += "  %s_gen (F := tacF message) (N := tacN message) (W := tacW message) %s hg\n\n" % (
        name, " ".join(give.get(h, h) for h, _ in hy))
    if kind == "at":
        outs = ["%s.size = %s" % (memt, size),
                "loadWord (memoryReadBytes %s 64 32) 0 32 = %s" % (memt, GV["fpw"]),
                "loadWord (memoryReadBytes %s 96 32) 0 32 = %s" % (memt, GV["L"])]
        hm = ["(%s : %s)" % (h, PCTX[h]) for h in ("hL", "hF", "hFe", "hW", "hN")]
        o.s += "theorem %s_mem_gen {F N W : Nat}\n    %s :\n    %s := by\n" % (
            name, "\n    ".join(hm), " ∧\n    ".join(outs))
        o.s += "  have hFm : F % 32 = 0 := by omega\n  have hFb : F < 2 ^ 128 := by omega\n"
        o.s += "  have hF0 : 128 ≤ F := by omega\n  have hNF : W + 128 ≤ F := by omega\n"
        o.s += "\n".join(olines) + "\n"
        o.s += "  exact ⟨%s, %s, %s⟩\n\n" % (cur["hsz"], cur["h64"], cur["h96"])
        o.s += "theorem %s_mem (hN : tacN message < 2 ^ 64) :\n    %s :=\n" % (
            name, sub(" ∧\n    ".join(outs), TACV))
        o.s += "  %s_mem_gen (F := tacF message) (N := tacN message) (W := tacW message) rfl (tacFpw_toNat rfl hN) rfl rfl hN\n\n" % name
    r = dict(name=name, hyps=[(h, sub(t, TACV)) for h, t in hy if h not in skip],
             stack=[sub(t, TACV) for t in cur["stack"]], mem=sub(memt, TACV), st=sub(stt, TACV),
             ss=sub(sst, TACV), cost=sub(costt, TACV), pc=pc, sstore=sstore, kind=kind,
             concl=concl2, hg=hg2)
    info["path:" + name] = r
    print("PATH", name, [h for h, _ in r["hyps"]])
    return r



CTXF = ["(hF : fpw.toNat = F)", "(hFm : F % 32 = 0)", "(hFb : F < 2 ^ 128)", "(hF0 : 128 ≤ F)"]
CTXN = CTXF + ["(hL : L.toNat = N)", "(hW : W = (N + 31) / 32 * 32)", "(hNF : W + 128 ≤ F)"]
NAT = {"fpw": (L("F"), "hF"), "L": (L("N"), "hL")}
AUTO = [("hfork", "(hfork : .berlin ≤ fork)"), ("hstatic", "(hstatic : message.isStatic = false)"),
        ("hacc", "(hacc : hasAccount state message.currentTarget)")]


def MH(sz):
    return ["(hsz : mem.size = %s)" % sz,
            "(h64 : loadWord (memoryReadBytes mem 64 32) 0 32 = fpw)",
            "(h96 : loadWord (memoryReadBytes mem 96 32) 0 32 = L)"]


def W0():
    return {Lin(k=64): ("fpw", "h64"), Lin(k=96): ("L", "h96")}


def auto(b, hyps, extra=""):
    txt = "\n".join(b.lines) + extra
    return [h for k, h in AUTO if re.search(r"\b%s\b" % k, txt)] + list(hyps)


REVERT = ("halt", "true", "ByteArray.empty", "revert0K hfork (by code_fact) (by code_fact)")


def main():
    ops = load_dis(sys.argv[1])
    out = sys.argv[2]
    info = {}
    FW = lambda k: Lin({"F": 1, "W": 1}, k)

    def blk(o, name, b, hyps, end=("at",)):
        extra = end[3] if end[0] == "halt" else ""
        r = o.block(name, b, auto(b, hyps, extra), end)
        info[name] = r
        return r

    def B(pc, stack, sz, **kw):
        kw.setdefault("words", W0())
        kw.setdefault("nat", NAT)
        return Blk(ops, pc, abstract(stack), sz=sz, **kw)

    # ---- A: the entry block and the test of the recipient ---------------------------------
    o = Out("transferAndCall: the arguments and the test of the recipient",
            "LinkVerify.Link.Tac.Args")
    b = Blk(ops, 530, ["sel"], mem="(memW [(0 : U256), (0 : U256), (96 : U256)])", sz=Lin(k=96),
            hs="(size_memW3 (0 : U256) (0 : U256) (96 : U256))",
            words={Lin(k=64): (96, "(memW_load64 (0 : U256) (0 : U256) (96 : U256) [])")},
            nat={"(tacLen message)": (L("N"), "hL"), "(tacFpw (tacLen message))": (L("F"), "hF")},
            newsz={604: L("F")},
            folds={546: ("(tacTo message)", "rfl"), 551: ("(tacValue message)", "rfl"),
                   559: ("(tacOff message)", "rfl"), 566: ("(tacLen message)", "rfl"),
                   585: ("(tacFpw (tacLen message))", "rfl")})
    b.go(stop=(1277,))
    blk(o, "dec", b, ["(hL : (tacLen message).toNat = N)",
                      "(hF : (tacFpw (tacLen message)).toNat = F)", "(hFe : F = W + 128)",
                      "(hW : W = (N + 31) / 32 * 32)", "(hN : N < 2 ^ 64)"])
    st = [96, "value", "to", 361, "sel"]
    b = Blk(ops, 1277, st).go(stop=(1332,), branches={1298: (True, "hc1"), 1328: (False, "hc2")})
    blk(o, "vr_zero", b, [], REVERT)
    b = Blk(ops, 1277, st).go(stop=(1332,), branches={1298: (False, "hc1"), 1328: (False, "hc2")})
    blk(o, "vr_self", b, [], REVERT)
    b = Blk(ops, 1277, st).go(stop=(2618,), branches={1298: (False, "hc1"), 1328: (True, "hc2")})
    st = blk(o, "vr_ok", b, [])["stack"]
    o.write(out + "/BlocksA.lean")

    # ---- B: the transfer ------------------------------------------------------------------
    o = Out("transferAndCall: the transfer of the tokens", "LinkVerify.Link.Tac.Args")
    H = CTXF + MH("F")
    b = B(2618, st, L("F")).go(stop=(2606,), branches={2605: (False, "hc3")})
    blk(o, "xf_low", b, H, ("fault",))
    b = B(2618, st, L("F")).go(stop=(2659,), branches={2605: (True, "hc3")})
    st = blk(o, "xf1", b, H)["stack"]
    b = B(2659, st, L("F")).go(stop=(2689,))
    blk(o, "xf2_stuck", b, H + ["(hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)"],
        ("stuck",))
    b = B(2659, st, L("F")).go(stop=(2824,), branches={2823: (False, "hc4")})
    blk(o, "xf_over", b, H, ("fault",))
    b = B(2659, st, L("F")).go(stop=(2712,), branches={2823: (True, "hc4")})
    st = blk(o, "xf2", b, H)["stack"]
    b = B(2712, st, L("F")).go(stop=(2376,))
    st = blk(o, "xf3", b, H)["stack"]
    o.write(out + "/BlocksB.lean")

    # ---- C: the second log ----------------------------------------------------------------
    o = Out("transferAndCall: the log with the data", "LinkVerify.Link.Tac.Args")
    b = B(2376, st, L("F", 32)).go(stop=(2474,))
    st = blk(o, "lg1", b, CTXN + MH("F + 32"))["stack"]
    LOOP = ["(hi : i.toNat = K)", "(hK : K % 32 = 0)", "(hKW : K + 32 ≤ W)",
            "(hsz : mem.size = S)", "(hSm : S % 32 = 0)", "(hSF : F ≤ S)"]
    natK = dict(NAT)
    natK["i"] = (L("K"), "hi")
    b = B(2474, ["i"] + st[1:], L("S"), words={}, nat=natK, newsz={2490: L("S'")})
    b.step()
    b.go(stop=(2474,), branches={2482: (False, "hc")})
    blk(o, "lb1", b, CTXN + LOOP + ["(hS' : S' = max S (F + K + 128))"])
    b = B(2474, ["i"] + st[1:], L("S"), words={}, nat=natK)
    b.step()
    b.go(stop=(2504,), branches={2482: (True, "hc")})
    st = blk(o, "lx1", b, [])["stack"]
    HM = ["(hR : (bitwiseAnd (31 : U256) L).toNat = R)", "(hRN : R = N % 32)", "(hR0 : 0 < R)"]
    natR = dict(NAT)
    natR["(bitwiseAnd (31 : U256) L)"] = (L("R"), "hR")
    H = CTXN + MH("F + W + 96")
    b = B(2504, st, FW(96), renat={2508: FW(96)}).go(stop=(2559,), branches={2518: (True, "hc")})
    blk(o, "lg2n", b, H + ["(hN0 : N % 32 = 0)"])
    b = B(2504, st, FW(96), nat=natR, renat={2541: FW(96)}, inb=(2538,)).go(
        stop=(2559,), branches={2518: (False, "hc")})
    st2 = blk(o, "lg2m", b, H + HM)["stack"]
    st = info["lg2n"]["stack"]
    assert st == st2, (st, st2)
    loop(o, info, 1, 96, 96, 128)
    unify(o, info, "lg2", "lg2n", "lg2m")
    o.write(out + "/BlocksC.lean")

    # ---- D: the test of the code and the start of the call data ---------------------------
    o = Out("transferAndCall: the test of the code and the head of the call data",
            "LinkVerify.Link.Tac.Args")
    b = B(2559, st, FW(96)).go(stop=(2840,))
    blk(o, "ic_pre", b, [])
    b = B(2559, st, FW(96)).go(branches={2572: (True, "hc")})
    blk(o, "ic_none", b, H, b.ret())
    b = B(2559, st, FW(96)).go(stop=(2851,), branches={2572: (False, "hc")})
    st = blk(o, "ic_some", b, H)["stack"]
    b = B(2851, st, FW(96), newsz={2956: L("S1"), 2962: L("S2")}).go(stop=(2980,))
    st = blk(o, "fb1", b, H + ["(hS1 : S1 = max (F + W + 96) (F + 128))",
                               "(hS2 : S2 = max S1 (F + 160))"])["stack"]
    b = B(2980, ["i"] + st[1:], L("S"), words={}, nat=natK, newsz={2996: L("S'")})
    b.step()
    b.go(stop=(2980,), branches={2988: (False, "hc")})
    blk(o, "lb2", b, CTXN + LOOP + ["(hS' : S' = max S (F + K + 192))"])
    b = B(2980, ["i"] + st[1:], L("S"), words={}, nat=natK)
    b.step()
    b.go(stop=(3010,), branches={2988: (True, "hc")})
    st = blk(o, "lx2", b, [])["stack"]
    loop(o, info, 2, 160, 132, 192)
    o.write(out + "/BlocksD.lean")

    # ---- E: the end of the call data and the end after the call ---------------------------
    o = Out("transferAndCall: the end of the call data and the end after the call",
            "LinkVerify.Link.Tac.Args")
    H = CTXN + MH("F + W + 160")
    b = B(3010, st, FW(160), renat={3014: FW(132)}, canon=(3014, 3065)).go(
        stop=(3086,), branches={3024: (True, "hc"), 3077: (True, "hc2")})
    blk(o, "fb2n", b, H + ["(hN0 : N % 32 = 0)"])
    b = B(3010, st, FW(160), nat=natR, renat={3047: FW(132)}, inb=(3044,), canon=(3047, 3065)).go(
        stop=(3086,), branches={3024: (False, "hc"), 3077: (True, "hc2")})
    st2 = blk(o, "fb2m", b, H + HM)["stack"]
    st = info["fb2n"]["stack"]
    assert st == st2, (st, st2)
    unify(o, info, "fb2", "fb2n", "fb2m")
    HA = CTXF + ["(hsz : mem.size = S)", "(hSm : S % 32 = 0)", "(hSF : F + 32 ≤ S)",
                 "(h64 : loadWord (memoryReadBytes mem 64 32) 0 32 = fpw)"]
    sa = ["flag"] + st[7:]
    b = B(3089, sa, L("S"), words={Lin(k=64): ("fpw", "h64")}, inb=(369,)).go(
        branches={3094: (True, "hc")})
    blk(o, "af_ok", b, HA, b.ret())
    b = B(3089, sa, L("S"), words={Lin(k=64): ("fpw", "h64")}).go(
        stop=(3098,), branches={3094: (False, "hc")})
    blk(o, "af_fail", b, [], REVERT)
    o.write(out + "/BlocksE.lean")

    # ---- the paths ------------------------------------------------------------------------
    o = Out("transferAndCall: the paths from the entry of the function",
            "LinkVerify.Link.Tac.BlocksA\nimport LinkVerify.Link.Tac.BlocksB\nimport LinkVerify.Link.Tac.BlocksC\nimport LinkVerify.Link.Tac.BlocksD\nimport LinkVerify.Link.Tac.BlocksE")
    PRE = [("dec", {}), ("vr_ok", {})]
    XF = [("xf1", {}), ("xf2", {}), ("xf3", {})]
    LG = [("lg1", {}), ("cp1", {"S": "(F + 96)"}), ("lg2", {})]
    S1T = "(max (F + W + 96) (F + 128))"
    S2T = "(max %s (F + 160))" % S1T
    FB = [("ic_some", {}), ("fb1", {"S1": S1T, "S2": S2T}), ("cp2", {"S": S2T}), ("fb2", {})]
    path(o, info, "tac_zero", "The recipient is the zero address: the call reverts.",
         [("dec", {}), ("vr_zero", {})])
    path(o, info, "tac_self", "The recipient is the token itself: the call reverts.",
         [("dec", {}), ("vr_self", {})])
    path(o, info, "tac_low", "The amount is above the balance of the caller: the invalid opcode.",
         PRE + [("xf_low", {})])
    path(o, info, "tac_stuck", "A static call, or a frame with no account: the first SSTORE fails.",
         PRE + [("xf1", {}), ("xf2_stuck", {})])
    path(o, info, "tac_over", "The balance of the recipient would wrap: the invalid opcode.",
         PRE + [("xf1", {}), ("xf_over", {})])
    path(o, info, "tac_ext", "The transfer and both logs: the frame at the EXTCODESIZE of the recipient.",
         PRE + XF + LG + [("ic_pre", {})], size="F + W + 96")
    path(o, info, "tac_none", "The recipient has no code: both logs, then the return of true.",
         PRE + XF + LG + [("ic_none", {})])
    path(o, info, "tac_call", "The recipient has code: the frame just before the GAS of the call.",
         PRE + XF + LG + FB, over={("fb2", "hc2"): "(code_twice hc_ic_some)"}, size="F + W + 160")
    o.write(out + "/Paths.lean")
    import json
    json.dump(info, open(os.path.join(os.path.dirname(os.path.abspath(sys.argv[1])), "tac_info.json"), "w"), indent=1)


main()

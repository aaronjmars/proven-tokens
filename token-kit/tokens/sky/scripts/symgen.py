#!/usr/bin/env python3
"""Generator of SkyVerify/Sky/BytesGen.lean: straight-line segments of the SKY runtime code whose
memory offsets are not numerals but sums of numerals and named natural numbers (the rounded
length of the signature, the free memory pointer).

The generators of the kit cut paths with fixed memory shapes. The route of
`permit(owner, spender, value, deadline, bytes)` for a signature whose length is not 65 has
offsets that depend on the length, so its segments are generated here: the script runs the
opcodes of a segment over a symbolic stack and memory and prints one `step` per opcode, with the
side conditions on offsets left to `omega`.

Usage: python3 scripts/symgen.py          (writes SkyVerify/Sky/BytesGen.lean)
       python3 scripts/symgen.py --check  (fails when the file on disk differs)
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "SkyVerify", "Sky", "BytesGen.lean")
M256 = 1 << 256


def load_code():
    h = open(os.path.join(ROOT, "data", "sky.runtime.hex")).read().strip()
    if h.startswith("0x"):
        h = h[2:]
    return bytes.fromhex(h)


CODE = load_code()

# ---------------------------------------------------------------- values


class Aff:
    """const + sum of coeff * atom, a natural number."""

    def __init__(self, const=0, co=None):
        self.c = const
        self.co = {k: v for k, v in (co or {}).items() if v != 0}

    def __add__(self, o):
        co = dict(self.co)
        for k, v in o.co.items():
            co[k] = co.get(k, 0) + v
        return Aff(self.c + o.c, co)

    def __sub__(self, o):
        co = dict(self.co)
        for k, v in o.co.items():
            co[k] = co.get(k, 0) - v
        return Aff(self.c - o.c, co)

    def plus(self, n):
        return Aff(self.c + n, self.co)

    def is_const(self):
        return not self.co

    def s(self):
        parts = []
        for k in sorted(self.co):
            v = self.co[k]
            if v < 0:
                raise ValueError("negative coefficient in " + repr((self.c, self.co)))
            parts.append(k if v == 1 else "%d * %s" % (v, k))
        if self.c < 0:
            raise ValueError("negative constant in " + repr((self.c, self.co)))
        if self.c or not parts:
            parts.append(str(self.c))
        return " + ".join(parts)

    def key(self):
        return self.s()


def lit(n):
    return ("lit", n % M256)


def aff(a):
    if a.is_const() and a.c >= 0:
        return ("lit", a.c)
    return ("aff", a)


def op(s):
    return ("op", s)


def to_aff(v):
    if v[0] == "lit":
        return Aff(v[1])
    if v[0] == "aff":
        return v[1]
    return None


def lean(v):
    if v[0] == "lit":
        return "(%d : U256)" % v[1]
    if v[0] == "aff":
        return "(W (%s))" % v[1].s()
    return v[1]


def natstr(v):
    return to_aff(v).s()


NOT31 = M256 - 32

# ---------------------------------------------------------------- the segment runner

BASE = {"JUMPDEST": 1, "POP": 2, "JUMP": 8, "JUMPI": 10}


class Seg:
    def __init__(self, spec):
        self.spec = spec
        self.name = spec["name"]
        self.atoms = spec.get("atoms", {})  # name -> (residue mod 32, lower bound)
        self.stack = list(spec["stack"])
        self.pc = spec["pc"]
        self.size = spec["size"]  # Aff
        self.size0 = self.size
        self.szp = "hms"
        self.memterm = "mem"
        self.words = {}  # key -> (Aff, value, proof)
        self.tops = {}  # key -> (Aff, n, value, proof)
        for (a, v, h) in spec.get("words", []):
            self.words[a.key()] = (a, v, h)
        for (a, n, v, h) in spec.get("tops", []):
            self.tops[a.key()] = (a, n, v, h)
        self.lines = []
        self.K = 0
        self.grow = []  # (old size Aff, new size Aff)
        self.hyps = []  # (name, statement) of the branch conditions
        self.branches = list(spec.get("branches", []))
        self.writes = []  # (size proof before, offset Aff)
        self.state = "state"
        self.sub = "substate"
        self.extra = []  # terms of the cost that are not numerals (the price of a write)
        self.sstore = False
        self.static = False
        self.run()

    # lower bound of an Aff, or None
    def lb(self, a):
        t = a.c
        for k, v in a.co.items():
            if v < 0:
                return None
            t += v * self.atoms[k][1]
        return t

    def emit(self, s):
        self.lines.append("  " + s)

    def nat_proof(self, v):
        if v[0] == "lit":
            return "(by decide +kernel)"
        return "(W_toNat (by omega))"

    def push(self, v):
        self.stack.insert(0, v)

    def pop(self):
        return self.stack.pop(0)

    def fold_lit(self, n):
        self.emit("step foldK (y := (%d : U256)) (by decide +kernel)" % n)
        self.stack[0] = lit(n)

    def run(self):
        stop = self.spec["stop"]
        guard = 0
        while self.pc != stop:
            guard += 1
            if guard > 2000:
                raise RuntimeError("no stop in " + self.name)
            self.step()

    def step(self):
        pc = self.pc
        b = CODE[pc]
        st = self.stack
        if b == 0x5B:
            self.emit("step jumpdestR")
            self.K += 1
            self.pc += 1
        elif 0x60 <= b <= 0x7F:
            n = b - 0x5F
            v = int.from_bytes(CODE[pc + 1:pc + 1 + n], "big")
            self.emit("step pushR %d (%d : U256)" % (n, v))
            self.emit("at_pc %d" % (pc + 1 + n))
            self.push(lit(v))
            self.K += 3
            self.pc += 1 + n
        elif 0x80 <= b <= 0x8F:
            k = b - 0x80
            self.emit("step dupR %d" % k)
            self.push(st[k])
            self.K += 3
            self.pc += 1
        elif 0x90 <= b <= 0x9F:
            k = b - 0x8F
            self.emit("step swap%dK (by code_fact) (by code_fact) (by gas_ok)" % k)
            st[0], st[k] = st[k], st[0]
            self.K += 3
            self.pc += 1
        elif b == 0x50:
            self.emit("step popR")
            self.pop()
            self.K += 2
            self.pc += 1
        elif b == 0x01:
            self.emit("step binR 0x01 instruction_add")
            x, y = self.pop(), self.pop()
            self.K += 3
            self.pc += 1
            if x[0] == "lit" and y[0] == "lit":
                self.push(lit(x[1] + y[1]))
                self.fold_lit((x[1] + y[1]) % M256)
            elif y == ("lit", NOT31) and x[0] == "aff":
                r = aff(x[1].plus(-32))
                self.push(r)
                self.emit("step foldK (y := %s) ((W_add_not31 (a := %s) (by omega) (by omega)).trans (congrArg W (show %s - 32 = %s by omega)))"
                          % (lean(r), natstr(x), natstr(x), natstr(r)))
            elif to_aff(x) is not None and to_aff(y) is not None:
                r = aff(to_aff(x) + to_aff(y))
                self.push(r)
                self.emit("step foldK (y := %s) ((W_add (%s) (%s)).trans (congrArg W (show %s + (%s) = %s by omega)))"
                          % (lean(r), natstr(x), natstr(y), natstr(x), natstr(y), natstr(r)))
            else:
                self.push(op("(add %s %s)" % (lean(x), lean(y))))
        elif b == 0x03:
            self.emit("step binR 0x03 instruction_sub")
            x, y = self.pop(), self.pop()
            self.K += 3
            self.pc += 1
            ax, ay = to_aff(x), to_aff(y)
            if x[0] == "lit" and y[0] == "lit":
                self.push(lit(x[1] - y[1]))
                self.fold_lit((x[1] - y[1]) % M256)
            elif ax is not None and ay is not None and self.lb(ax - ay) is not None and self.lb(ax - ay) >= 0:
                r = aff(ax - ay)
                self.push(r)
                self.emit("step foldK (y := %s) ((W_sub (a := %s) (b := %s) (by omega) (by omega)).trans (congrArg W (show %s - (%s) = %s by omega)))"
                          % (lean(r), natstr(x), natstr(y), natstr(x), natstr(y), natstr(r)))
            else:
                self.push(op("(sub %s %s)" % (lean(x), lean(y))))
        elif b in (0x16, 0x17, 0x14, 0x10, 0x11, 0x12):
            nm = {0x16: "bitwiseAnd", 0x17: "bitwiseOr", 0x14: "equal", 0x10: "lessThan",
                  0x11: "greaterThan", 0x12: "signedLessThan"}[b]
            ins = "instruction_eq" if b == 0x14 else "(instruction_of_stackOnlyStep rfl)"
            if b == 0x12:
                self.emit("step bin3L (by code_fact) (by code_fact) (byte := 0x12) rfl (Nat.le_trans (by decide) hfork) (instruction_of_stackOnlyStep rfl) rfl (by gas_ok)")
            else:
                self.emit("step binR 0x%02x %s" % (b, ins))
            x, y = self.pop(), self.pop()
            self.K += 3
            self.pc += 1
            small = x[0] == "lit" and y[0] == "lit" and x[1] < (1 << 255) and y[1] < (1 << 255)
            ceil = self.spec.get("ceil")
            if x[0] == "lit" and y[0] == "lit" and (b in (0x16, 0x17, 0x14, 0x10, 0x11) or small):
                r = {0x16: x[1] & y[1], 0x17: x[1] | y[1], 0x14: int(x[1] == y[1]),
                     0x10: int(x[1] < y[1]), 0x11: int(x[1] > y[1]), 0x12: int(x[1] < y[1])}[b]
                self.push(lit(r))
                self.fold_lit(r)
            elif b == 0x16 and x == ("lit", NOT31) and y[0] == "aff" and ceil and y[1].key() == ceil[0]:
                r = aff(Aff(0, {ceil[1]: 1}))
                self.push(r)
                self.emit("step foldK (y := %s) ((W_floor' (n := %s) (by omega)).trans (congrArg W (show (%s) / 32 * 32 = %s by omega)))"
                          % (lean(r), natstr(y), natstr(y), natstr(r)))
            else:
                self.push(op("(%s %s %s)" % (nm, lean(x), lean(y))))
        elif b == 0x1B:
            self.emit("step bin3L (by code_fact) (by code_fact) (byte := 0x1b) rfl (Nat.le_trans (by decide) hfork) (instruction_of_stackOnlyStep rfl) rfl (by gas_ok)")
            x, y = self.pop(), self.pop()
            self.K += 3
            self.pc += 1
            if x[0] == "lit" and y[0] == "lit":
                r = (y[1] << x[1]) % M256 if x[1] < 256 else 0
                self.push(lit(r))
                self.fold_lit(r)
            else:
                self.push(op("(bitwiseShl %s %s)" % (lean(x), lean(y))))
        elif b in (0x15, 0x19):
            x = self.pop()
            self.K += 3
            self.pc += 1
            if b == 0x15:
                self.emit("step unR 0x15 instruction_iszero")
                if x[0] == "lit":
                    self.push(lit(int(x[1] == 0)))
                    self.fold_lit(int(x[1] == 0))
                else:
                    self.push(op("(isZero %s)" % lean(x)))
            else:
                self.emit("step unR 0x19 (instruction_of_stackOnlyStep rfl)")
                if x[0] == "lit":
                    self.push(lit(M256 - 1 - x[1]))
                    self.fold_lit(M256 - 1 - x[1])
                else:
                    self.push(op("(bitwiseNot %s)" % lean(x)))
        elif b == 0x30:
            self.emit("step addressL (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)")
            self.push(op("message.currentTarget.toU256"))
            self.K += 2
            self.pc += 1
        elif b == 0x51:
            a = self.pop()
            aa = to_aff(a)
            if aa is None:
                raise RuntimeError("%s: MLOAD at pc %d of an unknown word %s" % (self.name, pc, lean(a)))
            if aa.key() not in self.words:
                self.words[aa.key()] = (aa, op("(loadWord (memoryReadBytes %s (%s) 32) 0 32)" % (self.memterm, aa.s())), "rfl")
            _, v, pr = self.words[aa.key()]
            self.emit("step mloadK (sz := %s) (o := %s) (by code_fact) (by code_fact) %s %s (by omega) %s (by gas_ok)"
                      % (self.size.s(), aa.s(), self.szp, self.nat_proof(a), pr))
            self.push(v)
            self.K += 3
            self.pc += 1
        elif b == 0x52:
            a, v = self.pop(), self.pop()
            aa = to_aff(a)
            if aa is None:
                raise RuntimeError("%s: MSTORE at pc %d at an unknown offset" % (self.name, pc))
            self.mstore(aa, a, v)
            self.K += 3
            self.pc += 1
        elif b == 0x20:
            a, k = self.pop(), self.pop()
            self.keccak(a, k)
            self.pc += 1
        elif b == 0x55:
            if self.spec.get("stuck"):
                self.emit("exact stuckL (Gas.sstoreStuckW (by code_fact) (by code_fact) hbad)")
                self.pc = self.spec["stop"]
                return
            k, v = self.pop(), self.pop()
            self.emit("step sstoreK hfork (by code_fact) (by code_fact) hstatic hacc (by gas_ok) (by gas_ok)")
            t = "message.currentTarget"
            st, ss = self.state, self.sub
            self.extra.append("(Gas.writeCost fork (originalAt %s %s %s) (storageAt %s %s %s) %s (coldIn %s %s %s))"
                              % (st, t, lean(k), st, t, lean(k), lean(v), ss, t, lean(k)))
            self.sub = "(storeSub fork %s %s %s (originalAt %s %s %s) (storageAt %s %s %s) %s)" % (
                ss, t, lean(k), st, t, lean(k), st, t, lean(k), lean(v))
            self.state = "(writeSlot %s %s %s %s)" % (st, t, lean(k), lean(v))
            self.sstore = True
            self.static = True
            self.pc += 1
        elif b == 0xA3:
            a, k = self.pop(), self.pop()
            t1, t2, t3 = self.pop(), self.pop(), self.pop()
            aa = to_aff(a)
            assert k == ("lit", 32) and aa.key() in self.words
            _, v, pr = self.words[aa.key()]
            self.emit("step log3K (sz := %s) (o := %s) (k := 32) (c := 1756) (by code_fact) (by code_fact) hstatic %s %s (by decide +kernel) (by omega) (by decide +kernel) (readWord_raw %s %s (by omega)) (by gas_ok)"
                      % (self.size.s(), aa.s(), self.szp, self.nat_proof(a), pr, self.szp))
            self.sub = "(logSub %s message.currentTarget %s %s %s (wordBytes %s))" % (
                self.sub, lean(t1), lean(t2), lean(t3), lean(v))
            self.K += 1756
            self.static = True
            self.pc += 1
        elif b == 0x56:
            d = self.pop()
            assert d[0] == "lit", "%s: JUMP at pc %d to a word that is not a numeral" % (self.name, pc)
            self.emit("step jumpR")
            self.emit("at_pc %d" % d[1])
            self.K += 8
            self.pc = d[1]
        elif b == 0x57:
            d, c = self.pop(), self.pop()
            assert d[0] == "lit"
            self.K += 10
            if c[0] == "lit":
                taken = c[1] != 0
                pr = "(by decide +kernel)"
            else:
                taken, hn = self.branches.pop(0)
                self.hyps.append((hn, "%s %s 0" % (lean(c), "≠" if taken else "=")))
                pr = hn
            if taken:
                self.emit("step jumpiR %s" % pr)
                self.emit("at_pc %d" % d[1])
                self.pc = d[1]
            else:
                self.emit("step jumpi0R %s" % pr)
                self.emit("at_pc %d" % (pc + 1))
                self.pc = pc + 1
        else:
            raise RuntimeError("%s: opcode 0x%02x at pc %d is not handled" % (self.name, b, pc))

    def mstore(self, aa, a, v):
        end = aa.plus(32)
        inside = self.lb(self.size - end)
        if self.spec.get("nogrow") or (inside is not None and inside >= 0):
            new = self.size
            n = "0"
            ext = "(ext0 (o := %s) %s (by omega))" % (aa.s(), self.nat_proof(a))
        else:
            r = end.c
            for k, c in end.co.items():
                r += c * self.atoms[k][0]
            new = end.plus((-r) % 32)
            d = new - self.size
            n = str(d.c) if d.is_const() else "(%s - (%s))" % (new.s(), self.size.s())
            ext = "(extN (s' := %s) (o := %s) %s (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))" % (
                new.s(), aa.s(), self.nat_proof(a))
            self.grow.append((self.size, new))
        self.emit("step mstoreK (sz := %s) (n := %s) (o := %s) (by code_fact) (by code_fact) %s %s %s rfl (by gas_ok)"
                  % (self.size.s(), n, aa.s(), self.szp, ext, self.nat_proof(a)))
        old = self.szp
        self.writes.append((old, aa))
        # the facts that the write keeps
        words, tops = {}, {}
        for key, (wa, wv, wp) in self.words.items():
            d1, d2 = self.lb(aa - wa.plus(32)), self.lb(wa - end)
            if (d1 is not None and d1 >= 0) or (d2 is not None and d2 >= 0):
                words[key] = (wa, wv, "(load_rawW %s %s (by omega) (by omega) (by omega))" % (wp, old))
            else:
                d = aa - wa
                if d.is_const() and 0 < d.c < 32:
                    tops[key] = (wa, d.c, wv,
                                 "(top_of_word %s %s (by omega) (by omega) (by omega) (by omega))" % (wp, old))
        for key, (ta, tn, tv, tp) in self.tops.items():
            d1, d2 = self.lb(aa - ta.plus(tn)), self.lb(ta - end)
            if (d1 is not None and d1 >= 0) or (d2 is not None and d2 >= 0):
                tops[key] = (ta, tn, tv, "(top_rawW %s %s (by omega) (by omega) (by omega))" % (tp, old))
        words[aa.key()] = (aa, v, "(load_rawW_self %s (by omega))" % old)
        tops.pop(aa.key(), None)
        self.words, self.tops = words, tops
        self.memterm = "(memoryWrite (memoryExtend %s %s) (%s) (wordBytes %s))" % (self.memterm, n, aa.s(), lean(v))
        self.szp = "(sizeW (%s) %s (by omega) (by omega))" % (new.s(), old)
        self.size = new

    def words_from(self, a, n):
        """Proof that the `n` words from `a` are the list of their known values."""
        vals = []
        for i in range(n):
            key = a.plus(32 * i).key()
            if key not in self.words:
                raise RuntimeError("%s: no known word at %s for a hash" % (self.name, key))
            vals.append(self.words[key])
        pr = "(readWords_one %s %s (by omega))" % (vals[-1][2], self.szp)
        for i in range(n - 2, -1, -1):
            pr = "(readWords_consA (a := %s) (a' := %s) (k := %d) %s %s (by omega) %s (by omega) (by decide))" % (
                a.plus(32 * i).s(), a.plus(32 * i + 32).s(), 32 * (n - 1 - i), vals[i][2], pr, self.szp)
        return [v[1] for v in vals], pr

    def keccak(self, a, k):
        assert k[0] == "lit"
        aa = to_aff(a)
        kk = k[1]
        cost = 30 + 6 * ((kk + 31) // 32)
        self.K += cost
        if a == ("lit", 0) and kk == 64:
            w0, w1 = self.words["0"], self.words["32"]
            self.emit("step keccakMapK (sz := %s) (by code_fact) (by code_fact) %s (by omega) (read0_raw %s %s %s (by omega)) (by gas_ok)"
                      % (self.size.s(), self.szp, w0[2], w1[2], self.szp))
            self.push(op("(mapSlot %s %s)" % (lean(w0[1]), lean(w1[1]))))
            return
        if aa.key() in self.tops:
            ta, tn, tv, tp = self.tops[aa.key()]
            n = (kk - tn) // 32
            assert tn + 32 * n == kk
            vals, pr = self.words_from(aa.plus(tn), n)
            data = "(readTopA (a := %s) (a' := %s) (n := %d) (k := %d) %s %s (by omega) %s (by omega) (by decide) (by decide) (by decide))" % (
                aa.s(), aa.plus(tn).s(), tn, 32 * n, tp, pr, self.szp)
            res = "(keccak (topBytes %d %s (memW [%s])))" % (tn, lean(tv), ", ".join(lean(v) for v in vals))
        else:
            n = kk // 32
            assert 32 * n == kk
            vals, data = self.words_from(aa, n)
            res = "(keccak (memW [%s]))" % ", ".join(lean(v) for v in vals)
        self.emit("step keccakK (sz := %s) (o := %s) (k := %d) (c := %d) (by code_fact) (by code_fact) %s %s (by decide +kernel) (by omega) (by decide +kernel) %s (by gas_ok)"
                  % (self.size.s(), aa.s(), kk, cost, self.szp, self.nat_proof(a), data))
        self.push(op(res))

    # ------------------------------------------------------------ printing

    def cost(self):
        c = str(self.K)
        for e in self.extra:
            c += " + " + e
        if self.size.key() != self.size0.key():
            c += " + (memoryGasCost (%s) - memoryGasCost (%s))" % (self.size.s(), self.size0.s())
        return c

    def binders(self):
        sp = self.spec
        out = []
        if sp.get("vars"):
            out.append("{%s : U256}" % " ".join(sp["vars"]))
        out.append("{rest : List U256} {mem : ByteArray}")
        if self.atoms:
            out.append("{%s : Nat}" % " ".join(self.atoms))
        return " ".join(out)

    def mem_hyps(self):
        sp = self.spec
        hs = ["(hfork : .berlin ≤ fork)"]
        for (n, t) in sp.get("hyps", []):
            hs.append("(%s : %s)" % (n, t))
        if self.static:
            hs.append("(hstatic : message.isStatic = false)")
        if self.sstore:
            hs.append("(hacc : hasAccount state message.currentTarget)")
        hs.append("(hms : mem.size = %s)" % self.size0.s())
        for (a, v, h) in sp.get("words", []):
            hs.append("(%s : loadWord (memoryReadBytes mem (%s) 32) 0 32 = %s)" % (h, a.s(), lean(v)))
        for (a, n, v, h) in sp.get("tops", []):
            hs.append("(%s : TopBytes mem (%s) %d %s)" % (h, a.s(), n, lean(v)))
        return hs

    def stack_str(self, st):
        return "(" + " :: ".join([lean(v) for v in st] + ["rest"]) + ")"

    def text(self):
        sp = self.spec
        usesmsg = "message" in self.memterm
        margs = " ".join((["message"] if usesmsg else []) + ["mem"] + list(self.atoms) + sp.get("vars", []))
        mb = ("{fork : Fork} (message : Message fork) " if usesmsg else "") + "(mem : ByteArray)"
        if self.atoms:
            mb += " (%s : Nat)" % " ".join(self.atoms)
        if sp.get("vars"):
            mb += " (%s : U256)" % " ".join(sp["vars"])
        if sp.get("stuck"):
            o = ["/-- %s -/" % sp["doc"]]
            o.append("theorem %s %s {gas : Nat} {state : State.TransactionState} {substate : Substate}" % (
                self.name, self.binders()))
            for h in self.mem_hyps():
                o.append("    " + h)
            for (n, t) in self.hyps:
                o.append("    (%s : %s)" % (n, t))
            o.append("    (hbad : message.isStatic = true ∨ ¬hasAccount state message.currentTarget)")
            o.append("    (hrest : rest.length ≤ 900)")
            o.append("    (hg : %s ≤ gas) :" % self.cost())
            o.append("    Logic.HoareG fork (At CODE message %d %s mem gas state substate) Logic.Stuck := by" % (
                sp["pc"], self.stack_str(sp["stack"])))
            for i, (a, b2) in enumerate(self.grow):
                o.append("  have hm%d := memoryGasCost_mono (show %s ≤ %s by omega)" % (i, a.s(), b2.s()))
            o.extend(self.lines)
            o.append("")
            return "\n".join(o)
        o = []
        o.append("/-- The memory after the segment `%s`. -/" % self.name)
        o.append("abbrev %s_M %s : ByteArray :=\n  %s\n" % (self.name, mb, self.memterm))
        o.append("/-- %s -/" % sp["doc"])
        o.append("theorem %s %s {gas : Nat} {state : State.TransactionState} {substate : Substate}" % (
            self.name, self.binders()))
        for h in self.mem_hyps():
            o.append("    " + h)
        for (n, t) in self.hyps:
            o.append("    (%s : %s)" % (n, t))
        o.append("    (hrest : rest.length ≤ 900)")
        if self.sstore:
            o.append("    (hg : %s + 2300 < gas) :" % self.cost())
        else:
            o.append("    (hg : %s ≤ gas) :" % self.cost())
        o.append("    Logic.HoareG fork (At CODE message %d %s mem gas state substate)" % (
            sp["pc"], self.stack_str(sp["stack"])))
        o.append("      (At CODE message %d %s (%s_M %s) (gas - (%s)) %s %s) := by" % (
            self.pc, self.stack_str(self.stack), self.name, margs, self.cost(), self.state, self.sub))
        for i, (a, b2) in enumerate(self.grow):
            o.append("  have hm%d := memoryGasCost_mono (show %s ≤ %s by omega)" % (i, a.s(), b2.s()))
        o.extend(self.lines)
        o.append("  exact hoareL (restate (by decide) rfl rfl (by gas_ok) rfl rfl)")
        o.append("")
        # the facts on the memory after
        concl = ["(%s_M %s).size = %s" % (self.name, margs, self.size.s())]
        proofs = [self.szp]
        for key in self.words:
            wa, wv, wp = self.words[key]
            concl.append("loadWord (memoryReadBytes (%s_M %s) (%s) 32) 0 32 = %s" % (self.name, margs, wa.s(), lean(wv)))
            proofs.append(wp)
        for key in self.tops:
            ta, tn, tv, tp = self.tops[key]
            concl.append("TopBytes (%s_M %s) (%s) %d %s" % (self.name, margs, ta.s(), tn, lean(tv)))
            proofs.append(tp)
        lo, hi = sp["frame"]
        concl.append("(∀ i, %s ≤ i → i < %s → byteAt (%s_M %s) i = byteAt mem i)" % (lo, hi, self.name, margs))
        rws = ["byteAt_rawW_miss %s (by omega) (by omega)" % szp for (szp, _) in reversed(self.writes)]
        if rws:
            proofs.append("(fun i h1 h2 => by\n      rw [%s])" % ",\n        ".join(rws))
        else:
            proofs.append("(fun i h1 h2 => rfl)")
        o.append("/-- The memory after the segment `%s`: its size, its known words, and its bytes from %s"
                 " up to %s, which are the bytes of the memory before. -/" % (self.name, lo, hi))
        o.append("theorem %s_mem %s" % (self.name, self.binders()))
        for h in self.mem_hyps()[1:]:
            if not h.startswith("(hstatic") and not h.startswith("(hacc"):
                o.append("    " + h)
        o.append("    :")
        o.append("    " + " ∧\n    ".join(concl) + " :=")
        o.append("  ⟨" + ",\n    ".join(proofs) + "⟩")
        o.append("")
        self.K_total = self.K
        return "\n".join(o)


# ---------------------------------------------------------------- tails that revert


def lazy_tail(name, doc, pc, stack):
    """A straight path from `pc` to a REVERT, in the style of `permit_fail_tail`: one `ls` per
    opcode, for any memory. `stack` lists the top of the stack: a numeral or None (any word)."""
    st = list(stack)
    names = []
    shape = []
    for i, v in enumerate(st):
        if v is None:
            names.append("a%d" % i)
            shape.append("a%d" % i)
        else:
            shape.append("(%d : U256)" % v)
    lines = []
    guard = 0
    while True:
        guard += 1
        assert guard < 500
        b = CODE[pc]
        if b == 0x5B:
            pc += 1
            lines.append("ls %d ljumpdest" % pc)
        elif 0x60 <= b <= 0x7F:
            n = b - 0x5F
            v = int.from_bytes(CODE[pc + 1:pc + 1 + n], "big")
            pc += 1 + n
            if n == 2:
                lines.append("ls %d (lpush 2 %d)" % (pc, v))
            else:
                lines.append("ls %d (lpushAny %d)" % (pc, n))
            st.insert(0, v)
        elif 0x80 <= b <= 0x8F:
            k = b - 0x80
            pc += 1
            lines.append("ls %d (ldup %d)" % (pc, k))
            st.insert(0, st[k])
        elif 0x90 <= b <= 0x9F:
            k = b - 0x8F
            pc += 1
            lines.append("ls %d (lswap %d)" % (pc, k - 1))
            st[0], st[k] = st[k], st[0]
        elif b == 0x50:
            pc += 1
            lines.append("ls %d lpop" % pc)
            st.pop(0)
        elif b in (0x01, 0x03):
            pc += 1
            lines.append("ls %d (lbin 0x%02x %s)" % (pc, b, "instruction_add" if b == 1 else "instruction_sub"))
            st.pop(0)
            st[0] = None
        elif b == 0x1B:
            pc += 1
            lines.append("ls %d lshl" % pc)
            st.pop(0)
            st[0] = None
        elif b == 0x51:
            pc += 1
            lines.append("ls %d lmload" % pc)
            st[0] = None
        elif b == 0x52:
            pc += 1
            lines.append("ls %d lmstore" % pc)
            st.pop(0)
            st.pop(0)
        elif b == 0x56:
            d = st.pop(0)
            assert d is not None
            pc = d
            lines.append("ls %d ljump" % pc)
        elif b == 0x57:
            d, c = st.pop(0), st.pop(0)
            assert d is not None and c is not None
            if c:
                pc = d
                lines.append("ls %d (ljumpi (by decide))" % pc)
            else:
                pc += 1
                lines.append("ls %d (ljumpi0 rfl)" % pc)
        elif b == 0xFD:
            lines.append("exact h.reverts (fun G hG => Logic.revertG (Nat.le_trans (by decide) hfork) (by code_fact)")
            lines.append("  (by code_fact) hG) hok")
            break
        else:
            raise RuntimeError("%s: opcode 0x%02x at pc %d is not handled" % (name, b, pc))
    o = ["/-- %s -/" % doc]
    o.append("theorem %s (hfork : .berlin ≤ fork) {bound : Nat}" % name)
    o.append("    {runChild : MessageRunner fork Nat bound} {s : Evm fork Nat} {B : Nat}")
    if names:
        o.append("    {%s : U256}" % " ".join(names))
    o.append("    {R : List U256} {m rd : ByteArray} {st : State.TransactionState} {ss : Substate}")
    o.append("    (hR : R.length ≤ 100)")
    o.append("    (h : RunsTo runChild s CODE message B %d (%s) m st ss rd)" % (
        pc if False else stack_pc[0], " :: ".join(shape + ["R"])))
    o.append("    (hok : s.error = none) : False := by")
    o.extend("  " + l for l in lines)
    o.append("")
    return "\n".join(o)


stack_pc = [0]


def tail(name, doc, pc, stack):
    stack_pc[0] = pc
    return lazy_tail(name, doc, pc, stack)


# ---------------------------------------------------------------- segments copied from the kit


def derived(src_file, src_name, new_name, doc):
    """A block of the generated files with the size of the memory fixed (`msz = 288`), restated
    for any memory of 64 bytes or more: the block only uses the first two words."""
    t = open(os.path.join(ROOT, "SkyVerify", "Sky", "Gen", src_file)).read()
    m = re.search(r"^theorem %s .*?(?=^theorem |^end )" % re.escape(src_name), t, re.S | re.M)
    if not m:
        raise RuntimeError("block %s not found" % src_name)
    b = m.group(0).rstrip() + "\n"
    b = b.replace("theorem %s " % src_name, "theorem %s " % new_name, 1)
    assert "(hmsz : msz = 288)" in b
    b = b.replace("(hmsz : msz = 288)", "(hmsz : 64 ≤ msz)")
    b = b.replace("  subst hmsz\n", "")
    b = b.replace("(c := 0) (n := 0) (by decide +kernel) (o := 0) (by decide +kernel)",
                  "(c := 0) (n := 0) (ext0 (o := 0) (by decide +kernel) (by omega)) (o := 0) (by decide +kernel)")
    b = b.replace("(c := 0) (n := 0) (by decide +kernel) (o := 32) (by decide +kernel)",
                  "(c := 0) (n := 0) (ext0 (o := 32) (by decide +kernel) (by omega)) (o := 32) (by decide +kernel)")
    b = "\n".join(l.replace("(by decide)", "(by omega)")
                  if l.startswith("  step mstoreK") or l.startswith("  step keccakMapK") else l
                  for l in b.split("\n"))
    b = re.sub(r"\n    \(hfp : [^\n]*\n", "\n", b)
    b = re.sub(r"\n    \(ht224 : [^\n]*\n", "\n", b)
    b = b.replace(" mt224 :", " :")
    return "/-- %s -/\n%s" % (doc, b)


# ---------------------------------------------------------------- the specifications

MASK = 1461501637330902918203684832716283019655932542975
P = Aff(0, {"P": 1})
HYP_P = [("hP", "P % 32 = 0"), ("hP0", "160 ≤ P"), ("hPb", "P < 2 ^ 100")]


def v(name):
    return op(name)


SEGS = [
    dict(
        name="sb3191", pc=3191, stop=2512,
        doc="The code that builds the domain separator (pc 3191 to its return to pc 2512), for a "
            "free memory pointer `P` and a memory of `P + 32` bytes.",
        atoms={"P": (0, 160)}, hyps=HYP_P, vars=["x0"],
        stack=[v("x0"), lit(2512)],
        size=P.plus(32), words=[(Aff(64), aff(P), "hfp")], frame=("96", "P"),
    ),
    dict(
        name="sb2551", pc=2551, stop=2704,
        doc="The struct hash of `permit` and the start of the digest (pc 2551 to 2704), for a free "
            "memory pointer `P` and a memory of `sz` bytes, `P ≤ sz ≤ P + 32`.",
        atoms={"P": (0, 160), "sz": (0, 160)},
        hyps=HYP_P + [("hsz1", "P ≤ sz"), ("hsz2", "sz ≤ P + 32"), ("hszm", "sz % 32 = 0")],
        vars=["x0", "x2", "x4", "x5", "x6", "x7"],
        stack=[v("x0"), lit(0), v("x2"), lit(128), v("x4"), v("x5"), v("x6"), v("x7")],
        size=Aff(0, {"sz": 1}), words=[(Aff(64), aff(P), "hfp")], frame=("96", "P"),
    ),
    dict(
        name="sb2704", pc=2704, stop=3580,
        doc="The digest of `permit`, the read of the length of the signature and the branch for a "
            "length that is not 65 (pc 2704 to the EXTCODESIZE at pc 3580). `Q` is the free memory "
            "pointer, `L` the length.",
        atoms={"Q": (0, 384), "L": (0, 0)},
        hyps=[("hQ", "Q % 32 = 0"), ("hQ0", "384 ≤ Q"), ("hQb", "Q < 2 ^ 100"), ("hL", "L < 2 ^ 64")],
        vars=["x2", "x4", "x5", "x6", "x7", "dom", "sh"],
        stack=[aff(Aff(98, {"Q": 1})), lit(0), v("x2"), lit(128), v("x4"), v("x5"), v("x6"), v("x7")],
        size=Aff(128, {"Q": 1}),
        words=[(Aff(64), aff(Aff(0, {"Q": 1})), "hfp"), (Aff(128), aff(Aff(0, {"L": 1})), "hw128"),
               (Aff(34, {"Q": 1}), v("dom"), "hdom"), (Aff(66, {"Q": 1}), v("sh"), "hsh")],
        tops=[(Aff(32, {"Q": 1}), 2, lit(11309588061646438093662687302255421419811724423900836950936401294474059186176), "htop")],
        branches=[(True, "hlen")],
        frame=("96", "Q"),
    ),
]

F = Aff(0, {"F": 1})
X = Aff(0, {"X": 1})
SZ = Aff(0, {"s": 1})
HYP_F = [("hF", "F % 32 = 2"), ("hF0", "482 ≤ F"), ("hFb", "F < 2 ^ 100"), ("hL", "L < 2 ^ 64")]
HYP_C = [("hc1", "c % 32 = 0"), ("hc2", "L ≤ c"), ("hc3", "c < L + 32")]
BODY = ["dg", "nonce", "deadline", "value", "spender", "owner", "sel"]


def body_stack():
    return [v("dg"), v("nonce"), lit(128), v("deadline"), v("value"), v("spender"), v("owner"),
            lit(558), v("sel")]


def check_plain(st):
    for x in st:
        assert "memoryReadBytes" not in lean(x), "a word read from the memory stays on the stack"


def encoder():
    """The code from the test of the size of the code of the owner to the GAS before the
    STATICCALL, around the two runs of the copy routine (pc 3812 to 3847)."""
    out = []
    e1 = Seg(dict(
        name="sbE1", pc=3586, stop=3812,
        doc="The start of the call data of `isValidSignature` (pc 3586 to the copy routine at pc "
            "3812): the digest, the offset 64 and the length are written from `F + 36`. `F` is the "
            "free memory pointer, `L` the length of the signature.",
        atoms={"F": (2, 482), "L": (0, 0)}, hyps=HYP_F, vars=BODY,
        stack=[lit(0), lit(128), v("dg"), v("owner"), lit(2739)] + body_stack(),
        size=F.plus(30),
        words=[(Aff(64), aff(F), "hfp"), (Aff(128), aff(Aff(0, {"L": 1})), "hw128")],
        frame=("96", "F + 36")))
    out.append(e1.text())
    check_plain(e1.stack)
    e2 = Seg(dict(
        name="sbE2", pc=3847, stop=3812,
        doc="After the copy of the signature (pc 3847) to the second run of the copy routine: the "
            "length of the call data is written at `F`, the free memory pointer moves to "
            "`F + c + 132`, and the selector is written over the first 4 bytes at `F + 32`. `c` is "
            "the length rounded up to 32 and `s` the size of the memory.",
        atoms={"F": (2, 482), "L": (0, 0), "c": (0, 0), "s": (0, 0)},
        hyps=HYP_F + HYP_C + [("hs0", "s % 32 = 0"), ("hs1", "F + 158 ≤ s"), ("hsb", "s < 2 ^ 100")],
        vars=BODY, nogrow=True, ceil=("L + 31", "c"),
        stack=e1.stack[3:], size=SZ, words=[(Aff(64), aff(F), "hfp"), (Aff(96), lit(0), "hw96")],
        frame=("F + 64", "s")))
    out.append(e2.text())
    check_plain(e2.stack)
    e3 = Seg(dict(
        name="sbE3", pc=3847, stop=3681,
        doc="After the second copy (pc 3847) to the GAS before the STATICCALL to the owner (pc "
            "3681), with the arguments of the call on the stack.",
        atoms={"F": (2, 482), "c": (0, 0), "s": (0, 0)},
        hyps=[("hF", "F % 32 = 2"), ("hF0", "482 ≤ F"), ("hFb", "F < 2 ^ 100"), ("hc1", "c % 32 = 0"),
              ("hcb", "c < 2 ^ 100"), ("hs0", "s % 32 = 0"), ("hs1", "F + c + 164 ≤ s"),
              ("hsb", "s < 2 ^ 100")],
        vars=BODY, nogrow=True,
        stack=e2.stack[3:], size=SZ, words=[(Aff(64), aff(Aff(132, {"F": 1, "c": 1})), "hfp")],
        frame=("0", "s")))
    out.append(e3.text())
    return out


def answer():
    """The code after the STATICCALL, from the checks of the answer to the end."""
    out = []
    hyps = [("hX0", "128 ≤ X"), ("hX1", "X + 96 ≤ s"), ("hs0", "s % 32 = 0"), ("hsb", "s < 2 ^ 100")]

    def st(flag, top):
        return top + [lit(flag), lit(0), lit(0), lit(0), lit(128), v("dg"), v("owner"), lit(2739)] + body_stack()

    def seg(name, doc, flag, branches, stop, pc=3725):
        top = [lit(32), aff(X)] if pc == 3725 else [lit(0), lit(0)]
        words = [(Aff(64), aff(X.plus(64)), "hfp"), (X, lit(32), "hwX"), (X.plus(32), v("ans"), "hans")]
        if pc == 3729:
            words = [(Aff(96), lit(0), "hw96")]
        return Seg(dict(
            name=name, pc=pc, stop=stop, doc=doc,
            atoms={"X": (0, 128), "s": (0, 0)} if pc == 3725 else {"s": (0, 0)},
            hyps=hyps if pc == 3725 else [("hs1", "128 ≤ s")],
            vars=BODY + (["ans"] if pc == 3725 else []), nogrow=True, stack=st(flag, top), size=SZ,
            words=words, branches=branches, frame=("0", "0")))

    out.append(seg("sbA0", "The checks of the answer when the STATICCALL pushed 0: the code is at pc "
                   "3753 with a zero on the stack.", 0, [], 3753).text())
    out.append(seg("sbA1m", "The checks of the answer when the STATICCALL pushed 1 and the answer "
                   "has a nonzero bit after its first 4 bytes: the decoder is at its REVERT.",
                   1, [(False, "hm")], 4762).text())
    out.append(seg("sbA1e", "The checks of the answer when the STATICCALL pushed 1 and the first 4 "
                   "bytes of the answer are not the magic value: the code is at the revert of "
                   "`Sky/invalid-permit`.", 1, [(True, "hm"), (False, "he")], 2744).text())
    ok = seg("sbA1", "The checks of the answer when the STATICCALL pushed 1 and the answer is the "
             "magic value: the code is at the write of the allowance (pc 2804).",
             1, [(True, "hm"), (True, "he")], 2804)
    out.append(ok.text())
    w = Seg(dict(
        name="sbW", pc=2804, stop=558,
        doc="The write of the allowance and the log `Approval` (pc 2804 to the JUMPDEST at pc 558), "
            "for a free memory pointer `X + 64` and a memory of `s` bytes.",
        atoms={"X": (0, 128), "s": (0, 0)}, hyps=hyps, vars=BODY, nogrow=True,
        stack=ok.stack, size=SZ, words=[(Aff(64), aff(X.plus(64)), "hfp")], frame=("0", "0")))
    out.append(w.text())
    out.append(Seg(dict(
        name="sbW_2", pc=2804, stop=558, stuck=True,
        doc="The write of the allowance (from pc 2804) when the call is static or the token "
            "account does not exist: the run stops with an error at the SSTORE.",
        atoms={"X": (0, 128), "s": (0, 0)}, hyps=hyps, vars=BODY, nogrow=True,
        stack=ok.stack, size=SZ, words=[(Aff(64), aff(X.plus(64)), "hfp")], frame=("0", "0"))).text())
    out.append(seg("sbN0", "No return data and a 0 pushed by the STATICCALL: the code is at pc 3753 "
                   "with a zero on the stack.", 0, [], 3753, pc=3729).text())
    out.append(seg("sbN1", "No return data and a 1 pushed by the STATICCALL: the word at 96 is read "
                   "as the answer, its length 0 is not 32, and the code is at pc 3753 with a zero "
                   "on the stack.", 1, [], 3753, pc=3729).text())
    return out


def tails():
    return [
        tail("tail_deadline", "From pc 2296 (the deadline is passed): the code reverts with "
             "`Sky/permit-expired`, so no run ends with no error. The memory is any memory.", 2296, []),
        tail("tail_owner", "From pc 2371 (the owner is the zero address): the code reverts, so no run "
             "ends with no error.", 2371, []),
        tail("tail_no_code", "From pc 1432 with a zero on the stack (the owner holds no code): the "
             "code reverts with `Sky/invalid-permit`, so no run ends with no error.", 1432,
             [0, None, None, None, 2739]),
        tail("tail_mask", "From pc 4762 (the answer of the owner has a nonzero bit after its first "
             "4 bytes): the decoder reverts.", 4762, []),
        tail("tail_magic", "From pc 2744 (the answer of the owner is not the magic value): the code "
             "reverts with `Sky/invalid-permit`.", 2744, []),
    ]


HEADER = '''import SkyVerify.Sky.BytesWord

/-!
# Segments of `permit` with a signature as bytes, at memory offsets that depend on the length

Generated by `scripts/symgen.py`; do not edit.

Each segment is a triple with exact gas over a memory `mem` of which the hypotheses give the size
and the words that the segment reads. The offsets are sums of numerals and of natural numbers
(`P`, `Q`: a free memory pointer; `L`: the length of the signature); the side conditions on them
are closed by `omega`. `<name>_M` is the memory after the segment and `<name>_mem` gives its
size, its known words and the bytes that the segment does not write.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SkyVerify

open UsdtVerify
open TokenKit TokenKit.Complete
open SkyVerify.Blocks SkyVerify.Complete UsdtVerify.Complete UsdtVerify.Gas

open EthLib.Base (Fork U256 Address toAddressMasked byteAt)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic
open GasCosts

variable {fork : Fork} {message : Message fork}

'''


def build():
    out = [HEADER]
    for (src, new, doc) in [
        ("b2430_0", "sb2430_0", "The read and the write of the nonce (pc 2430), chain id not 1, for any memory of 64 bytes or more."),
        ("b2430_1", "sb2430_1", "The read and the write of the nonce (pc 2430), chain id 1, for any memory of 64 bytes or more."),
        ("b2430_2", "sb2430_2", "The write of the nonce in a static frame or with no account is stuck, for any memory of 64 bytes or more."),
    ]:
        out.append(derived("B12.lean", src, new, doc))
    for sp in SEGS:
        out.append(Seg(sp).text())
    out.extend(encoder())
    out.extend(answer())
    out.extend(tails())
    out.append("end SkyVerify\n")
    return "\n".join(out)


if __name__ == "__main__":
    text = build()
    if "--check" in sys.argv:
        if open(OUT).read() != text:
            sys.exit("BytesGen.lean differs from the output of scripts/symgen.py")
        print("BytesGen.lean is up to date")
    else:
        open(OUT, "w").write(text)
        print("wrote", OUT, len(text.splitlines()), "lines")

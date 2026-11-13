"""Symbolic walk of the LINK bytecode for the transferAndCall proofs.

Reads the disassembly (pc, hex pc, opcode, immediate) and walks it with a stack of Lean terms.
Stack-only opcodes give their `step` line; memory, storage, log and account opcodes are given by
the caller as hand-written lines (see gen_tac.py).
"""
import re

M256 = 1 << 256


def load_dis(path):
    ops = {}
    for line in open(path):
        p = line.split()
        if len(p) < 3:
            continue
        pc = int(p[0])
        ops[pc] = (p[2], int(p[3], 16) if len(p) > 3 else None)
    return ops


def lit(n):
    return "(%d : U256)" % n


def tm(x):
    return lit(x) if isinstance(x, int) else x


BIN = {
    "ADD": ("0x01", "instruction_add", "add", lambda a, b: (a + b) % M256),
    "MUL": ("0x02", "(instruction_of_stackOnlyStep rfl)", "mul", lambda a, b: (a * b) % M256),
    "SUB": ("0x03", "instruction_sub", "sub", lambda a, b: (a - b) % M256),
    "DIV": ("0x04", "(instruction_of_stackOnlyStep rfl)", "div", lambda a, b: 0 if b == 0 else a // b),
    "LT": ("0x10", "(instruction_of_stackOnlyStep rfl)", "lessThan", lambda a, b: int(a < b)),
    "GT": ("0x11", "(instruction_of_stackOnlyStep rfl)", "greaterThan", lambda a, b: int(a > b)),
    "EQ": ("0x14", "(instruction_of_stackOnlyStep rfl)", "equal", lambda a, b: int(a == b)),
    "AND": ("0x16", "(instruction_of_stackOnlyStep rfl)", "bitwiseAnd", lambda a, b: a & b),
}
UN = {
    "ISZERO": ("0x15", "instruction_iszero", "isZero", lambda a: int(a == 0)),
    "NOT": ("0x19", "(instruction_of_stackOnlyStep rfl)", "bitwiseNot", lambda a: (M256 - 1) ^ a),
}


class Walk:
    def __init__(self, ops, pc, stack):
        self.ops = ops
        self.pc = pc
        self.stack = list(stack)  # top first
        self.lines = []
        self.gas = 0  # the fixed part of the gas
        self.gsym = []  # symbolic parts of the gas
        self.trace = []

    def emit(self, s):
        self.lines.append("  " + s)

    def fold(self, new, proof="by decide +kernel"):
        """Replace the top of the stack by an equal term."""
        self.emit("step foldK (y := %s) (%s)" % (tm(new), proof))
        self.stack[0] = new

    def op(self):
        return self.ops[self.pc]

    def step(self, taken=None, hyp=None):
        """One stack-only opcode. Returns False at an opcode it does not know."""
        name, imm = self.ops[self.pc]
        st = self.stack
        self.trace.append((self.pc, name, list(st)))
        if name == "JUMPDEST":
            self.emit("step jumpdestR")
            self.gas += 1
            self.pc += 1
        elif name.startswith("PUSH"):
            n = int(name[4:])
            self.emit("step pushR %d %s" % (n, lit(imm)))
            self.emit("at_pc %d" % (self.pc + 1 + n))
            st.insert(0, imm)
            self.gas += 3
            self.pc += 1 + n
        elif name.startswith("DUP"):
            n = int(name[3:])
            self.emit("step dupR %d" % (n - 1))
            st.insert(0, st[n - 1])
            self.gas += 3
            self.pc += 1
        elif name.startswith("SWAP"):
            n = int(name[4:])
            self.emit("step swap%dK (by code_fact) (by code_fact) (by gas_ok)" % n)
            st[0], st[n] = st[n], st[0]
            self.gas += 3
            self.pc += 1
        elif name == "POP":
            self.emit("step popR")
            st.pop(0)
            self.gas += 2
            self.pc += 1
        elif name in BIN:
            byte, ins, f, ev = BIN[name]
            a, b = st.pop(0), st.pop(0)
            self.emit("step binR %s %s" % (byte, ins))
            self.gas += 5 if name in ("MUL", "DIV") else 3
            self.pc += 1
            if isinstance(a, int) and isinstance(b, int):
                st.insert(0, "(%s %s %s)" % (f, lit(a), lit(b)))
                self.fold(ev(a, b))
            else:
                st.insert(0, "(%s %s %s)" % (f, tm(a), tm(b)))
        elif name in UN:
            byte, ins, f, ev = UN[name]
            a = st.pop(0)
            self.emit("step unR %s %s" % (byte, ins))
            self.gas += 3
            self.pc += 1
            if isinstance(a, int):
                st.insert(0, "(%s %s)" % (f, lit(a)))
                self.fold(ev(a))
            else:
                st.insert(0, "(%s %s)" % (f, tm(a)))
        elif name == "EXP":
            if not (isinstance(st[0], int) and isinstance(st[1], int)):
                return False
            a, b = st.pop(0), st.pop(0)
            e = (b.bit_length() + 7) // 8
            self.emit("step expK hfork (by code_fact) (by code_fact) (e := %d) (by decide +kernel) (by gas_ok)" % e)
            st.insert(0, "(Evm.exp %s %s)" % (lit(a), lit(b)))
            self.gas += 10 + 50 * e
            self.pc += 1
            self.fold(pow(a, b, M256))
        elif name == "CALLER":
            self.emit("step Gas.callerG (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)")
            st.insert(0, "message.caller.toU256")
            self.gas += 2
            self.pc += 1
        elif name == "ADDRESS":
            self.emit("step addressL (by code_fact) (by code_fact) (by gas_ok) (by stk_ok)")
            st.insert(0, "message.currentTarget.toU256")
            self.gas += 2
            self.pc += 1
        elif name == "JUMP":
            d = st.pop(0)
            assert isinstance(d, int), (self.pc, d)
            self.emit("step jumpR")
            self.gas += 8
            self.pc = d
        elif name == "JUMPI":
            d, c = st.pop(0), st.pop(0)
            assert isinstance(d, int), (self.pc, d)
            assert taken is not None, (self.pc, c)
            self.cond = c
            self.gas += 10
            if taken:
                self.emit("step jumpiR %s" % hyp)
                self.pc = d
            else:
                self.emit("step jumpi0R %s" % hyp)
                self.pc += 1
        else:
            return False
        return True

    def run(self, stop=(), branches=None):
        """Walk until an opcode that is not stack-only, a pc of `stop`, or a JUMPI with no
        branch given. `branches` maps the pc of a JUMPI to (taken, hypothesis)."""
        branches = branches or {}
        while self.pc not in stop:
            name, _ = self.ops[self.pc]
            if name == "JUMPI":
                if self.pc not in branches:
                    return
                t, h = branches[self.pc]
                self.step(t, h)
            elif not self.step():
                return

    def show(self):
        return "%d %s [%s]" % (self.pc, self.ops[self.pc][0], ", ".join(tm(x) for x in self.stack))

#!/usr/bin/env python3
"""Read-only check, for every token: the code constant in the Lean source equals the deployed
runtime bytecode of survey/tokens/<SYM>/runtime.hex byte for byte.

For each token it reads token-kit/tokens/<t>/<Root>Verify/<Tok>/Code/Bytes.lean (CODE_NAT, CODE_SIZE)
and checks: CODE_NAT, padded to CODE_SIZE bytes, equals runtime.hex; CODE_SIZE is the byte count;
token-kit/tokens/<t>/data/<t>.runtime.hex is the same file; the keccak256 of the bytes is the one
in <Root>Verify/Test/Hash.lean and in survey/tokens/<SYM>/SOURCE.md.
Based on the code checks of the audits (one per token before; one script for all 15 now).

Usage: python3 -I audits/check_code.py   (from any folder; exit code 0 when all 15 pass)
"""
import glob, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TOKENS = "shib qnt bnb weth pepe wbt usdd dai usde ena sky link wbtc uni ondo".split()

# --- own keccak-256 (original padding 0x01) ---
RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
      0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
      0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56],
       [27, 20, 39, 8, 14]]
M = (1 << 64) - 1


def rol(x, n):
    n %= 64
    return ((x << n) | (x >> (64 - n))) & M if n else x


def f(A):
    for rc in RC:
        C = [A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4] for x in range(5)]
        D = [C[(x - 1) % 5] ^ rol(C[(x + 1) % 5], 1) for x in range(5)]
        A = [[A[x][y] ^ D[x] for y in range(5)] for x in range(5)]
        B = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                B[y][(2 * x + 3 * y) % 5] = rol(A[x][y], ROT[x][y])
        A = [[B[x][y] ^ ((~B[(x + 1) % 5][y]) & B[(x + 2) % 5][y]) for y in range(5)]
             for x in range(5)]
        A[0][0] ^= rc
    return A


def keccak(data: bytes) -> bytes:
    rate = 136
    p = bytearray(data) + b"\x01"
    while len(p) % rate:
        p += b"\x00"
    p[-1] |= 0x80
    A = [[0] * 5 for _ in range(5)]
    for i in range(0, len(p), rate):
        blk = p[i:i + rate]
        for j in range(rate // 8):
            x, y = j % 5, j // 5
            A[x][y] ^= int.from_bytes(blk[8 * j:8 * j + 8], "little")
        A = f(A)
    out = b""
    for j in range(4):
        out += A[j % 5][j // 5].to_bytes(8, "little")
    return out



assert keccak(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"


def read_hex(p):
    h = open(p).read().strip().lower()
    return h[2:] if h.startswith("0x") else h


def check(t):
    sym = t.upper()
    proj = os.path.join(ROOT, "token-kit", "tokens", t)
    (bytes_lean,) = glob.glob(os.path.join(proj, "*Verify", "*", "Code", "Bytes.lean"))
    (hash_lean,) = glob.glob(os.path.join(proj, "*Verify", "Test", "Hash.lean"))
    hx = read_hex(os.path.join(ROOT, "survey", "tokens", sym, "runtime.hex"))
    data = read_hex(os.path.join(proj, "data", f"{t}.runtime.hex"))
    src = open(bytes_lean).read()
    nat = re.search(r"def CODE_NAT : Nat :=\s*0x([0-9a-fA-F]+)", src).group(1).lower()
    size = int(re.search(r"def CODE_SIZE : Nat :=\s*(\d+)", src).group(1))
    k = keccak(bytes.fromhex(hx)).hex()
    r = {
        "bytes": len(hx) // 2,
        "code_eq_runtime_hex": nat.rjust(2 * size, "0") == hx,
        "code_size_eq": size == len(hx) // 2,
        "data_hex_eq": data == hx,
        "keccak_in_hash_lean": k in open(hash_lean).read().lower(),
        "keccak_in_source_md": k in open(os.path.join(ROOT, "survey", "tokens", sym, "SOURCE.md")).read().lower(),
    }
    r["ok"] = all(v for key, v in r.items() if key != "bytes")
    return r, k


def main():
    bad = 0
    for t in TOKENS:
        r, k = check(t)
        bad += not r["ok"]
        flags = " ".join(f"{key}={v}" for key, v in r.items() if key not in ("bytes", "ok"))
        print(f"{t:5} {'PASS' if r['ok'] else 'FAIL'} {r['bytes']:6} bytes keccak {k[:8]}..{k[-4:]} {flags}")
    print(f"{len(TOKENS) - bad}/{len(TOKENS)} pass")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

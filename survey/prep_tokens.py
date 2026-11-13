#!/usr/bin/env python3
"""Step 1-4 of the usdt-verify recipe for each "same recipe" token:
fetch runtime bytecode, record its source, build the selector map.

Usage: ETHERSCAN_KEY=... python3 -I prep_tokens.py <keccak_dir>
Writes tokens/<SYM>/{runtime.hex,SOURCE.md,MAP.md,abi.json} and tokens/summary.json.
"""
import datetime, json, os, sys, time, urllib.parse, urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, sys.argv[1])
from keccak import keccak256  # noqa: E402

RPC = "https://ethereum-rpc.publicnode.com"
ES = "https://api.etherscan.io/v2/api"
KEY = os.environ["ETHERSCAN_KEY"]
WANT = ["BNB", "LEO", "WBTC", "WBT", "LINK", "USDE", "DAI", "WETH", "UNI", "GRAM", "QNT",
        "SHIB", "CRO", "PEPE", "ENA", "ONDO", "USDD", "SKY"]

NAMES = {0x00: "STOP", 0x14: "EQ", 0x20: "SHA3", 0x54: "SLOAD", 0x55: "SSTORE", 0x56: "JUMP",
         0x57: "JUMPI", 0x5b: "JUMPDEST", 0x5f: "PUSH0", 0xf0: "CREATE", 0xf1: "CALL",
         0xf2: "CALLCODE", 0xf3: "RETURN", 0xf4: "DELEGATECALL", 0xf5: "CREATE2",
         0xfa: "STATICCALL", 0xfd: "REVERT", 0xfe: "INVALID", 0xff: "SELFDESTRUCT",
         0x31: "BALANCE", 0x47: "SELFBALANCE", 0x46: "CHAINID", 0x42: "TIMESTAMP",
         0x43: "NUMBER", 0x3b: "EXTCODESIZE", 0x3d: "RETURNDATASIZE", 0x3e: "RETURNDATACOPY",
         0x1b: "SHL", 0x1c: "SHR", 0x5c: "TLOAD", 0x5d: "TSTORE", 0x5e: "MCOPY",
         0x80: "DUP1", 0x81: "DUP2"}
for i in range(5):
    NAMES[0xa0 + i] = f"LOG{i}"


def get(url, data=None):
    err = None
    for i in range(4):
        try:
            req = urllib.request.Request(url, data=data, headers={
                "User-Agent": "token-survey/1.0", "Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=40) as r:
                return json.loads(r.read())
        except Exception as e:  # noqa
            err = e
            time.sleep(2 + 3 * i)
    raise err


def rpc(method, params):
    return get(RPC, json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                                "params": params}).encode()).get("result")


def es(action, addr):
    q = urllib.parse.urlencode({"chainid": 1, "module": "contract", "action": action,
                                "address": addr, "apikey": KEY})
    time.sleep(0.25)
    return get(f"{ES}?{q}").get("result")


def disasm(code):
    pc = 0
    while pc < len(code):
        op = code[pc]
        if 0x60 <= op <= 0x7f:
            n = op - 0x5f
            yield pc, f"PUSH{n}", code[pc + 1:pc + 1 + n].hex()
            pc += 1 + n
        else:
            yield pc, NAMES.get(op, f"op{op:02x}"), ""
            pc += 1


def strip_meta(code):
    """Drop the trailing CBOR metadata solc appends, when it is there."""
    if len(code) > 2:
        n = int.from_bytes(code[-2:], "big")
        if 30 <= n <= 120 and len(code) > n + 2 and code[-2 - n] in (0xa1, 0xa2, 0xa3, 0xa4):
            return code[:-2 - n], n + 2
    return code, 0


def canon(t):
    if t["type"].startswith("tuple"):
        return "(" + ",".join(canon(c) for c in t["components"]) + ")" + t["type"][5:]
    return t["type"]


def main():
    rows = {r["sym"]: r for r in json.load(open(os.path.join(HERE, "tokens.json")))}
    block = int(rpc("eth_blockNumber", []), 16)
    today = datetime.date.today().isoformat()
    summary = []
    for sym in WANT:
        r = rows[sym]
        addr = r["addr"]
        d = os.path.join(HERE, "tokens", sym)
        os.makedirs(d, exist_ok=True)
        code = bytes.fromhex(rpc("eth_getCode", [addr, hex(block)])[2:])
        open(os.path.join(d, "runtime.hex"), "w").write(code.hex() + "\n")
        h = keccak256(code).hex()
        src = es("getsourcecode", addr)[0]
        try:
            abi = json.loads(src.get("ABI") or "[]")
        except Exception:  # noqa
            abi = []
        json.dump(abi, open(os.path.join(d, "abi.json"), "w"), indent=1)
        sigs = {}
        for f in abi:
            if f.get("type") == "function":
                s = f["name"] + "(" + ",".join(canon(i) for i in f["inputs"]) + ")"
                sigs[keccak256(s.encode())[:4].hex()] = (s, f.get("stateMutability") or
                                                         ("view" if f.get("constant") else "nonpayable"))
        body, meta = strip_meta(code)
        ins = list(disasm(body))
        table = []
        for i, (pc, name, arg) in enumerate(ins):
            if name in ("PUSH4", "PUSH3") and i + 4 < len(ins):
                nxt = [x[1] for x in ins[i + 1:i + 5]]
                k = 1 if nxt[0] == "EQ" else (2 if nxt[0] == "DUP2" and nxt[1] == "EQ" else 0)
                if k and ins[i + k + 1][1] in ("PUSH2", "PUSH1") and ins[i + k + 2][1] == "JUMPI":
                    table.append((pc, arg.rjust(8, "0"), int(ins[i + k + 1][2], 16)))
        cnt = {}
        for _, name, _ in ins:
            if not name.startswith(("PUSH", "op", "DUP")):
                cnt[name] = cnt.get(name, 0) + 1
        found = {t[1] for t in table}
        missing = sorted(set(sigs) - found)
        unknown = sorted(found - set(sigs))
        writers = [s for k, (s, m) in sigs.items() if m not in ("view", "pure")]
        with open(os.path.join(d, "SOURCE.md"), "w") as f:
            f.write(f"# Source of `runtime.hex`\n\n- Contract: {src.get('ContractName')} ({sym}), {addr}, "
                    f"Ethereum mainnet.\n- Fetched on {today} with one JSON-RPC `eth_getCode` call at "
                    f"block {block} ({hex(block)}).\n- Endpoint: {RPC} (generic User-Agent, no other data "
                    f"sent).\n- Size: {len(code)} bytes ({meta} of them trailing compiler metadata).\n"
                    f"- keccak256: 0x{h} (pure Python, upstream `scripts/keccak.py`).\n"
                    f"- Compiler per Etherscan: {src.get('CompilerVersion')}, optimizer "
                    f"{src.get('OptimizationUsed')}, runs {src.get('Runs')}, EVM {src.get('EVMVersion')}.\n")
        with open(os.path.join(d, "MAP.md"), "w") as f:
            f.write(f"# Map of the {sym} runtime bytecode\n\n| entry pc | selector | signature | kind | "
                    "destination |\n|---|---|---|---|---|\n")
            for pc, sel, dest in table:
                s, m = sigs.get(sel, ("?", "?"))
                f.write(f"| {pc} | 0x{sel} | {s} | {m} | {dest} (0x{dest:04x}) |\n")
            f.write(f"\nInstructions: {len(ins)}; opcode counts: {json.dumps(cnt, sort_keys=True)}.\n")
            if missing:
                f.write("\nABI functions with no table entry found: "
                        + ", ".join(sigs[k][0] for k in missing) + "\n")
            if unknown:
                f.write("\nTable selectors not in the ABI: " + ", ".join(unknown) + "\n")
        summary.append({"sym": sym, "addr": addr, "name": src.get("ContractName"),
                        "compiler": src.get("CompilerVersion"), "opt": src.get("OptimizationUsed"),
                        "bytes": len(code), "keccak": h, "instr": len(ins),
                        "table": len(table), "abi_fns": len(sigs), "writers": sorted(writers),
                        "missing": [sigs[k][0] for k in missing], "unknown": unknown, "counts": cnt})
        print(sym, len(code), len(ins), len(table), len(sigs), len(writers), file=sys.stderr)
    json.dump({"block": block, "date": today, "tokens": summary},
              open(os.path.join(HERE, "tokens", "summary.json"), "w"), indent=1)


if __name__ == "__main__":
    main()

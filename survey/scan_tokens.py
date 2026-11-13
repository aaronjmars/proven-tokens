#!/usr/bin/env python3
"""Top Ethereum tokens by market cap: contract structure survey.

Reads ETHERSCAN_KEY from env. Writes tokens.json next to this script.
"""
import json, os, sys, time, urllib.request, urllib.parse

RPC = "https://ethereum-rpc.publicnode.com"
ES = "https://api.etherscan.io/v2/api"
KEY = os.environ["ETHERSCAN_KEY"]
N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tokens.json")


def get(url, data=None, tries=4):
    for i in range(tries):
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
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    return get(RPC, body).get("result")


def source(addr):
    q = urllib.parse.urlencode({"chainid": 1, "module": "contract", "action": "getsourcecode",
                                "address": addr, "apikey": KEY})
    r = get(f"{ES}?{q}")
    time.sleep(0.25)
    res = r.get("result")
    if not isinstance(res, list):
        return {"err": str(res)[:80]}
    x = res[0]
    return {"name": x.get("ContractName"), "compiler": x.get("CompilerVersion"),
            "opt": x.get("OptimizationUsed"), "runs": x.get("Runs"),
            "proxy": x.get("Proxy"), "impl": x.get("Implementation"),
            "verified": bool(x.get("SourceCode"))}


OPS = {0xF1: "CALL", 0xF2: "CALLCODE", 0xF4: "DELEGATECALL", 0xFA: "STATICCALL",
       0x55: "SSTORE", 0x54: "SLOAD", 0xF0: "CREATE", 0xF5: "CREATE2", 0xFF: "SELFDESTRUCT",
       0x5C: "TLOAD", 0x5D: "TSTORE", 0x01: "ECADD?", 0x20: "KECCAK", 0x5B: "JUMPDEST",
       0x57: "JUMPI", 0x56: "JUMP"}


def analyze(code_hex):
    b = bytes.fromhex(code_hex[2:])
    counts, sels, i, prev4 = {}, set(), 0, None
    n_ops = 0
    while i < len(b):
        op = b[i]
        n_ops += 1
        if 0x60 <= op <= 0x7F:
            n = op - 0x5F
            if op == 0x63:
                prev4 = b[i + 1:i + 5].hex()
            i += 1 + n
            continue
        if op == 0x14 and prev4:  # EQ right after PUSH4 = selector compare
            sels.add(prev4)
        if op not in (0x80, 0x81, 0x90):
            prev4 = None if op != 0x14 else None
        name = OPS.get(op)
        if name:
            counts[name] = counts.get(name, 0) + 1
        i += 1
    # ecrecover hint: permit selector
    return {"bytes": len(b), "ops": n_ops, "selectors": len(sels),
            "permit": "d505accf" in sels, "counts": counts,
            "sels": sorted(sels)}


def main():
    mk = []
    for page in (1, 2):
        mk += get("https://api.coingecko.com/api/v3/coins/markets?vs_currency=usd"
                  f"&category=ethereum-ecosystem&order=market_cap_desc&per_page=250&page={page}")
        time.sleep(2)
    plat = {c["id"]: c.get("platforms", {}) for c in
            get("https://api.coingecko.com/api/v3/coins/list?include_platform=true")}
    rows = []
    for c in mk:
        addr = (plat.get(c["id"]) or {}).get("ethereum")
        if not addr:
            continue
        rows.append({"rank": len(rows) + 1, "id": c["id"], "sym": c["symbol"].upper(),
                     "mcap": c["market_cap"], "addr": addr})
        if len(rows) >= N:
            break
    for r in rows:
        try:
            code = rpc("eth_getCode", [r["addr"], "latest"]) or "0x"
            r["src"] = source(r["addr"])
            r["code"] = analyze(code)
            impl = r["src"].get("impl") or ""
            if not impl:
                for slot in ("0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc",
                             "0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3"):
                    v = rpc("eth_getStorageAt", [r["addr"], slot, "latest"]) or "0x0"
                    if int(v, 16):
                        impl = "0x" + v[-40:]
                        break
            if impl and int(impl, 16):
                r["impl_addr"] = impl
                r["impl_src"] = source(impl)
                r["impl_code"] = analyze(rpc("eth_getCode", [impl, "latest"]) or "0x")
        except Exception as e:  # noqa
            r["error"] = repr(e)[:120]
        print(r["rank"], r["sym"], r.get("code", {}).get("bytes"), r.get("impl_addr", ""),
              r.get("error", ""), file=sys.stderr)
    json.dump(rows, open(OUT, "w"), indent=1)
    print(OUT)


if __name__ == "__main__":
    main()

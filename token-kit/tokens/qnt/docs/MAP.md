# Map of the QNT proof

> Kit layout: this project is `tokens/qnt` of the token kit. `scripts/...` below means the scripts of the kit (`../../scripts`), run as `bash ../../scripts/regen.sh config/qnt.json`; the generic Lean files are the library `TokenKit` of the kit (`../../TokenKit/Evm`), not a folder of this project.

Contract: QNT (Quant, contract name StandardToken), 0x4a220e6096b25eadb88358cb44068a3248254675,
runtime bytecode of 5155 bytes (solc 0.4.21, optimizer off), keccak256
37a685d7f4eca5e68dbfeae3fecdd7ec467dcac37d5c0c90591de54d5ea525c1. Every statement is about these
bytes (`QntVerify/Qnt/Code.lean`, `QntVerify/Test/Hash.lean`).

## Selector table (from the bytes, `python3 scripts/map.py config/qnt.json`)

| index | entry pc | selector | signature | destination | covered by |
|---|---|---|---|---|---|
| 0 | 54 | 0x06fdde03 | name() | 213 (0x00d5) | paths |
| 1 | 65 | 0x095ea7b3 | approve(address,uint256) | 355 (0x0163) | paths |
| 2 | 76 | 0x18160ddd | totalSupply() | 445 (0x01bd) | paths |
| 3 | 87 | 0x23b872dd | transferFrom(address,address,uint256) | 486 (0x01e6) | paths |
| 4 | 98 | 0x313ce567 | decimals() | 607 (0x025f) | paths |
| 5 | 109 | 0x40c10f19 | mint(address,uint256) | 654 (0x028e) | paths |
| 6 | 120 | 0x414d784e | DECIMAL_ZEROS() | 720 (0x02d0) | paths |
| 7 | 131 | 0x66188463 | decreaseApproval(address,uint256) | 761 (0x02f9) | paths |
| 8 | 142 | 0x70a08231 | balanceOf(address) | 851 (0x0353) | paths |
| 9 | 153 | 0x95d89b41 | symbol() | 928 (0x03a0) | paths |
| 10 | 164 | 0x9c1e03a0 | crowdsale() | 1070 (0x042e) | paths |
| 11 | 175 | 0xa9059cbb | transfer(address,uint256) | 1155 (0x0483) | paths |
| 12 | 186 | 0xd73dd623 | increaseApproval(address,uint256) | 1245 (0x04dd) | paths |
| 13 | 197 | 0xdd62ed3e | allowance(address,address) | 1335 (0x0537) | paths |

Instructions: 2142; JUMPDESTs at an opcode boundary: 83.

All 14 entries are covered by path theorems: 47 paths (15 success, 20 revert, 5 INVALID, 7 stuck:
SSTORE in a static frame or with no account) and a completeness theorem `ok_<fn>` per function. `name()` and
`symbol()` have no loop here (the strings are PUSHed constants), so their exact return bytes are
proved (`memW [32, 5, "Quant"]`, `memW [32, 3, "QNT"]`).

## Storage, as the bytecode reads it

- `balances[a]`: slot `mapSlot a 0`
- `totalSupply_`: slot 1 (read by `totalSupply()`, written by no function)
- `allowed[o][s]`: slot `mapSlot s (mapSlot o 2)`
- `crowdsale`: low 160 bits of slot 3 (read by `crowdsale()` and `mint`, written by no function)

## mint, as the bytes implement it

`mint(to, amount)` needs: no value, the address word of the caller equal to the low 160 bits of
slot 3, no overflow of `balances[to]` (overflow ends in INVALID 0xfe). It adds `amount` to
`balances[to]`, logs `Transfer(0, to, amount)` and stops with no return data. It does NOT write
slot 1, there is no cap and no mint-finished flag. So a mint with a nonzero amount breaks
"sum of balances = totalSupply_" (`goodCall_mint_D`).

## Where to read what is proved

- `QntVerify/Qnt/Readable.lean` - start here. `<fn>_readable` for the 14 functions: what a
  successful call needs of the call and the START state, in plain arithmetic, the output, the END
  storage in terms of the start storage and the exact logs. Functions that write take
  `Sep (callKeys message)`.
- `QntVerify/Qnt/Gen/P<Fn>.lean` - every path `<fn>_p<i>` with exact output, gas, state and logs,
  and `ok_<fn>`.
- `QntVerify/Qnt/Invariant.lean` - `supply_step`: a run that ends with no error keeps
  `D` = (sum of balances) - (slot 1), or it is `mint` and `D` grows by the amount word; slots 1
  and 3 keep their word.
- `QntVerify/Qnt/Seq.lean` - `mint_caller` (only the address in slot 3 can mint, no keccak
  hypothesis), and the lift to a top-level message run by EthLib's `processMessage` and to finite
  sequences: `calls_fixed` (slots 1 and 3 never change, `D` never goes down),
  `inv_calls_no_crowdsale` (with no call from the address in slot 3, sum of balances =
  `totalSupply_` is kept), `process_step`, `process_step_inv`. From Paris, one-counter meter.
- `QntVerify/Qnt/Sanity/` - every success path has a concrete run: `Zero.lean` (13 witnesses,
  amount 0, all-zero state) and `Moves.lean` (`transfer_moves`, `mint_runs`,
  `decreaseApproval_p2_runs`).

## Files

- `config/qnt.json` - everything about the token that the generators need.
- `TokenKit/Evm/` (the shared library of the kit, two folders up) - not about QNT, reusable (SHIB's files plus: aligned memory lemmas for any
  word list in `Mem`, `decided_by` in `Rules`, a few shapes in `Readable` and `Witness`).
- By hand: `QntVerify/Qnt/Sep.lean`, `Seq.lean`, `Sanity/Moves.lean`.
- Generated (do not edit; `bash scripts/regen.sh config/qnt.json`):
  - `Code/Bytes.lean`, `Test/Hash.lean` - `scripts/gen_code.py`.
  - `Code.lean`, `Steps.lean`, `Map.lean`, `Enter.lean`, `Spec/Dispatch.lean`,
    `Complete/Dispatch.lean` - `scripts/gen_dispatch.py` (table size, selectors, fallback pc and
    free pointer read from the bytes).
  - `Gen/B0..B4`, `Gen/P<Fn>`, `Gen.lean` - `scripts/gen_paths.py`: 171 block lemmas, the paths
    and `ok_<fn>`. 3 branches that an earlier condition of the same path decides are not followed.
  - `Invariant.lean` - `scripts/gen_supply.py` (mode `delta`).
  - `Readable.lean` - `scripts/gen_readable.py`. `Sanity/Zero.lean` - `scripts/gen_sanity.py`.
  - `Test/Axioms.lean` - `scripts/gen_axioms.py`: the axioms of 131 theorems.

## Rebuild

`bash scripts/regen.sh config/qnt.json`, then `lake build` (on the build box:
`bash scripts/build_box.sh qnt`) and `bash scripts/check_axioms.sh <build log>` (run it on Linux).

## Not proved

- `Sep` is an assumption about keccak256.
- `transferFrom` has one INVALID path (`sub` of the allowance after the balance writes) that the
  earlier checks exclude unless an allowance slot equals a balance slot; it is a proved path
  theorem, it is not shown unreachable (that would need `Sep`).
- The constructor and the first state are not verified; whether the live state has
  sum of balances = `totalSupply_` is not addressed.
- Completeness is about runs that end with no error; there is no theorem that every failing run
  is one of the proved revert / INVALID paths. Revert, INVALID and stuck paths have no witnesses.
- A success path theorem with an SSTORE takes gas above (its cost + 2300). `ok_<fn>` covers every
  run that ends with no error (exact cost, cost <= gas); that a run with gas between the cost and
  cost + 2300 does end with no error is not stated.
- The two-counter gas meter of EIP-8037.

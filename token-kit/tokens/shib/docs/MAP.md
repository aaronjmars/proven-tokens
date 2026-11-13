# Map of the SHIB proof

> Kit layout: this project is `tokens/shib` of the token kit. `scripts/...` below means the scripts of the kit (`../../scripts`), run as `bash ../../scripts/regen.sh config/shib.json`; the generic Lean files are the library `TokenKit` of the kit (`../../TokenKit/Evm`), not a folder of this project.

Contract: SHIB, 0x95ad61b0a150d79219dcf64e1e6cc01f0b64c4ce, runtime bytecode of 4852 bytes
(solc 0.5.0, optimizer off). Every statement is about these bytes (`ShibVerify/Shib/Code.lean`).

## Selector table (from the bytes, `python3 scripts/map.py config/shib.json`)

| index | entry pc | selector | signature | destination | covered by |
|---|---|---|---|---|---|
| 0 | 54 | 0x06fdde03 | name() | 191 (0x00bf) | read-only loop |
| 1 | 65 | 0x095ea7b3 | approve(address,uint256) | 335 (0x014f) | paths |
| 2 | 76 | 0x18160ddd | totalSupply() | 450 (0x01c2) | paths |
| 3 | 87 | 0x23b872dd | transferFrom(address,address,uint256) | 493 (0x01ed) | paths |
| 4 | 98 | 0x313ce567 | decimals() | 640 (0x0280) | paths |
| 5 | 109 | 0x39509351 | increaseAllowance(address,uint256) | 689 (0x02b1) | paths |
| 6 | 120 | 0x42966c68 | burn(uint256) | 804 (0x0324) | paths |
| 7 | 131 | 0x70a08231 | balanceOf(address) | 863 (0x035f) | paths |
| 8 | 142 | 0x95d89b41 | symbol() | 964 (0x03c4) | read-only loop |
| 9 | 153 | 0xa457c2d7 | decreaseAllowance(address,uint256) | 1108 (0x0454) | paths |
| 10 | 164 | 0xa9059cbb | transfer(address,uint256) | 1223 (0x04c7) | paths |
| 11 | 175 | 0xdd62ed3e | allowance(address,address) | 1338 (0x053a) | paths |

Instructions: 2292; JUMPDESTs at an opcode boundary: 95.

All 12 entries are covered. The 10 functions marked `paths` have every path proved (55 path
theorems: 10 success, 39 revert, 6 stuck SSTORE) and a completeness theorem `ok_<fn>`. `name()`
and `symbol()` loop over a string in storage: for them `ro_<fn>` proves that a run that ends
with no error writes no storage word and adds no log; the bytes they return are NOT proved.

## Storage, as the bytecode reads it

- `_balances[a]`: slot `mapSlot a 0`
- `_allowances[o][s]`: slot `mapSlot s (mapSlot o 1)`
- `_totalSupply`: slot 2
- `decimals`: slot 5

## Where to read what is proved

- `ShibVerify/Shib/Readable.lean` - start here. `<fn>_readable` for the 10 functions: what a
  successful call needs of the call and the START state, in plain arithmetic, and the output,
  the END storage in terms of the start storage and the exact logs. The case `to = from` of
  `transfer` and `transferFrom` is stated apart. Functions that write take `Sep (callKeys message)`.
- `ShibVerify/Shib/Invariant.lean` - `supply_preserved`: a run that ends with no error, with any
  selector, keeps "sum of all balances = `_totalSupply`".
- `ShibVerify/Shib/Seq.lean` - the same for a whole top-level message run by EthLib's
  `processMessage` (`process_step`, `process_step_inv`: it keeps the invariant or leaves the
  storage unchanged) and for any finite sequence of steps (`inv_calls`). From Paris, one-counter
  meter.
- `ShibVerify/Shib/Sanity/` - every success path has a concrete run: `Zero.lean` (`<fn>_runs`,
  amount 0, all-zero state) and `Moves.lean` (`transfer_moves`, a transfer of 1 from a balance
  of 5).

## Files

- `config/shib.json` - everything about the token that the generators need (see below).
- `TokenKit/Evm/` (the shared library of the kit, two folders up) - not about SHIB, reusable: `Mem` (memory as a list of words), `Rules`
  (one rule per opcode shape: MSTORE, MLOAD, mapping hash, LOG3, RETURN, REVERT, SLOAD, SSTORE),
  `Stack` (SWAP1..16), `Supply` (sum of balances against the total supply), `Readable` (raw
  conditions to plain arithmetic), `Witness` (tools for a concrete run), `Safe` (a run that only
  reads: `Ro`, the rules as facts about a run that ends with no error).
- `ShibVerify/Shib/Code.lean`, `Steps`, `Map`, `Spec/Dispatch`, `Complete/Dispatch`, `Enter` - the
  code, the prelude and the selector table, written by hand. `Sep.lean` - the invariant `Inv`,
  the hypothesis on keccak `Sep` and the slot rules, by hand. `Seq.lean`, `Sanity/Moves.lean` -
  by hand.
- Generated (do not edit; `bash scripts/regen.sh config/shib.json`):
  - `ShibVerify/Shib/Code/Bytes.lean`, `ShibVerify/Test/Hash.lean` - `scripts/gen_code.py`.
  - `ShibVerify/Shib/Gen/B0..B3`, `P<Fn>`, `Gen.lean` - `scripts/gen_paths.py`: 158 block lemmas,
    the paths `<fn>_p<i>` of each function and `ok_<fn>` (a run that ends with no error took the
    success path: exact output, gas, state, logs). A branch that an earlier condition of the same
    path decides is not followed (1 such branch, in `transferFrom`), so no path theorem has
    conditions that contradict each other.
  - `ShibVerify/Shib/Gen/Loops.lean` - `scripts/gen_loops.py`: `ro_name`, `ro_symbol`.
  - `ShibVerify/Shib/Invariant.lean` - `scripts/gen_supply.py`: `supply_<fn>`, `supply_preserved`.
  - `ShibVerify/Shib/Readable.lean` - `scripts/gen_readable.py`.
  - `ShibVerify/Shib/Sanity/Zero.lean` - `scripts/gen_sanity.py`.
  - `ShibVerify/Test/Axioms.lean` - `scripts/gen_axioms.py`: the axioms of 122 theorems.

## Rebuild

`bash scripts/regen.sh config/shib.json` (runs the seven generators in order), then `lake build`
(on the build box: `bash scripts/build_box.sh shib`) and `bash scripts/check_axioms.sh <build log>`.

## Not proved

- The bytes returned by `name()` and `symbol()`.
- `Sep` is an assumption about keccak256.
- The invariant is kept, not established: the constructor and the first state are not verified.
- Completeness is about runs that end with no error; there is no theorem that every failing run
  is one of the proved revert paths.
- The two-counter gas meter of EIP-8037.

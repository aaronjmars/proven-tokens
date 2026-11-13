# proven-tokens

**Math proofs, checked by a computer, that 15 of the biggest Ethereum tokens do what they promise.** Together they are worth about **$54 billion** on Ethereum (market cap; for BNB and USDD, only the part on Ethereum).

Most token audits are people reading the source code and running tests. That finds many bugs, but it only checks the cases someone thought of, and it checks the source, not the program that actually runs on chain. This repo does something stronger: for each token it takes the exact bytecode deployed on Ethereum and proves facts about it in [Lean 4](https://lean-lang.org), a proof checker. A proof covers every possible input, every caller and every order of calls, and the computer refuses it if a single step is wrong.

What that buys:

- **No hidden money printer.** For each token, balances always add up to the total supply, or supply can only grow the way the rules say, whatever anyone calls.
- **Who really holds the keys.** Who can mint, freeze, blacklist or pause is read from the real code, not from the docs.
- **Real code, not source.** The proofs are about the bytes on chain, so a compiler bug or a source that does not match the deployment cannot hide.

## The tokens

Value is the market cap on CoinGecko on 2026-11-12, in US dollars. For BNB and USDD only the part on Ethereum is counted, because most of their supply lives on other chains.

| Token | What it is | Value | What was proved | Worth knowing (each backed by a theorem) |
|---|---|---|---|---|
| WBTC | Wrapped Bitcoin | $8.3B | balances always add up to supply, also when another contract calls back in | only the owner can mint; pausing does not stop mint or burn |
| WBT | WhiteBIT exchange coin | $8.2B | the total supply can never grow | the owner can blacklist any address with no log, then wipe its balance with no Transfer event |
| LINK | Chainlink | $7.7B | supply is fixed at 1 billion and stays consistent, also when a receiver calls back in | a failed receiver undoes the whole transfer |
| USDE | Ethena USDe stablecoin | $4.9B | balances always add up to supply | only the minter can mint; only the owner can change the minter; ownership cannot be renounced |
| DAI | Maker / Sky stablecoin | $4.5B | balances always add up to supply | only a ward (admin) can mint, and wards add or remove other wards |
| WETH | Wrapped ether | $4.3B | it always holds enough ether to pay back every holder | |
| UNI | Uniswap | $3.7B | balances always add up to supply | a mint adds at most 2 percent, then the next one waits 365 days |
| SHIB | Shiba Inu | $2.6B | balances always add up to supply | |
| QNT | Quant | $2.4B | the total supply and the crowdsale address never change | |
| PEPE | Pepe | $1.9B | balances always add up to supply | the owner sets trading limits freely and can block all burns; a blacklisted spender can still move other people's tokens |
| ENA | Ethena | $1.9B | balances always add up to supply; mint rules | one mint per 365 days, at most 10 percent; ownership cannot be renounced |
| ONDO | Ondo Finance | $1.7B | balances always add up to supply; vesting locks hold | only minter-role holders can mint; a mint gives no votes; locked tokens cannot be sent |
| SKY | Sky (ex-Maker) | $1.4B | balances always add up to supply | only a ward can mint |
| BNB | BNB on Ethereum | $0.26B | balances plus frozen balances equal supply | |
| USDD | USDD stablecoin on Ethereum | $0.15B | balances always add up to supply | only a ward can mint |

The full list of what the proofs show about each contract is in [`FINDINGS.md`](FINDINGS.md). It lists only findings backed by a checked theorem.

## What was found

- **Every token keeps its main rule**, under the named assumptions below. For 12 tokens it is "balances add up to the total supply" (for BNB, frozen balances included); for WETH, "enough ether to pay every holder"; for WBT, "supply never grows"; for QNT, "supply never changes" (its balances add up only as long as the crowdsale address does not call the token). For LINK the result is proved per call, including calls back into the token.
- **Owner powers are real and sometimes quiet.** WBT's owner can freeze and wipe an address without the Transfer event most trackers watch. PEPE's owner can block all burns. In ENA and USDE, renouncing ownership always fails.
- **Small rule gaps.** In PEPE and WBT, the blacklist is not checked for the spender in `transferFrom`. In ONDO, while transfers are off, the permission checked is the spender's, not the holder's. ONDO's mint creates tokens that carry no votes.

## What it does not prove

Every proof rests on named assumptions, listed in each token's `token-kit/tokens/<token>/status.json`. The main ones: a short list of facts about Ethereum's hash function (keccak) is assumed, not proved; results hold from the Dencun fork to before Glamsterdam; contract creation is not covered; and the proofs say what the code allows, not who holds each role today. See [What could be done next](#what-could-be-done-next).

Adapted from the USDT proof [usdt-verify](https://github.com/Giulio2002/usdt-verify) by Giulio Rebuffo, on top of [EthLib](https://github.com/ethereum/EthLib)'s model of the Ethereum virtual machine. Bytecode from block 26386793. See [Sources and credits](#sources-and-credits).

## Technical status

15 tokens proved, 7,024 theorems in total. Every build ended with exit code 0 and uses only the three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no added axiom.

All 15 were built from scratch on 2026-11-12 UTC (pinned usdt-verify and EthLib, Lean v4.35.0): each ended with exit 0, a matching theorem count and standard axioms only. UNI and ONDO each need most of an 8 GB machine. Logs are in `logs/`: `<t>.log` (build) and `<t>.axioms` (axioms check) per token, plus `kit.log` for the shared library.

What the proofs show about each contract, limited to findings backed by a checked theorem: `FINDINGS.md` (evidence per item in `findings-verified.json`).

"Theorems" is the count checked by `token-kit/scripts/check_axioms.sh` (the list in each token's `Test/Axioms.lean`).

| Token | Theorems | Main result | Status record | Clean rebuild 2026-11-12 |
|---|---|---|---|---|
| SHIB | 139 | supply invariant for every function | `token-kit/tokens/shib/status.json` | pass |
| QNT | 157 | only the crowdsale address can mint | `token-kit/tokens/qnt/status.json` | pass |
| BNB | 176 | balances + frozen = total supply | `token-kit/tokens/bnb/status.json` | pass |
| WETH | 180 | solvency: balances never exceed ether held | `token-kit/tokens/weth/status.json` | pass |
| PEPE | 351 | supply invariant after any list of transactions | `token-kit/tokens/pepe/status.json` | pass |
| WBT | 311 | total supply never grows | `token-kit/tokens/wbt/status.json` | pass |
| USDD | 333 | supply invariant, with permit | `token-kit/tokens/usdd/status.json` | pass |
| DAI | 342 | supply invariant, with permit | `token-kit/tokens/dai/status.json` | pass |
| USDE | 424 | supply invariant, OpenZeppelin permit | `token-kit/tokens/usde/status.json` | pass |
| ENA | 445 | mint rules, with permit | `token-kit/tokens/ena/status.json` | pass |
| SKY | 453 | supply invariant over any transaction, both permits (bytes form: signatures of any length) | `token-kit/tokens/sky/status.json` | pass |
| LINK | 250 | transferAndCall with reentrancy, run-local keccak form | `token-kit/tokens/link/status.json` | pass |
| WBTC | 399 | reclaimToken with reentry, local callee assumption | `token-kit/tokens/wbtc/status.json` | pass |
| UNI | 862 | supply invariant for every selector | `token-kit/tokens/uni/status.json` | pass |
| ONDO | 2,202 | supply invariant for all 42 functions over any transaction, vesting rule in plain words | `token-kit/tokens/ondo/status.json` | pass |

CRO, GRAM and LEO also have bytecode prepared in `survey/tokens/` but are not planned.

### What is verified

- **The bytecode is the real one.** The code in every token's Lean files equals the bytecode on chain at block 26386793, byte for byte (`python3 -I audits/check_code.py`, no Lean needed), and every function selector is covered.
- **No shortcuts.** No `sorry`, no `native_decide`, no added axiom; only Lean's three standard axioms.
- **Every function.** Each token's main result covers all its functions. For 13 tokens it also covers any caller, including calls from inside another contract at any depth (see the next point); LINK and WBTC cover calls back into the token with their own proofs.
- **Whole transactions.** For 13 tokens the main result holds over any list of whole transactions as Ethereum runs them, from the Dencun fork to before Glamsterdam (shared library `token-kit/TokenKit/Seq/`, one `Tx.lean` per token). LINK and WBTC have their own proofs for a contract that calls back into the token, shown on a real run.
- **Real runs.** Success theorems are backed by concrete runs: a real permit with a real signature for USDD, DAI, USDE, ENA, SKY and UNI; a receiver that calls back in for LINK and WBTC; transfer, transferFrom and delegate for ONDO.
- **Permit.** SKY's permit is proved for contract wallets (the owner is asked and its answer checked) and for signatures of any length.
- **ONDO vesting.** The lock rule is stated in plain words and proved for transfer and transferFrom.
- **Independently reviewed.** Every token's proof was audited by a separate reviewer. The audit and the follow-up for each token are in `audits/<t>/` (`findings.json`, `fixes.json`).

### Assumed or not covered

- A short, named list of keccak (hash) facts per token, 5 to 33 (21 for ONDO), is assumed: keccak is opaque in the model, so Lean cannot prove them. Each token's `Instance.lean` shows the assumption is exactly that list and nothing more.
- Fork range: from Dencun to before Glamsterdam; some older generated theorems keep their original range.
- Contract creation and whole blocks are not modelled. WETH assumes the sender is not WETH itself.
- Owner powers are proved per call, not over time.
- Not yet shown on a real run: ONDO delegateBySig, a vote-moving run for UNI and ONDO, name(), symbol() and version() for PEPE, WBT, USDD, USDE and ENA. PEPE has no single "nobody else can mint" theorem.

## What could be done next

The proofs are done for 15 tokens, but some limits remain. In short:

- **Remove the hash assumption.** The named keccak facts are assumed, not proved. A kernel-checkable keccak would turn them into checked facts.
- **Finish the open witnesses.** ONDO delegateBySig, vote-moving runs for UNI and ONDO, name() and symbol() runs for five tokens.
- **Prove owner powers over time.** Results like "only the minter can mint" hold per call; lifting them to any list of transactions makes rules like "at most 10 percent per year" real theorems.
- **Turn the 32 dropped findings into theorems** (`findings-verified.json`, `dropped`).
- **Cover more:** LINK and WBTC in whole-transaction form, constructors, newer forks, upgradeable tokens like USDC, and more tokens.
- **Easier to run:** shared pieces into the kit, a scheduled CI rebuild, faster builds for UNI and ONDO.

The full list, with where to start for each item, is in `NEXT.md`.

## Layout

```
token-kit/        the proofs (the only folder the build needs)
  TokenKit/         shared Lean library: EVM lemmas and tactics (Evm/), transaction-level invariant (Seq/)
  scripts/          one generator set for every token (gen_*.py, regen.sh, check_axioms.sh, build_box.sh)
  tokens/<t>/       one Lean package per token: config, bytecode, generated + hand-written proofs, docs/MAP.md
  statement-dumps/  before/after statement diffs from the merge into the kit
  kit-status.json   kit record: layout, merges, how to add a token
survey/           which tokens to do
  tokens.json       survey of the top 45 Ethereum tokens (proxy, compiler, size); scan_tokens.py makes it
  tokens/<SYM>/     runtime bytecode, source record, ABI and selector map for 18 tokens; prep_tokens.py makes them
audits/           one folder per token
  <t>/              findings.json (what the audit found) and fixes.json (what was fixed, what is still open)
  check_code.py     checks the bytecode in the Lean files against survey/tokens/<SYM>/runtime.hex
logs/             latest clean build: <t>.log and <t>.axioms per token, kit.log for the library
e2b/              scripts that build on the Linux box (full_rebuild.sh runs it all from the Mac and writes logs/)
```

Some Lean comments are dated records and were not rewritten, so they may still name a folder of an earlier layout (for example a `work/` file or a `*-verify/` project). The generators write their scratch output to `token-kit/tokens/<t>/work/`, which is not kept.

## Sources and credits

This work is adapted from **usdt-verify** by Giulio2002, which proved properties of the deployed USDT bytecode in Lean. The method here (model the bytecode in Lean, generate one theorem per code path, then prove invariants on top) comes from that project and is extended to 15 more tokens.

- **usdt-verify** (the USDT proof this is adapted from): https://github.com/Giulio2002/usdt-verify, used at commit `d0e684c5f20461b5816fa0a806e3888500535a51`. `token-kit` imports its general EVM lemmas (`UsdtVerify/Evm`). License: MIT, granted by the author on X on 2026-11-12 (https://x.com/GiulioRebuffo/status/2120921295252803990); the MIT LICENSE file landed in that repo on the same day (commit `e8ac085c7a5f`, after the pinned one). EthLib is CC0.
- **EthLib** (the EVM model in Lean that every proof runs against): https://github.com/ethereum/EthLib, at commit `62dbd687dfa0a10641cf24e35c2572d3039bad55` (the commit usdt-verify pins).
- **Lean 4** (the proof language and checker): https://lean-lang.org, toolchain `leanprover/lean4:v4.35.0`.
- **Mathlib** (the Lean math library, pulled in through EthLib): https://github.com/leanprover-community/mathlib4.
- **Token bytecode and verified sources**: read from Ethereum mainnet at block 26386793 and from Etherscan (`survey/scan_tokens.py`, `survey/prep_tokens.py`); each token's record is in `survey/tokens/<SYM>/SOURCE.md`.

usdt-verify, EthLib and Mathlib are not copied into this repo; fetch them at the commits above.

## Build

Lean runs on a Linux box (E2B), not on the Mac.

1. Build the base once: `e2b/build_template.py`, then `e2b/remote_build.sh` on the box. It fetches and builds usdt-verify with EthLib and Mathlib (about 9 minutes, 2.4 GB RAM peak).
2. Build tokens: `bash token-kit/scripts/build_box.sh <t> [<t> ...]`. It copies the kit to `/home/user/token-kit`, which must sit next to the built `/home/user/usdt-verify`, runs `lake build` for the library and each token, then the axioms check.
3. Full clean rebuild of everything: `e2b/verify_all.sh` on the box. One token: `e2b/verify_one.sh <t>`. Most tokens take 2 to 6 minutes. UNI takes about 40 minutes and its biggest files need close to 3 GB RAM each, so the scripts build it with 2 workers (`LEAN_NUM_THREADS=2`). ONDO takes about 25 minutes; its five biggest files are built alone first.

Do not move files inside `token-kit/`: the lakefiles use relative paths (`../usdt-verify`, `../..`).

## Add a token

Short version; the full steps are in `token-kit/kit-status.json` under `how_to_run_for_a_new_token`.

1. Add the token to the survey and run `survey/prep_tokens.py` to get its bytecode and selector map.
2. Make `token-kit/tokens/<t>/` with `config/<t>.json` (copy the closest existing token) and `data/<t>.runtime.hex`.
3. In that folder run `bash ../../scripts/regen.sh config/<t>.json` to generate the Lean files.
4. Write the token-specific files by hand (separation, sequences, a sanity witness, any function that calls out).
5. Build on the box with `build_box.sh <t>`. Lemmas that are not about the token go into `TokenKit/Evm/`, then rebuild every token.

## License

MIT, see `LICENSE`. Parts are adapted from [usdt-verify](https://github.com/Giulio2002/usdt-verify) by Giulio Rebuffo (MIT). EthLib is CC0.

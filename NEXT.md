# What could be done next

Open work, roughly in order of value. Each item names where to start. Contributions are welcome.

## Close the gaps that are left

1. **Prove the hash facts.** Every token assumes a short, named list of keccak facts (5 to 33 per token, 21 for ONDO), because keccak is opaque in EthLib's model. A keccak function the Lean kernel can evaluate, shown equal to the model's one, would turn each fact into a checked computation and remove the biggest assumption in the repo. Start: each token's `Instance.lean` (`KeyFacts`) and `status.json` (`assumptions`).
2. **ONDO: a worked delegateBySig run.** Needs a real signature and a port of UNI's ECRECOVER run rule (`token-kit/tokens/uni/`) to ONDO.
3. **Vote-moving runs for UNI and ONDO.** The worked examples move no votes, so the checkpoint paths have no concrete witness yet.
4. **LINK and WBTC: whole-transaction form.** They keep their own reentrancy proofs and have no `Tx.lean`. Port them to the shared `token-kit/TokenKit/Seq/` like the 13 other tokens.
5. **PEPE: one "nobody else can mint" theorem.** Today it follows from reading 32 success paths; one theorem needs a change in `token-kit/scripts/gen_nomint.py`.
6. **Worked examples for name(), symbol(), version()** on PEPE, WBT, USDD, USDE and ENA, and the ERC-1271 permit and permit(bytes) runs for SKY.
7. **WETH: drop the "sender is not WETH" assumption**, and cover EIP-7702 delegated callers for WETH withdraw and the BNB owner.

## Make the claims stronger

8. **Owner powers over time, not per call.** Findings like "only the minter can mint" or "ENA mints at most once a year" are proved for one call at a time. Lift them to any list of transactions with the same `Seq` library, so "at most 10 percent per year" becomes a theorem, not an inference.
9. **The 32 findings without a theorem.** `findings-verified.json` lists them under `dropped` (for example "ONDO has no burn", "UNI mint moves votes"). Each is a small, well-defined theorem to add.
10. **One shared ERC-20 spec.** Each token states its own invariant. A single Lean spec of ERC-20 behaviour (transfer, approve, allowance rules) proved for each token would make tokens comparable side by side.
11. **Newer forks.** Most results hold from Dencun to before Glamsterdam, and older generated theorems keep their original fork range. Re-check on each new fork as EthLib adds it.
12. **Constructors and whole blocks** are not modelled for any token.

## Cover more contracts

13. **Upgradeable tokens.** USDC and many others sit behind a proxy. A proof would need to state what the proxy and its admin can change.
14. **More tokens.** CRO, GRAM and LEO have bytecode in `survey/tokens/` but no proof yet. `README.md` (Add a token) and `token-kit/kit-status.json` (`how_to_run_for_a_new_token`) give the steps.
15. **Live state.** The proofs say what the code allows; they do not read who holds each role today. A small script that reads the current owner, minters and wards on chain would make each finding concrete.

## Make it easier to use

16. **Move shared pieces into the kit.** Several tokens carry their own copy of the same generic file (ECRECOVER rule, finite-key Sep generator, ONDO's dead-branch table, `Arith.lean`). Each `status.json` lists them under `to_merge_into_kit`. Rebuild every token after.
17. **CI.** Builds run on an 8 vCPU, 8 GB Linux box (`e2b/`); UNI and ONDO need most of that memory. A scheduled rebuild on a large CI runner would show that every result still checks.
18. **Faster builds.** ONDO and UNI take 25 to 40 minutes. Splitting the largest generated files would cut memory and time.

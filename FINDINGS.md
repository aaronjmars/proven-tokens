# What the proofs show about 15 token contracts

Only findings backed by a checked Lean theorem are listed; each line ends with the theorem name.
The source of truth, with the full theorem statements and every dropped item, is `findings-verified.json`.

How to read it: "per call" means the theorem is about one call to the contract. "Succeeds only if" means the theorem lists what a successful call needs; it does not show that nothing else is checked. Many results also rest on named hash (keccak) assumptions that are stated but not proved; the JSON file gives them for each line.

## SHIB

- If the balances add up to the total supply, they still do after any list of whole transactions, whoever calls and however deep, under the named assumptions. `supply_any_transactions`

## QNT

- After any list of transactions, the total supply and the crowdsale address never change, and the balances never add up to less than before. `fixed_mono_any_transactions`
- Balances keep adding up to the total supply as long as the crowdsale address does not call the token. `inv_any_transactions_no_crowdsale`

## BNB

- If balances plus frozen balances equal the total supply, they still do after any list of whole transactions, withdrawEther included. `supply_any_transactions`

## WETH

- If WETH holds at least as much ether as all balances together, it still does after any list of whole transactions whose sender is not WETH itself. `solvent_any_transactions`

## PEPE

- Any call that sends ether fails. `ok_valueSent`
- A transfer succeeds only if neither the sender nor the receiver is blacklisted (per call). `transfer_readable`
- Before trading opens (no pair set), a transfer succeeds only if the sender or the receiver is the owner (per call). `transfer_readable`
- On a buy from the pair while limits are on, the buyer's new balance must sit inside the holding limits (per call). `transfer_readable`
- transferFrom can succeed without any check on the blacklist status of the spender who calls it (per call). `transferFrom_p19`
- A burn fails whenever address 0 is blacklisted, so the owner can block all burns (per call). `burn_readable`
- Only the owner can call setRule, and the owner can set any limits and any pair, 0 included (per call). `setRule_readable`, `setRule_p6`
- A burn lowers the total supply and the caller's balance by the same amount (per call). `burn_readable`

## WBT

- No call of any function makes the total supply larger (per call). `total_le`
- Over any list of transactions, the total supply never grows. `supply_never_grows_any_transactions`
- destroyBlackFunds is owner only, works on blacklisted addresses only, zeroes their balance, lowers the supply and emits no Transfer event (per call). `destroyBlackFunds_readable`
- blacklistAccount is owner only and leaves no log (per call). `blacklistAccount_readable`
- Pause stops transfer and transferFrom, but burn, destroyBlackFunds, approve and the ownership functions still work while paused (per call). `transfer_readable`, `burn_p7`, `destroyBlackFunds_p7`, `approve_p6`, `transferOwnership_p7`
- transferFrom can succeed for a spender who is blacklisted (per call). `transferFrom_p13`
- isOwner(a) checks its argument, not the caller (per call). `isOwner_readable`

## USDD

- Only a ward can mint, and a mint adds the same amount to the balance and the total supply (per call). `mint_readable`
- Burning needs no ward: it needs only enough balance and, for someone else's tokens, enough allowance (per call). `burn_readable`
- An allowance set to the largest value is never lowered by transferFrom, move or pull (per call). `transferFrom_readable`, `move_readable`, `pull_readable`
- Any call that sends ether fails. `ok_valueSent`

## DAI

- Only a ward can mint, and a mint adds the same amount to the balance and the total supply (per call). `mint_readable`
- Burning needs no ward: it needs only enough balance and, for someone else's tokens, enough allowance (per call). `burn_readable`
- An allowance set to the largest value is never lowered by transferFrom, move or pull (per call). `transferFrom_readable`, `move_readable`, `pull_readable`
- rely and deny are ward only and each writes one anonymous note log (per call). `rely_readable`, `deny_readable`

## USDE

- Only the minter address can mint, and a mint raises the total supply by exactly the amount (per call). `mint_readable`
- Only the owner can change the minter (per call). `setMinter_readable`
- Ownership moves in two steps: the owner names a pending owner, who must then accept (per call). `transferOwnership_readable`, `acceptOwnership_readable`
- renounceOwnership always fails. `renounceOwnership_never`
- In permit, the nonce is already raised when the signature is checked (per call). `ok_permit_real`

## ENA

- Only the owner can mint (per call). `mint_readable`
- A mint needs at least 365 days since the last mint and can add at most 10 percent of the total supply (per call). `mint_readable`
- Every successful mint, of any amount, restarts the 365 day wait (per call). `mint_readable`
- renounceOwnership always fails, so the owner can never be removed that way. `renounceOwnership_never`
- Transfers move the exact amount, with no fee (per call). `transfer_readable`

## SKY

- Only a ward can mint (per call). `mint_readable`
- Burning needs no ward: a real burn by a non-ward was run and succeeded. `burn_p6_runs`
- Transfers to address 0 or to the token itself fail (per call). `transfer_readable`
- In permit, the nonce is raised before the signature check, and a call to a contract wallet owner is read-only with no ether (per call). `ok_permit_full`
- Any call that sends ether fails. `ok_valueSent`

## LINK

- totalSupply() always returns the fixed number 10^27 (per call). `ok_totalSupply`
- No call, including one where the receiver calls back into the token, changes the sum of the balances, under the named assumptions (per call). `supply_all_real_local`
- transferAndCall writes both balances and both Transfer logs before it calls the receiver (per call). `tac_at_call`, `tacDoneSs_eq`
- If the receiver fails, the whole transferAndCall is undone (per call; also shown on a real run). `tac_after_fail`, `transferAndCall_reverts`
- A real run with a receiver that calls back into the token succeeds and keeps the supply. `reenter_closed`
- increaseApproval and decreaseApproval accept spender 0 or the token itself (per call). `increaseApproval_p3`, `decreaseApproval_p2`
- Any call that sends ether fails (per call). `value_zero_of_ok`

## WBTC

- In reclaimToken, the owner who gets paid is read again after the first outside call, so that call can change who is paid (per call). `reclaimToken_readable`
- If the outside token returns false on transfer, reclaimToken is undone (shown on a real run). `reclaimToken_falseReturn_reverts`
- Only the owner can mint, and only while minting is not finished (per call). `mint_only_owner`
- Pause does not stop mint or burn: both were run on a paused token and succeeded. `mint_paused_runs`, `burn_paused_runs`
- While paused, transfer, transferFrom, approve, increaseApproval and decreaseApproval always fail. `paused_blocks`
- renounceOwnership always fails. `renounceOwnership_fails`
- transferFrom always lowers the allowance, even the largest one, and emits no Approval event (per call). `transferFrom_readable`
- finishMinting returns false and changes nothing (per call). `finishMinting_does_nothing`

## UNI

- A mint can add at most 2 percent of the total supply (per call). `mint_readable`
- After a mint, the next one is allowed only 365 days later (per call). `mint_readable`
- In permit, the signed message uses the old nonce, and the nonce is raised by the time the signature is checked (per call). `ok_permit_real`
- Approving the largest number stores the largest 96-bit allowance (per call). `approve_readable`

## ONDO

- Only holders of the minter role can mint, and a mint adds the same amount to the balance and the total supply (per call). `mint_readable`, `mint_amounts`
- A mint moves no votes: the receiver's balance grows but no vote checkpoint changes (per call). `mint_votes_gap`
- While transfers are not enabled, only holders of the transfer role can send tokens (per call). `transfer_readable`
- A locked holder can only send what is above the locked amount at that time (per call). `transfer_vesting`
- An address that already has a lock cannot be given a new one (per call). `ok_updateTrancheBalance`
- The admin can set the cliff date to any value (per call). `updateCliffTimestamp_readable`

## Gaps the audits found in the proofs

The audits found 14 serious gaps (2 critical, 12 major). All were confirmed. 11 are closed and 3 are partly closed.

- BNB-1 (critical): the withdrawEther result relied on an assumption shown to be false. Closed: replaced by a result proved for the real EVM runner. `Withdraw.processRunner_keepsInv`
- BNB-2 (major): the supply result left out withdrawEther and assumed outside steps leave the token alone. Closed. `supply_any_transactions`
- BNB-3 (major): withdrawEther had no full successful run. Partly closed: a real run now exists, but there is still no run with amount 0, and the owner is still assumed not to be a delegated (EIP-7702) account. `withdrawEther_pays_closed`
- WETH-1 (major): safety during withdraw to a contract was assumed, not proved. Closed: proved for any receiver code. `solvent_preserved_process`
- WETH-3 (major): withdraw needed many side assumptions. Partly closed: a withdraw from a delegated (EIP-7702) caller is still excluded. `ok_withdraw_all`
- LINK-1 (critical): the reentrancy and sequence results rested on a hash assumption that is almost surely false. Closed: restated on narrow, per-run hash conditions. `supply_all_real_local`
- LINK-2 (major): contract creation was not covered. Partly closed: creation is now covered, but LINK still has no result over whole transactions (fees, refunds and EIP-7702 steps are assumed). `create_good_local`
- SKY-1 (major): the contract-wallet permit result did not say the owner was really asked. Closed. `ok_permit_full`
- SKY-2 (major): permit with a bytes signature was proved for 65-byte signatures only. Closed: any length. `ok_permitBytes_full`
- DAI-1, USDD-1, UNI-1, WBT-1, ONDO-1 (major): the "any sequence of calls" results covered direct calls only. Closed: each now holds over any list of whole transactions. `supply_any_transactions` (WBT also `supply_never_grows_any_transactions`)

Still true for every token after the fixes: the named hash facts are assumed, not proved, and constructors and whole blocks are not modelled.

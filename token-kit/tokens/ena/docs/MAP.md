# Map of the ENA runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 64 | 0xdd62ed3e | allowance(address,address) | view | 947 (0x03b3) |
| 75 | 0xe30c3978 | pendingOwner() | view | 1016 (0x03f8) |
| 86 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1046 (0x0416) |
| 97 | 0xfdb04bbf | MAX_INFLATION() | view | 1065 (0x0429) |
| 112 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 890 (0x037a) |
| 123 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 909 (0x038d) |
| 134 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 928 (0x03a0) |
| 160 | 0x8da5cb5b | owner() | view | 781 (0x030d) |
| 171 | 0x8e80ff5d | lastMintTimestamp() | view | 843 (0x034b) |
| 182 | 0x95d89b41 | symbol() | view | 882 (0x0372) |
| 197 | 0x79cc6790 | burnFrom(address,uint256) | nonpayable | 716 (0x02cc) |
| 208 | 0x7ecebe00 | nonces(address) | view | 735 (0x02df) |
| 219 | 0x84b0196e | eip712Domain() | view | 754 (0x02f2) |
| 256 | 0x42966c68 | burn(uint256) | nonpayable | 628 (0x0274) |
| 267 | 0x70a08231 | balanceOf(address) | view | 647 (0x0287) |
| 278 | 0x715018a6 | renounceOwnership() | view | 700 (0x02bc) |
| 289 | 0x79ba5097 | acceptOwnership() | nonpayable | 708 (0x02c4) |
| 304 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 580 (0x0244) |
| 315 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 588 (0x024c) |
| 326 | 0x40c10f19 | mint(address,uint256) | nonpayable | 607 (0x025f) |
| 352 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 508 (0x01fc) |
| 363 | 0x313ce567 | decimals() | view | 527 (0x020f) |
| 374 | 0x3544fd2b | MINT_WAIT_PERIOD() | view | 548 (0x0224) |
| 389 | 0x06fdde03 | name() | view | 425 (0x01a9) |
| 400 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 455 (0x01c7) |
| 411 | 0x18160ddd | totalSupply() | view | 490 (0x01ea) |

Instructions: 3250; opcode counts: {"CHAINID": 3, "EQ": 36, "INVALID": 1, "JUMP": 164, "JUMPDEST": 209, "JUMPI": 89, "LOG2": 1, "LOG3": 5, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 27, "SHA3": 24, "SHR": 2, "SLOAD": 35, "SSTORE": 12, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 3}.

## Limits of the proofs (the ten-token audit)

Written by hand in the fix round of the ten-token audit (the table above is generated). Full detail: `status.json`
(`fork_range`, `closed_instance`, `permit.witness`, `claims`).

- Fork: every claim is for Shapella <= fork < Glamsterdam (transactions: Dencun <= fork < Glamsterdam).
  The proofs use the one-counter gas meter, which EthLib runs only before Glamsterdam. The older
  generated theorems state only the lower bound (Shapella); read them with fork < Glamsterdam.
- Keccak: the invariant and readable theorems of the writers hold under `Sep (callKeys message)`, a
  hypothesis on keccak that is NOT proved. No instance of `supply_*` with every hypothesis proved is
  machine-checked: each open fact of `Sep` is a statement over 2^160 values of keccak. `Sep` fails only
  on a keccak collision or preimage (about 2^-96 per fact under the random-function view; a heuristic).
- What is machine-checked instead (`Instance.lean`): for the state with all-zero storage and the call
  `allowance(K, K)`, the start invariant holds (`inv_start`) and `Sep` is exactly the 7 named facts of
  `KeyFacts` (`sep_iff`); `supply_m0` and `supply_permit_m1` need only the fork range and `KeyFacts`.
- `Sep` says nothing about an allowance slot or a nonce slot being slot 0, 1 or 11. A reading such as
  "approve or permit never changes the owner word" needs one more keccak fact per call, not proved in
  general (computed by the kernel for the keys of the instance: `Instance.slots_not_fixed`).
- permit: `Instance.permit_runs` (`PermitRun.lean`) is one real successful run under EthLib's real
  runner, with a real signature that the kernel checks with EthLib's own ECRECOVER. It covers
  the branch of the cached domain separator (chain id 1, the deployed address); the other success ways have no witness.
- `NoDelegation1` (permit, from Pectra): proved for every state where address 1 has the empty code hash
  (`noDelegation1_of_emptyHash`); not shown to be kept by a run.
- The mint rules (only the owner, 365 days since the last mint, at most 10 percent of the supply) are
  proved PER CALL (`mint_readable`). "At most 10 percent per 365 days" over time is an inference, not
  a Lean theorem: there is no sequence theorem about slot 11.
- Every rule about who can do what is PER CALL and about the bytes. Nothing here reads the live chain
  state (who holds a role today).

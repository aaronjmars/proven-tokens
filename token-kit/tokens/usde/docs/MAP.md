# Map of the USDE runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 66 | 0xdd62ed3e | allowance(address,address) | view | 907 (0x038b) |
| 77 | 0xe30c3978 | pendingOwner() | view | 977 (0x03d1) |
| 88 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1007 (0x03ef) |
| 99 | 0xfca3b5aa | setMinter(address) | nonpayable | 1026 (0x0402) |
| 115 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 850 (0x0352) |
| 126 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 869 (0x0365) |
| 137 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 888 (0x0378) |
| 164 | 0x84b0196e | eip712Domain() | view | 785 (0x0311) |
| 175 | 0x8da5cb5b | owner() | view | 812 (0x032c) |
| 186 | 0x95d89b41 | symbol() | view | 842 (0x034a) |
| 202 | 0x79ba5097 | acceptOwnership() | nonpayable | 739 (0x02e3) |
| 213 | 0x79cc6790 | burnFrom(address,uint256) | nonpayable | 747 (0x02eb) |
| 224 | 0x7ecebe00 | nonces(address) | view | 766 (0x02fe) |
| 262 | 0x42966c68 | burn(uint256) | nonpayable | 658 (0x0292) |
| 273 | 0x70a08231 | balanceOf(address) | view | 677 (0x02a5) |
| 284 | 0x715018a6 | renounceOwnership() | view | 731 (0x02db) |
| 300 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 610 (0x0262) |
| 311 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 618 (0x026a) |
| 322 | 0x40c10f19 | mint(address,uint256) | nonpayable | 637 (0x027d) |
| 349 | 0x18160ddd | totalSupply() | view | 558 (0x022e) |
| 360 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 576 (0x0240) |
| 371 | 0x313ce567 | decimals() | view | 595 (0x0253) |
| 387 | 0x06fdde03 | name() | view | 424 (0x01a8) |
| 398 | 0x07546172 | minter() | view | 454 (0x01c6) |
| 409 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 523 (0x020b) |

Instructions: 3107; opcode counts: {"CHAINID": 3, "EQ": 35, "INVALID": 1, "JUMP": 154, "JUMPDEST": 195, "JUMPI": 84, "LOG3": 6, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 25, "SHA3": 24, "SHR": 2, "SLOAD": 35, "SSTORE": 12, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 1}.

## Limits of the proofs (the ten-token audit)

Written by hand in the fix round of the ten-token audit (the table above is generated). Full detail: `status.json`
(`fork_range`, `closed_instance`, `permit.witness`, `claims`).

- Fork: every claim is for Paris <= fork < Glamsterdam (transactions: Dencun <= fork < Glamsterdam).
  The proofs use the one-counter gas meter, which EthLib runs only before Glamsterdam. The older
  generated theorems state only the lower bound (Berlin); read them with fork < Glamsterdam.
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
- "Only the minter can mint" is proved PER CALL (`ok_mint`, `mint_readable`): a successful mint was
  sent by the address in slot 11 at that call. The owner can change slot 11 at any time (`setMinter`),
  and no single theorem says that nothing else raises the total supply.
- Every rule about who can do what is PER CALL and about the bytes. Nothing here reads the live chain
  state (who holds a role today).

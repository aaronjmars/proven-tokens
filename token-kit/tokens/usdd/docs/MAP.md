# Map of the USDD runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 990 (0x03de) |
| 66 | 0xb753a98c | push(address,uint256) | nonpayable | 1034 (0x040a) |
| 77 | 0xbb35783b | move(address,address,uint256) | nonpayable | 1078 (0x0436) |
| 88 | 0xbf353dbb | wards(address) | view | 1132 (0x046c) |
| 99 | 0xdd62ed3e | allowance(address,address) | view | 1170 (0x0492) |
| 110 | 0xf2d5d56b | pull(address,uint256) | nonpayable | 1216 (0x04c0) |
| 126 | 0x7ecebe00 | nonces(address) | view | 772 (0x0304) |
| 137 | 0x8fcbaf0c | permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32) | nonpayable | 810 (0x032a) |
| 148 | 0x95d89b41 | symbol() | view | 900 (0x0384) |
| 159 | 0x9c52a7f1 | deny(address) | nonpayable | 908 (0x038c) |
| 170 | 0x9dc29fac | burn(address,uint256) | nonpayable | 946 (0x03b2) |
| 197 | 0x313ce567 | decimals() | view | 604 (0x025c) |
| 208 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 634 (0x027a) |
| 219 | 0x40c10f19 | mint(address,uint256) | nonpayable | 642 (0x0282) |
| 230 | 0x54fd4d50 | version() | view | 688 (0x02b0) |
| 241 | 0x65fae35e | rely(address) | nonpayable | 696 (0x02b8) |
| 252 | 0x70a08231 | balanceOf(address) | view | 734 (0x02de) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 452 (0x01c4) |
| 290 | 0x18160ddd | totalSupply() | view | 516 (0x0204) |
| 301 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 542 (0x021e) |
| 312 | 0x30adf81f | PERMIT_TYPEHASH() | view | 596 (0x0254) |

Instructions: 2598; opcode counts: {"EQ": 31, "INVALID": 1, "JUMP": 60, "JUMPDEST": 105, "JUMPI": 64, "LOG3": 5, "RETURN": 4, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 31, "SHA3": 43, "SHL": 68, "SHR": 1, "SLOAD": 25, "SSTORE": 13, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 1}.

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
  `allowance(K, K)`, the start invariant holds (`inv_start`) and `Sep` is exactly the 5 named facts of
  `KeyFacts` (`sep_iff`); `supply_m0` and `supply_permit_m1` need only the fork range and `KeyFacts`.
- permit: `Instance.permit_runs` (`PermitRun.lean`) is one real successful run under EthLib's real
  runner, with a real signature that the kernel checks with EthLib's own ECRECOVER. It covers
  one of its 4 success ways (allowed != 0, expiry == 0); the other success ways have no witness.
- `NoDelegation1` (permit, from Pectra): proved for every state where address 1 has the empty code hash
  (`noDelegation1_of_emptyHash`); not shown to be kept by a run.
- Every rule about who can do what is PER CALL and about the bytes. Nothing here reads the live chain
  state (who holds a role today).

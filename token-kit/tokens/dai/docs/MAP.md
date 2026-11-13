# Map of the DAI runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1716 (0x06b4) |
| 66 | 0xb753a98c | push(address,uint256) | nonpayable | 1818 (0x071a) |
| 77 | 0xbb35783b | move(address,address,uint256) | nonpayable | 1896 (0x0768) |
| 88 | 0xbf353dbb | wards(address) | view | 2006 (0x07d6) |
| 99 | 0xdd62ed3e | allowance(address,address) | view | 2094 (0x082e) |
| 110 | 0xf2d5d56b | pull(address,uint256) | nonpayable | 2214 (0x08a6) |
| 126 | 0x7ecebe00 | nonces(address) | view | 1185 (0x04a1) |
| 137 | 0x8fcbaf0c | permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32) | nonpayable | 1273 (0x04f9) |
| 148 | 0x95d89b41 | symbol() | view | 1439 (0x059f) |
| 159 | 0x9c52a7f1 | deny(address) | nonpayable | 1570 (0x0622) |
| 170 | 0x9dc29fac | burn(address,uint256) | nonpayable | 1638 (0x0666) |
| 197 | 0x313ce567 | decimals() | view | 754 (0x02f2) |
| 208 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 790 (0x0316) |
| 219 | 0x40c10f19 | mint(address,uint256) | nonpayable | 820 (0x0334) |
| 230 | 0x54fd4d50 | version() | view | 898 (0x0382) |
| 241 | 0x65fae35e | rely(address) | nonpayable | 1029 (0x0405) |
| 252 | 0x70a08231 | balanceOf(address) | view | 1097 (0x0449) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 458 (0x01ca) |
| 290 | 0x18160ddd | totalSupply() | view | 560 (0x0230) |
| 301 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 590 (0x024e) |
| 312 | 0x30adf81f | PERMIT_TYPEHASH() | view | 724 (0x02d4) |

Instructions: 3488; opcode counts: {"EQ": 33, "INVALID": 1, "JUMP": 65, "JUMPDEST": 130, "JUMPI": 68, "LOG3": 5, "LOG4": 2, "RETURN": 14, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 31, "SHA3": 43, "SHL": 4, "SHR": 3, "SLOAD": 25, "SSTORE": 13, "STATICCALL": 1, "STOP": 8, "TIMESTAMP": 1}.

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

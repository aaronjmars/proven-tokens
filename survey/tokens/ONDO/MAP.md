# Map of the ONDO runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 66 | 0xe07edfdc | cliffTimestamp() | view | 1695 (0x069f) |
| 77 | 0xe09c3702 | tranche2VestingPeriod() | view | 1704 (0x06a8) |
| 88 | 0xe17ddf87 | updateTrancheBalance(address,uint256,uint8) | nonpayable | 1743 (0x06cf) |
| 99 | 0xe7a324dc | DELEGATION_TYPEHASH() | view | 1762 (0x06e2) |
| 110 | 0xf1127ed8 | checkpoints(address,uint32) | view | 1801 (0x0709) |
| 121 | 0xf1b50c1d | enableTransfer() | nonpayable | 1904 (0x0770) |
| 137 | 0xb4b5ea57 | getCurrentVotes(address) | view | 1533 (0x05fd) |
| 148 | 0xc3cda520 | delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 1552 (0x0610) |
| 159 | 0xd5391393 | MINTER_ROLE() | view | 1571 (0x0623) |
| 170 | 0xd547741f | revokeRole(bytes32,address) | nonpayable | 1610 (0x064a) |
| 181 | 0xdd62ed3e | allowance(address,address) | view | 1629 (0x065d) |
| 208 | 0x94d83076 | passedAllVestingPeriods() | view | 1424 (0x0590) |
| 219 | 0x95d89b41 | symbol() | view | 1432 (0x0598) |
| 230 | 0xa217fddf | DEFAULT_ADMIN_ROLE() | view | 1467 (0x05bb) |
| 241 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1475 (0x05c3) |
| 252 | 0xab65f09a | tranche1VestingPeriod() | view | 1494 (0x05d6) |
| 268 | 0x782d6fe1 | getPriorVotes(address,uint256) | view | 1251 (0x04e3) |
| 279 | 0x7ecebe00 | nonces(address) | view | 1294 (0x050e) |
| 290 | 0x7f58b9d3 | getVestedBalance(address) | view | 1326 (0x052e) |
| 301 | 0x91c903a6 | seedVestingPeriod() | view | 1366 (0x0556) |
| 312 | 0x91d14854 | hasRole(bytes32,address) | view | 1405 (0x057d) |
| 350 | 0x44f61ab7 | passedCliff() | view | 1029 (0x0405) |
| 361 | 0x587cde1e | delegates(address) | view | 1039 (0x040f) |
| 372 | 0x5c19a95c | delegate(address) | nonpayable | 1104 (0x0450) |
| 383 | 0x6cde20ab | getFreedBalance(address) | view | 1123 (0x0463) |
| 394 | 0x6fcfff45 | numCheckpoints(address) | view | 1142 (0x0476) |
| 405 | 0x70a08231 | balanceOf(address) | view | 1201 (0x04b1) |
| 421 | 0x2f2ff15d | grantRole(bytes32,address) | nonpayable | 933 (0x03a5) |
| 432 | 0x313ce567 | decimals() | view | 952 (0x03b8) |
| 443 | 0x34fec467 | transferAllowed() | view | 978 (0x03d2) |
| 454 | 0x36568abe | renounceRole(bytes32,address) | nonpayable | 991 (0x03df) |
| 465 | 0x40c10f19 | mint(address,uint256) | nonpayable | 1010 (0x03f2) |
| 492 | 0x18160ddd | totalSupply() | view | 792 (0x0318) |
| 503 | 0x20606b70 | DOMAIN_TYPEHASH() | view | 801 (0x0321) |
| 514 | 0x206b60f9 | TRANSFER_ROLE() | view | 840 (0x0348) |
| 525 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 879 (0x036f) |
| 536 | 0x248a9ca3 | getRoleAdmin(bytes32) | view | 898 (0x0382) |
| 552 | 0x01ffc9a7 | supportsInterface(bytes4) | view | 611 (0x0263) |
| 563 | 0x04c981ba | updateCliffTimestamp(uint256) | nonpayable | 651 (0x028b) |
| 574 | 0x06fdde03 | name() | view | 672 (0x02a0) |
| 585 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 720 (0x02d0) |
| 596 | 0x0f36554a | TIMELOCK_UPDATE_ROLE() | view | 739 (0x02e3) |

Instructions: 6411; opcode counts: {"CHAINID": 1, "EQ": 61, "INVALID": 1, "JUMP": 262, "JUMPDEST": 322, "JUMPI": 148, "LOG1": 2, "LOG2": 1, "LOG3": 4, "LOG4": 3, "NUMBER": 2, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 32, "SHA3": 78, "SHL": 186, "SHR": 1, "SLOAD": 67, "SSTORE": 17, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 6}.

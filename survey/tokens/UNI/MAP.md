# Map of the UNI runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 66 | 0xdd62ed3e | allowance(address,address) | view | 875 (0x036b) |
| 77 | 0xe7a324dc | DELEGATION_TYPEHASH() | view | 894 (0x037e) |
| 88 | 0xf1127ed8 | checkpoints(address,uint32) | view | 902 (0x0386) |
| 99 | 0xfca3b5aa | setMinter(address) | nonpayable | 935 (0x03a7) |
| 115 | 0xb4b5ea57 | getCurrentVotes(address) | view | 818 (0x0332) |
| 126 | 0xc3cda520 | delegateBySig(address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 837 (0x0345) |
| 137 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 856 (0x0358) |
| 164 | 0x782d6fe1 | getPriorVotes(address,uint256) | view | 740 (0x02e4) |
| 175 | 0x7ecebe00 | nonces(address) | view | 772 (0x0304) |
| 186 | 0x95d89b41 | symbol() | view | 791 (0x0317) |
| 197 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 799 (0x031f) |
| 213 | 0x6fcfff45 | numCheckpoints(address) | view | 694 (0x02b6) |
| 224 | 0x70a08231 | balanceOf(address) | view | 713 (0x02c9) |
| 235 | 0x76c71ca1 | mintCap() | view | 732 (0x02dc) |
| 273 | 0x40c10f19 | mint(address,uint256) | nonpayable | 614 (0x0266) |
| 284 | 0x587cde1e | delegates(address) | view | 635 (0x027b) |
| 295 | 0x5c11d62f | minimumTimeBetweenMints() | view | 654 (0x028e) |
| 306 | 0x5c19a95c | delegate(address) | nonpayable | 675 (0x02a3) |
| 322 | 0x30adf81f | PERMIT_TYPEHASH() | view | 577 (0x0241) |
| 333 | 0x30b36cef | mintingAllowedAfter() | view | 585 (0x0249) |
| 344 | 0x313ce567 | decimals() | view | 593 (0x0251) |
| 371 | 0x18160ddd | totalSupply() | view | 529 (0x0211) |
| 382 | 0x20606b70 | DOMAIN_TYPEHASH() | view | 550 (0x0226) |
| 393 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 558 (0x022e) |
| 409 | 0x06fdde03 | name() | view | 446 (0x01be) |
| 420 | 0x07546172 | minter() | view | 476 (0x01dc) |
| 431 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 497 (0x01f1) |

Instructions: 5301; opcode counts: {"CHAINID": 1, "EQ": 40, "INVALID": 3, "JUMP": 337, "JUMPDEST": 370, "JUMPI": 91, "LOG1": 1, "LOG2": 1, "LOG3": 5, "LOG4": 1, "NUMBER": 2, "RETURN": 1, "RETURNDATACOPY": 2, "RETURNDATASIZE": 4, "REVERT": 13, "SHA3": 74, "SHR": 1, "SLOAD": 49, "SSTORE": 20, "STATICCALL": 2, "STOP": 1, "TIMESTAMP": 4}.

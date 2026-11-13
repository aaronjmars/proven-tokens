# Map of the WBTC runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 53 | 0x05d2035b | mintingFinished() | view | 322 (0x0142) |
| 65 | 0x06fdde03 | name() | view | 363 (0x016b) |
| 76 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 501 (0x01f5) |
| 87 | 0x17ffc320 | reclaimToken(address) | nonpayable | 537 (0x0219) |
| 98 | 0x18160ddd | totalSupply() | view | 572 (0x023c) |
| 109 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 611 (0x0263) |
| 120 | 0x313ce567 | decimals() | view | 653 (0x028d) |
| 131 | 0x3f4ba83a | unpause() | nonpayable | 696 (0x02b8) |
| 142 | 0x40c10f19 | mint(address,uint256) | nonpayable | 717 (0x02cd) |
| 153 | 0x42966c68 | burn(uint256) | nonpayable | 753 (0x02f1) |
| 164 | 0x4e71e0c8 | claimOwnership() | nonpayable | 777 (0x0309) |
| 175 | 0x5c975abb | paused() | view | 798 (0x031e) |
| 186 | 0x66188463 | decreaseApproval(address,uint256) | nonpayable | 819 (0x0333) |
| 197 | 0x70a08231 | balanceOf(address) | view | 855 (0x0357) |
| 208 | 0x715018a6 | renounceOwnership() | nonpayable | 888 (0x0378) |
| 219 | 0x7d64bcb4 | finishMinting() | nonpayable | 909 (0x038d) |
| 230 | 0x8456cb59 | pause() | nonpayable | 930 (0x03a2) |
| 241 | 0x8da5cb5b | owner() | view | 951 (0x03b7) |
| 252 | 0x95d89b41 | symbol() | view | 1000 (0x03e8) |
| 263 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1021 (0x03fd) |
| 274 | 0xd73dd623 | increaseApproval(address,uint256) | nonpayable | 1057 (0x0421) |
| 285 | 0xdd62ed3e | allowance(address,address) | view | 1093 (0x0445) |
| 296 | 0xe30c3978 | pendingOwner() | view | 1132 (0x046c) |
| 307 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1153 (0x0481) |

Instructions: 2903; opcode counts: {"CALL": 3, "CALLCODE": 1, "CREATE2": 2, "EQ": 33, "EXTCODESIZE": 2, "INVALID": 2, "JUMP": 75, "JUMPDEST": 144, "JUMPI": 89, "LOG1": 2, "LOG2": 2, "LOG3": 8, "RETURN": 5, "RETURNDATACOPY": 2, "RETURNDATASIZE": 6, "REVERT": 56, "SHA3": 39, "SHL": 1, "SLOAD": 54, "SSTORE": 18, "STOP": 2}.

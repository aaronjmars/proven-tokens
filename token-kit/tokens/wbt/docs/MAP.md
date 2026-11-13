# Map of the WBT runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 833 (0x0341) |
| 66 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 881 (0x0371) |
| 77 | 0xdd62ed3e | allowance(address,address) | view | 929 (0x03a1) |
| 88 | 0xf2fde38b | transferOwnership(address) | nonpayable | 977 (0x03d1) |
| 99 | 0xf3bdc228 | destroyBlackFunds(address) | nonpayable | 1005 (0x03ed) |
| 110 | 0xfe575a87 | isBlacklisted(address) | view | 1033 (0x0409) |
| 126 | 0x70a08231 | balanceOf(address) | view | 705 (0x02c1) |
| 137 | 0x715018a6 | renounceOwnership() | nonpayable | 753 (0x02f1) |
| 148 | 0x8456cb59 | pause() | nonpayable | 763 (0x02fb) |
| 159 | 0x8da5cb5b | owner() | view | 773 (0x0305) |
| 170 | 0x95d89b41 | symbol() | view | 803 (0x0323) |
| 197 | 0x2f54bf6e | isOwner(address) | view | 511 (0x01ff) |
| 208 | 0x313ce567 | decimals() | view | 559 (0x022f) |
| 219 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 589 (0x024d) |
| 230 | 0x3f4ba83a | unpause() | nonpayable | 637 (0x027d) |
| 241 | 0x42966c68 | burn(uint256) | nonpayable | 647 (0x0287) |
| 252 | 0x5c975abb | paused() | view | 675 (0x02a3) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 357 (0x0165) |
| 290 | 0x18160ddd | totalSupply() | view | 405 (0x0195) |
| 301 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 435 (0x01b3) |
| 312 | 0x2d5a5d34 | blacklistAccount(address,bool) | nonpayable | 483 (0x01e3) |

Instructions: 3853; opcode counts: {"EQ": 36, "INVALID": 1, "JUMP": 255, "JUMPDEST": 324, "JUMPI": 71, "LOG1": 2, "LOG2": 1, "LOG3": 7, "RETURN": 15, "REVERT": 31, "SHA3": 26, "SHR": 1, "SLOAD": 38, "SSTORE": 15, "STOP": 7}.

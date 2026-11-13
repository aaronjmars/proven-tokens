# Map of the WETH runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0x06fdde03 | name() | view | 185 (0x00b9) |
| 66 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 327 (0x0147) |
| 77 | 0x18160ddd | totalSupply() | view | 417 (0x01a1) |
| 88 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 458 (0x01ca) |
| 99 | 0x2e1a7d4d | withdraw(uint256) | nonpayable | 579 (0x0243) |
| 110 | 0x313ce567 | decimals() | view | 614 (0x0266) |
| 121 | 0x70a08231 | balanceOf(address) | view | 661 (0x0295) |
| 132 | 0x95d89b41 | symbol() | view | 738 (0x02e2) |
| 143 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 880 (0x0370) |
| 154 | 0xd0e30db0 | deposit() | payable | 970 (0x03ca) |
| 165 | 0xdd62ed3e | allowance(address,address) | view | 980 (0x03d4) |

Instructions: 1555; opcode counts: {"BALANCE": 1, "CALL": 1, "EQ": 13, "JUMP": 28, "JUMPDEST": 64, "JUMPI": 38, "LOG2": 2, "LOG3": 2, "RETURN": 9, "REVERT": 14, "SHA3": 19, "SLOAD": 20, "SSTORE": 6, "STOP": 4}.

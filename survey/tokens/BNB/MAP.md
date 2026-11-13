# Map of the BNB runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 53 | 0x06fdde03 | name() | view | 226 (0x00e2) |
| 64 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 369 (0x0171) |
| 75 | 0x18160ddd | totalSupply() | view | 459 (0x01cb) |
| 86 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 500 (0x01f4) |
| 97 | 0x313ce567 | decimals() | view | 621 (0x026d) |
| 108 | 0x3bed33ce | withdrawEther(uint256) | nonpayable | 668 (0x029c) |
| 119 | 0x42966c68 | burn(uint256) | nonpayable | 703 (0x02bf) |
| 130 | 0x6623fc46 | unfreeze(uint256) | nonpayable | 762 (0x02fa) |
| 141 | 0x70a08231 | balanceOf(address) | view | 821 (0x0335) |
| 152 | 0x8da5cb5b | owner() | view | 898 (0x0382) |
| 163 | 0x95d89b41 | symbol() | view | 983 (0x03d7) |
| 174 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1126 (0x0466) |
| 185 | 0xcd4217c1 | freezeOf(address) | view | 1192 (0x04a8) |
| 196 | 0xd7a78db8 | freeze(uint256) | nonpayable | 1269 (0x04f5) |
| 207 | 0xdd62ed3e | allowance(address,address) | view | 1328 (0x0530) |

Instructions: 2487; opcode counts: {"CALL": 1, "EQ": 18, "JUMP": 51, "JUMPDEST": 124, "JUMPI": 61, "LOG2": 3, "LOG3": 2, "RETURN": 13, "REVERT": 34, "SHA3": 41, "SLOAD": 37, "SSTORE": 12, "STOP": 4}.

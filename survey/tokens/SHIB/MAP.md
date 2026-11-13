# Map of the SHIB runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0x06fdde03 | name() | view | 191 (0x00bf) |
| 66 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 335 (0x014f) |
| 77 | 0x18160ddd | totalSupply() | view | 450 (0x01c2) |
| 88 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 493 (0x01ed) |
| 99 | 0x313ce567 | decimals() | view | 640 (0x0280) |
| 110 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 689 (0x02b1) |
| 121 | 0x42966c68 | burn(uint256) | nonpayable | 804 (0x0324) |
| 132 | 0x70a08231 | balanceOf(address) | view | 863 (0x035f) |
| 143 | 0x95d89b41 | symbol() | view | 964 (0x03c4) |
| 154 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 1108 (0x0454) |
| 165 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1223 (0x04c7) |
| 176 | 0xdd62ed3e | allowance(address,address) | view | 1338 (0x053a) |

Instructions: 2270; opcode counts: {"EQ": 17, "INVALID": 1, "JUMP": 47, "JUMPDEST": 95, "JUMPI": 50, "LOG3": 3, "RETURN": 11, "REVERT": 28, "SHA3": 19, "SLOAD": 19, "SSTORE": 5, "STOP": 1}.

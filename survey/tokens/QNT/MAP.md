# Map of the QNT runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0x06fdde03 | name() | view | 213 (0x00d5) |
| 66 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 355 (0x0163) |
| 77 | 0x18160ddd | totalSupply() | view | 445 (0x01bd) |
| 88 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 486 (0x01e6) |
| 99 | 0x313ce567 | decimals() | view | 607 (0x025f) |
| 110 | 0x40c10f19 | mint(address,uint256) | nonpayable | 654 (0x028e) |
| 121 | 0x414d784e | DECIMAL_ZEROS() | view | 720 (0x02d0) |
| 132 | 0x66188463 | decreaseApproval(address,uint256) | nonpayable | 761 (0x02f9) |
| 143 | 0x70a08231 | balanceOf(address) | view | 851 (0x0353) |
| 154 | 0x95d89b41 | symbol() | view | 928 (0x03a0) |
| 165 | 0x9c1e03a0 | crowdsale() | view | 1070 (0x042e) |
| 176 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1155 (0x0483) |
| 187 | 0xd73dd623 | increaseApproval(address,uint256) | nonpayable | 1245 (0x04dd) |
| 198 | 0xdd62ed3e | allowance(address,address) | view | 1335 (0x0537) |

Instructions: 2126; opcode counts: {"EQ": 17, "INVALID": 2, "JUMP": 41, "JUMPDEST": 83, "JUMPI": 42, "LOG3": 6, "RETURN": 13, "REVERT": 21, "SHA3": 37, "SLOAD": 18, "SSTORE": 10, "STOP": 2}.

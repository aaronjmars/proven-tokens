# Map of the LINK runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 51 | 0x06fdde03 | name() | view | 188 (0x00bc) |
| 63 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 327 (0x0147) |
| 74 | 0x18160ddd | totalSupply() | view | 381 (0x017d) |
| 85 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 418 (0x01a2) |
| 96 | 0x313ce567 | decimals() | view | 478 (0x01de) |
| 107 | 0x4000aea0 | transferAndCall(address,uint256,bytes) | nonpayable | 519 (0x0207) |
| 118 | 0x66188463 | decreaseApproval(address,uint256) | nonpayable | 640 (0x0280) |
| 129 | 0x70a08231 | balanceOf(address) | view | 694 (0x02b6) |
| 140 | 0x95d89b41 | symbol() | view | 743 (0x02e7) |
| 151 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 882 (0x0372) |
| 162 | 0xd73dd623 | increaseApproval(address,uint256) | nonpayable | 936 (0x03a8) |
| 173 | 0xdd62ed3e | allowance(address,address) | view | 990 (0x03de) |

Instructions: 2131; opcode counts: {"CALL": 1, "EQ": 16, "EXTCODESIZE": 2, "INVALID": 2, "JUMP": 51, "JUMPDEST": 122, "JUMPI": 47, "LOG3": 6, "RETURN": 12, "REVERT": 19, "SHA3": 29, "SLOAD": 10, "SSTORE": 9, "STOP": 1}.

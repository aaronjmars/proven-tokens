# Map of the SKY runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0x9fd5a6cf | permit(address,address,uint256,uint256,bytes) | nonpayable | 747 (0x02eb) |
| 66 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 766 (0x02fe) |
| 77 | 0xbf353dbb | wards(address) | view | 785 (0x0311) |
| 88 | 0xcd0d0096 | deploymentChainId() | view | 817 (0x0331) |
| 99 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 856 (0x0358) |
| 110 | 0xdd62ed3e | allowance(address,address) | view | 875 (0x036b) |
| 126 | 0x70a08231 | balanceOf(address) | view | 611 (0x0263) |
| 137 | 0x7ecebe00 | nonces(address) | view | 643 (0x0283) |
| 148 | 0x95d89b41 | symbol() | view | 675 (0x02a3) |
| 159 | 0x9c52a7f1 | deny(address) | nonpayable | 709 (0x02c5) |
| 170 | 0x9dc29fac | burn(address,uint256) | nonpayable | 728 (0x02d8) |
| 197 | 0x313ce567 | decimals() | view | 505 (0x01f9) |
| 208 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 531 (0x0213) |
| 219 | 0x40c10f19 | mint(address,uint256) | nonpayable | 539 (0x021b) |
| 230 | 0x54fd4d50 | version() | view | 560 (0x0230) |
| 241 | 0x65fae35e | rely(address) | nonpayable | 592 (0x0250) |
| 257 | 0x06fdde03 | name() | view | 316 (0x013c) |
| 268 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 389 (0x0185) |
| 279 | 0x18160ddd | totalSupply() | view | 424 (0x01a8) |
| 290 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 447 (0x01bf) |
| 301 | 0x30adf81f | PERMIT_TYPEHASH() | view | 466 (0x01d2) |

Instructions: 2977; opcode counts: {"CALL": 1, "CALLCODE": 1, "CHAINID": 4, "CREATE2": 2, "EQ": 39, "EXTCODESIZE": 1, "INVALID": 1, "JUMP": 110, "JUMPDEST": 149, "JUMPI": 73, "LOG2": 2, "LOG3": 6, "RETURN": 1, "RETURNDATACOPY": 2, "RETURNDATASIZE": 6, "REVERT": 22, "SHA3": 35, "SHL": 66, "SHR": 1, "SLOAD": 19, "SSTORE": 15, "STATICCALL": 2, "STOP": 1, "TIMESTAMP": 1}.

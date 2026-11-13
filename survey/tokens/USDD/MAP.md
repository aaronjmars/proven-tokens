# Map of the USDD runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 990 (0x03de) |
| 66 | 0xb753a98c | push(address,uint256) | nonpayable | 1034 (0x040a) |
| 77 | 0xbb35783b | move(address,address,uint256) | nonpayable | 1078 (0x0436) |
| 88 | 0xbf353dbb | wards(address) | view | 1132 (0x046c) |
| 99 | 0xdd62ed3e | allowance(address,address) | view | 1170 (0x0492) |
| 110 | 0xf2d5d56b | pull(address,uint256) | nonpayable | 1216 (0x04c0) |
| 126 | 0x7ecebe00 | nonces(address) | view | 772 (0x0304) |
| 137 | 0x8fcbaf0c | permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32) | nonpayable | 810 (0x032a) |
| 148 | 0x95d89b41 | symbol() | view | 900 (0x0384) |
| 159 | 0x9c52a7f1 | deny(address) | nonpayable | 908 (0x038c) |
| 170 | 0x9dc29fac | burn(address,uint256) | nonpayable | 946 (0x03b2) |
| 197 | 0x313ce567 | decimals() | view | 604 (0x025c) |
| 208 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 634 (0x027a) |
| 219 | 0x40c10f19 | mint(address,uint256) | nonpayable | 642 (0x0282) |
| 230 | 0x54fd4d50 | version() | view | 688 (0x02b0) |
| 241 | 0x65fae35e | rely(address) | nonpayable | 696 (0x02b8) |
| 252 | 0x70a08231 | balanceOf(address) | view | 734 (0x02de) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 452 (0x01c4) |
| 290 | 0x18160ddd | totalSupply() | view | 516 (0x0204) |
| 301 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 542 (0x021e) |
| 312 | 0x30adf81f | PERMIT_TYPEHASH() | view | 596 (0x0254) |

Instructions: 2598; opcode counts: {"EQ": 31, "INVALID": 1, "JUMP": 60, "JUMPDEST": 105, "JUMPI": 64, "LOG3": 5, "RETURN": 4, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 31, "SHA3": 43, "SHL": 68, "SHR": 1, "SLOAD": 25, "SSTORE": 13, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 1}.

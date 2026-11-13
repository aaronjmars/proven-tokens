# Map of the DAI runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1716 (0x06b4) |
| 66 | 0xb753a98c | push(address,uint256) | nonpayable | 1818 (0x071a) |
| 77 | 0xbb35783b | move(address,address,uint256) | nonpayable | 1896 (0x0768) |
| 88 | 0xbf353dbb | wards(address) | view | 2006 (0x07d6) |
| 99 | 0xdd62ed3e | allowance(address,address) | view | 2094 (0x082e) |
| 110 | 0xf2d5d56b | pull(address,uint256) | nonpayable | 2214 (0x08a6) |
| 126 | 0x7ecebe00 | nonces(address) | view | 1185 (0x04a1) |
| 137 | 0x8fcbaf0c | permit(address,address,uint256,uint256,bool,uint8,bytes32,bytes32) | nonpayable | 1273 (0x04f9) |
| 148 | 0x95d89b41 | symbol() | view | 1439 (0x059f) |
| 159 | 0x9c52a7f1 | deny(address) | nonpayable | 1570 (0x0622) |
| 170 | 0x9dc29fac | burn(address,uint256) | nonpayable | 1638 (0x0666) |
| 197 | 0x313ce567 | decimals() | view | 754 (0x02f2) |
| 208 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 790 (0x0316) |
| 219 | 0x40c10f19 | mint(address,uint256) | nonpayable | 820 (0x0334) |
| 230 | 0x54fd4d50 | version() | view | 898 (0x0382) |
| 241 | 0x65fae35e | rely(address) | nonpayable | 1029 (0x0405) |
| 252 | 0x70a08231 | balanceOf(address) | view | 1097 (0x0449) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 458 (0x01ca) |
| 290 | 0x18160ddd | totalSupply() | view | 560 (0x0230) |
| 301 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 590 (0x024e) |
| 312 | 0x30adf81f | PERMIT_TYPEHASH() | view | 724 (0x02d4) |

Instructions: 3488; opcode counts: {"EQ": 33, "INVALID": 1, "JUMP": 65, "JUMPDEST": 130, "JUMPI": 68, "LOG3": 5, "LOG4": 2, "RETURN": 14, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 31, "SHA3": 43, "SHL": 4, "SHR": 3, "SLOAD": 25, "SSTORE": 13, "STATICCALL": 1, "STOP": 8, "TIMESTAMP": 1}.

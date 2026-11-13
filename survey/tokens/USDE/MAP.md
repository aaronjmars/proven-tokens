# Map of the USDE runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 66 | 0xdd62ed3e | allowance(address,address) | view | 907 (0x038b) |
| 77 | 0xe30c3978 | pendingOwner() | view | 977 (0x03d1) |
| 88 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1007 (0x03ef) |
| 99 | 0xfca3b5aa | setMinter(address) | nonpayable | 1026 (0x0402) |
| 115 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 850 (0x0352) |
| 126 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 869 (0x0365) |
| 137 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 888 (0x0378) |
| 164 | 0x84b0196e | eip712Domain() | view | 785 (0x0311) |
| 175 | 0x8da5cb5b | owner() | view | 812 (0x032c) |
| 186 | 0x95d89b41 | symbol() | view | 842 (0x034a) |
| 202 | 0x79ba5097 | acceptOwnership() | nonpayable | 739 (0x02e3) |
| 213 | 0x79cc6790 | burnFrom(address,uint256) | nonpayable | 747 (0x02eb) |
| 224 | 0x7ecebe00 | nonces(address) | view | 766 (0x02fe) |
| 262 | 0x42966c68 | burn(uint256) | nonpayable | 658 (0x0292) |
| 273 | 0x70a08231 | balanceOf(address) | view | 677 (0x02a5) |
| 284 | 0x715018a6 | renounceOwnership() | view | 731 (0x02db) |
| 300 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 610 (0x0262) |
| 311 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 618 (0x026a) |
| 322 | 0x40c10f19 | mint(address,uint256) | nonpayable | 637 (0x027d) |
| 349 | 0x18160ddd | totalSupply() | view | 558 (0x022e) |
| 360 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 576 (0x0240) |
| 371 | 0x313ce567 | decimals() | view | 595 (0x0253) |
| 387 | 0x06fdde03 | name() | view | 424 (0x01a8) |
| 398 | 0x07546172 | minter() | view | 454 (0x01c6) |
| 409 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 523 (0x020b) |

Instructions: 3107; opcode counts: {"CHAINID": 3, "EQ": 35, "INVALID": 1, "JUMP": 154, "JUMPDEST": 195, "JUMPI": 84, "LOG3": 6, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 25, "SHA3": 24, "SHR": 2, "SLOAD": 35, "SSTORE": 12, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 1}.

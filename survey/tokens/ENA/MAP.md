# Map of the ENA runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 64 | 0xdd62ed3e | allowance(address,address) | view | 947 (0x03b3) |
| 75 | 0xe30c3978 | pendingOwner() | view | 1016 (0x03f8) |
| 86 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1046 (0x0416) |
| 97 | 0xfdb04bbf | MAX_INFLATION() | view | 1065 (0x0429) |
| 112 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 890 (0x037a) |
| 123 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 909 (0x038d) |
| 134 | 0xd505accf | permit(address,address,uint256,uint256,uint8,bytes32,bytes32) | nonpayable | 928 (0x03a0) |
| 160 | 0x8da5cb5b | owner() | view | 781 (0x030d) |
| 171 | 0x8e80ff5d | lastMintTimestamp() | view | 843 (0x034b) |
| 182 | 0x95d89b41 | symbol() | view | 882 (0x0372) |
| 197 | 0x79cc6790 | burnFrom(address,uint256) | nonpayable | 716 (0x02cc) |
| 208 | 0x7ecebe00 | nonces(address) | view | 735 (0x02df) |
| 219 | 0x84b0196e | eip712Domain() | view | 754 (0x02f2) |
| 256 | 0x42966c68 | burn(uint256) | nonpayable | 628 (0x0274) |
| 267 | 0x70a08231 | balanceOf(address) | view | 647 (0x0287) |
| 278 | 0x715018a6 | renounceOwnership() | view | 700 (0x02bc) |
| 289 | 0x79ba5097 | acceptOwnership() | nonpayable | 708 (0x02c4) |
| 304 | 0x3644e515 | DOMAIN_SEPARATOR() | view | 580 (0x0244) |
| 315 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 588 (0x024c) |
| 326 | 0x40c10f19 | mint(address,uint256) | nonpayable | 607 (0x025f) |
| 352 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 508 (0x01fc) |
| 363 | 0x313ce567 | decimals() | view | 527 (0x020f) |
| 374 | 0x3544fd2b | MINT_WAIT_PERIOD() | view | 548 (0x0224) |
| 389 | 0x06fdde03 | name() | view | 425 (0x01a9) |
| 400 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 455 (0x01c7) |
| 411 | 0x18160ddd | totalSupply() | view | 490 (0x01ea) |

Instructions: 3250; opcode counts: {"CHAINID": 3, "EQ": 36, "INVALID": 1, "JUMP": 164, "JUMPDEST": 209, "JUMPI": 89, "LOG2": 1, "LOG3": 5, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 27, "SHA3": 24, "SHR": 2, "SLOAD": 35, "SSTORE": 12, "STATICCALL": 1, "STOP": 1, "TIMESTAMP": 3}.

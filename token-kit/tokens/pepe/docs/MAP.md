# Map of the PEPE runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 55 | 0x8da5cb5b | owner() | view | 619 (0x026b) |
| 66 | 0x95d89b41 | symbol() | view | 627 (0x0273) |
| 77 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 635 (0x027b) |
| 88 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 654 (0x028e) |
| 99 | 0xdd62ed3e | allowance(address,address) | view | 673 (0x02a1) |
| 110 | 0xf2fde38b | transferOwnership(address) | nonpayable | 692 (0x02b4) |
| 126 | 0x49bd5a5e | uniswapV2Pair() | view | 555 (0x022b) |
| 137 | 0x70a08231 | balanceOf(address) | view | 576 (0x0240) |
| 148 | 0x715018a6 | renounceOwnership() | nonpayable | 595 (0x0253) |
| 159 | 0x860a32ec | limited() | view | 603 (0x025b) |
| 170 | 0x89f9a1d3 | maxHoldingAmount() | view | 611 (0x0263) |
| 197 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 437 (0x01b5) |
| 208 | 0x313ce567 | decimals() | view | 456 (0x01c8) |
| 219 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 477 (0x01dd) |
| 230 | 0x3aa633aa | setRule(bool,address,uint256,uint256) | nonpayable | 496 (0x01f0) |
| 241 | 0x404e5129 | blacklist(address,bool) | nonpayable | 517 (0x0205) |
| 252 | 0x42966c68 | burn(uint256) | nonpayable | 536 (0x0218) |
| 268 | 0x06fdde03 | name() | view | 327 (0x0147) |
| 279 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 357 (0x0165) |
| 290 | 0x16c02129 | blacklists(address) | view | 389 (0x0185) |
| 301 | 0x18160ddd | totalSupply() | view | 408 (0x0198) |
| 312 | 0x1ab99e12 | minHoldingAmount() | view | 429 (0x01ad) |

Instructions: 2677; opcode counts: {"EQ": 32, "INVALID": 1, "JUMP": 168, "JUMPDEST": 195, "JUMPI": 68, "LOG3": 4, "RETURN": 1, "REVERT": 14, "SHA3": 21, "SHL": 78, "SHR": 1, "SLOAD": 32, "SSTORE": 11, "STOP": 1}.

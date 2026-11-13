
> Kit layout: this project is `tokens/weth` of the token kit. `scripts/...` below means the scripts of the kit (`../../scripts`), run as `bash ../../scripts/regen.sh config/weth.json`; the generic Lean files are the library `TokenKit` of the kit (`../../TokenKit/Evm`), not a folder of this project.
| index | entry pc | selector | signature | destination | covered by |
|---|---|---|---|---|---|
| 0 | 54 | 0x06fdde03 | name() | 185 (0x00b9) | read-only loop |
| 1 | 65 | 0x095ea7b3 | approve(address,uint256) | 327 (0x0147) | paths |
| 2 | 76 | 0x18160ddd | totalSupply() | 417 (0x01a1) | paths |
| 3 | 87 | 0x23b872dd | transferFrom(address,address,uint256) | 458 (0x01ca) | paths |
| 4 | 98 | 0x2e1a7d4d | withdraw(uint256) | 579 (0x0243) | paths |
| 5 | 109 | 0x313ce567 | decimals() | 614 (0x0266) | paths |
| 6 | 120 | 0x70a08231 | balanceOf(address) | 661 (0x0295) | paths |
| 7 | 131 | 0x95d89b41 | symbol() | 738 (0x02e2) | read-only loop |
| 8 | 142 | 0xa9059cbb | transfer(address,uint256) | 880 (0x0370) | paths |
| 9 | 153 | 0xd0e30db0 | deposit() | 970 (0x03ca) | paths |
| 10 | 164 | 0xdd62ed3e | allowance(address,address) | 980 (0x03d4) | paths |

Instructions: 1577; JUMPDESTs at an opcode boundary: 64.

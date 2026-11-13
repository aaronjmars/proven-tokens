
> Kit layout: this project is `tokens/bnb` of the token kit. `scripts/...` below means the scripts of the kit (`../../scripts`), run as `bash ../../scripts/regen.sh config/bnb.json`; the generic Lean files are the library `TokenKit` of the kit (`../../TokenKit/Evm`), not a folder of this project.
| index | entry pc | selector | signature | destination | covered by |
|---|---|---|---|---|---|
| 0 | 52 | 0x06fdde03 | name() | 226 (0x00e2) | read-only loop |
| 1 | 63 | 0x095ea7b3 | approve(address,uint256) | 369 (0x0171) | paths |
| 2 | 74 | 0x18160ddd | totalSupply() | 459 (0x01cb) | paths |
| 3 | 85 | 0x23b872dd | transferFrom(address,address,uint256) | 500 (0x01f4) | paths |
| 4 | 96 | 0x313ce567 | decimals() | 621 (0x026d) | paths |
| 5 | 107 | 0x3bed33ce | withdrawEther(uint256) | 668 (0x029c) | paths |
| 6 | 118 | 0x42966c68 | burn(uint256) | 703 (0x02bf) | paths |
| 7 | 129 | 0x6623fc46 | unfreeze(uint256) | 762 (0x02fa) | paths |
| 8 | 140 | 0x70a08231 | balanceOf(address) | 821 (0x0335) | paths |
| 9 | 151 | 0x8da5cb5b | owner() | 898 (0x0382) | paths |
| 10 | 162 | 0x95d89b41 | symbol() | 983 (0x03d7) | read-only loop |
| 11 | 173 | 0xa9059cbb | transfer(address,uint256) | 1126 (0x0466) | paths |
| 12 | 184 | 0xcd4217c1 | freezeOf(address) | 1192 (0x04a8) | paths |
| 13 | 195 | 0xd7a78db8 | freeze(uint256) | 1269 (0x04f5) | paths |
| 14 | 206 | 0xdd62ed3e | allowance(address,address) | 1328 (0x0530) | paths |

Instructions: 2513; JUMPDESTs at an opcode boundary: 124.

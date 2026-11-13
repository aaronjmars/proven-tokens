# Map of the GRAM runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 66 | 0xcf1a0ce1 | finishedVotings(bytes32) | view | 798 (0x031e) |
| 77 | 0xdd62ed3e | allowance(address,address) | view | 817 (0x0331) |
| 88 | 0xe057fbff | burn(uint256,(int8,bytes32)) | nonpayable | 836 (0x0344) |
| 99 | 0xffb6b2fa | voteForSwitchBurn(bool,int256,(address,bytes)[]) | nonpayable | 855 (0x0357) |
| 115 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 741 (0x02e5) |
| 126 | 0xa97e5c93 | isOracle(address) | view | 760 (0x02f8) |
| 137 | 0xaefe7da4 | getNewSetId(int256,address[]) | pure | 779 (0x030b) |
| 153 | 0x70a08231 | balanceOf(address) | view | 636 (0x027c) |
| 164 | 0x75f2d82b | getFullOracleSet() | view | 655 (0x028f) |
| 175 | 0x7ddc1027 | getNewBurnStatusId(bool,int256) | pure | 676 (0x02a4) |
| 186 | 0x95d89b41 | symbol() | view | 695 (0x02b7) |
| 197 | 0xa2d7cab8 | checkSignature(bytes32,(address,bytes)) | pure | 703 (0x02bf) |
| 208 | 0xa457c2d7 | decreaseAllowance(address,uint256) | nonpayable | 722 (0x02d2) |
| 235 | 0x35e061fc | allowBurn() | view | 520 (0x0208) |
| 246 | 0x39509351 | increaseAllowance(address,uint256) | nonpayable | 528 (0x0210) |
| 257 | 0x4054b92b | voteForMinting((address,uint64,((int8,bytes32),bytes32,uint64)),(address,bytes)[]) | nonpayable | 547 (0x0223) |
| 268 | 0x43672af0 | burnFrom(address,uint256,(int8,bytes32)) | nonpayable | 566 (0x0236) |
| 279 | 0x4fd77954 | oraclesSet(uint256) | view | 585 (0x0249) |
| 290 | 0x633a0d18 | getSwapDataId((address,uint64,((int8,bytes32),bytes32,uint64))) | pure | 617 (0x0269) |
| 306 | 0x06fdde03 | name() | view | 376 (0x0178) |
| 317 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 406 (0x0196) |
| 328 | 0x0a55ec25 | voteForNewOracleSet(int256,address[],(address,bytes)[]) | nonpayable | 438 (0x01b6) |
| 339 | 0x18160ddd | totalSupply() | view | 459 (0x01cb) |
| 350 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 480 (0x01e0) |
| 361 | 0x313ce567 | decimals() | pure | 499 (0x01f3) |

Instructions: 5013; opcode counts: {"EQ": 33, "INVALID": 13, "JUMP": 219, "JUMPDEST": 296, "JUMPI": 121, "LOG1": 1, "LOG3": 6, "LOG4": 1, "NUMBER": 3, "RETURN": 1, "RETURNDATACOPY": 1, "RETURNDATASIZE": 2, "REVERT": 49, "SHA3": 40, "SHL": 78, "SHR": 1, "SLOAD": 41, "SSTORE": 14, "STATICCALL": 1, "STOP": 1}.

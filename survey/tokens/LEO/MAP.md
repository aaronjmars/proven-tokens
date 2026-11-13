# Map of the LEO runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 22 | 0x06fdde03 | name() | view | 478 (0x01de) |
| 34 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 616 (0x0268) |
| 45 | 0x17634514 | creationBlock() | view | 693 (0x02b5) |
| 56 | 0x18160ddd | totalSupply() | view | 732 (0x02dc) |
| 67 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 753 (0x02f1) |
| 78 | 0x313ce567 | decimals() | view | 820 (0x0334) |
| 89 | 0x3cebb823 | changeController(address) | nonpayable | 863 (0x035f) |
| 100 | 0x4ee2cd7e | balanceOfAt(address,uint256) | view | 914 (0x0392) |
| 111 | 0x54fd4d50 | version() | view | 971 (0x03cb) |
| 122 | 0x6638c087 | createCloneToken(string,uint8,string,uint256,bool) | nonpayable | 992 (0x03e0) |
| 133 | 0x70a08231 | balanceOf(address) | view | 1352 (0x0548) |
| 144 | 0x80a54001 | parentToken() | view | 1403 (0x057b) |
| 155 | 0x827f32c0 | generateTokens(address,uint256) | nonpayable | 1424 (0x0590) |
| 166 | 0x95d89b41 | symbol() | view | 1481 (0x05c9) |
| 177 | 0x981b24d0 | totalSupplyAt(uint256) | view | 1502 (0x05de) |
| 188 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1544 (0x0608) |
| 199 | 0xbef97c87 | transfersEnabled() | view | 1601 (0x0641) |
| 210 | 0xc5bcc4f1 | parentSnapShotBlock() | view | 1622 (0x0656) |
| 221 | 0xcae9ca51 | approveAndCall(address,uint256,bytes) | nonpayable | 1643 (0x066b) |
| 232 | 0xd3ce77fe | destroyTokens(address,uint256) | nonpayable | 1843 (0x0733) |
| 243 | 0xdd62ed3e | allowance(address,address) | view | 1900 (0x076c) |
| 254 | 0xe77772fe | tokenFactory() | view | 1959 (0x07a7) |
| 265 | 0xf41e60c5 | enableTransfers(bool) | nonpayable | 1980 (0x07bc) |
| 276 | 0xf77c4791 | controller() | view | 2024 (0x07e8) |

Instructions: 4485; opcode counts: {"CALL": 7, "CALLCODE": 1, "CREATE2": 2, "EQ": 30, "EXTCODESIZE": 9, "INVALID": 11, "JUMP": 97, "JUMPDEST": 229, "JUMPI": 165, "LOG2": 1, "LOG3": 6, "NUMBER": 8, "RETURN": 5, "RETURNDATACOPY": 8, "RETURNDATASIZE": 22, "REVERT": 90, "SHA3": 31, "SHL": 1, "SLOAD": 69, "SSTORE": 10, "STATICCALL": 2, "STOP": 1}.

# Map of the CRO runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 53 | 0x02f652a3 | setTransferAgent(address,bool) | nonpayable | 454 (0x01c6) |
| 65 | 0x05d2035b | mintingFinished() | view | 494 (0x01ee) |
| 76 | 0x06fdde03 | name() | view | 535 (0x0217) |
| 87 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 673 (0x02a1) |
| 98 | 0x18160ddd | totalSupply() | view | 709 (0x02c5) |
| 109 | 0x1f3bec3b | secondarySaleReserveWallet() | view | 748 (0x02ec) |
| 120 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 797 (0x031d) |
| 131 | 0x29ff4f53 | setReleaseAgent(address) | nonpayable | 839 (0x0347) |
| 142 | 0x313ce567 | decimals() | view | 872 (0x0368) |
| 153 | 0x40c10f19 | mint(address,uint256) | nonpayable | 915 (0x0393) |
| 164 | 0x45977d03 | upgrade(uint256) | nonpayable | 951 (0x03b7) |
| 175 | 0x5de4ccb0 | upgradeAgent() | view | 975 (0x03cf) |
| 186 | 0x5f412d4f | releaseTokenTransfer() | nonpayable | 996 (0x03e4) |
| 197 | 0x600440cb | upgradeMaster() | view | 1017 (0x03f9) |
| 208 | 0x642b4a4d | mainNetLaunchIncentiveReserveWallet() | view | 1038 (0x040e) |
| 219 | 0x66188463 | decreaseApproval(address,uint256) | nonpayable | 1059 (0x0423) |
| 230 | 0x70a08231 | balanceOf(address) | view | 1095 (0x0447) |
| 241 | 0x715018a6 | renounceOwnership() | nonpayable | 1128 (0x0468) |
| 252 | 0x7d64bcb4 | finishMinting() | nonpayable | 1149 (0x047d) |
| 263 | 0x8444b391 | getUpgradeState() | view | 1170 (0x0492) |
| 274 | 0x867c2857 | transferAgents(address) | view | 1227 (0x04cb) |
| 285 | 0x8da5cb5b | owner() | view | 1260 (0x04ec) |
| 296 | 0x95d89b41 | symbol() | view | 1281 (0x0501) |
| 307 | 0x96132521 | released() | view | 1302 (0x0516) |
| 318 | 0x9738968c | canUpgrade() | view | 1323 (0x052b) |
| 329 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 1344 (0x0540) |
| 340 | 0xadf403ad | capitalReserveWallet() | view | 1380 (0x0564) |
| 351 | 0xae1616b0 | airdropReserveWallet() | view | 1401 (0x0579) |
| 362 | 0xc752ff62 | totalUpgraded() | view | 1422 (0x058e) |
| 373 | 0xd1f276d3 | releaseAgent() | view | 1443 (0x05a3) |
| 384 | 0xd73dd623 | increaseApproval(address,uint256) | nonpayable | 1464 (0x05b8) |
| 395 | 0xd7e7088a | setUpgradeAgent(address) | nonpayable | 1500 (0x05dc) |
| 406 | 0xdd62ed3e | allowance(address,address) | view | 1533 (0x05fd) |
| 417 | 0xdd681e51 | ecosystemGrantsReserveWallet() | view | 1572 (0x0624) |
| 428 | 0xf2fde38b | transferOwnership(address) | nonpayable | 1593 (0x0639) |
| 439 | 0xffeb7d75 | setUpgradeMaster(address) | nonpayable | 1626 (0x065a) |

Instructions: 4327; opcode counts: {"CALL": 3, "EQ": 50, "EXTCODESIZE": 3, "INVALID": 8, "JUMP": 106, "JUMPDEST": 206, "JUMPI": 134, "LOG1": 2, "LOG2": 2, "LOG3": 8, "RETURN": 6, "RETURNDATACOPY": 3, "RETURNDATASIZE": 8, "REVERT": 76, "SHA3": 43, "SLOAD": 78, "SSTORE": 23, "STOP": 2}.

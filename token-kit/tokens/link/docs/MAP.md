# Map of the LINK runtime bytecode

| entry pc | selector | signature | kind | destination |
|---|---|---|---|---|
| 51 | 0x06fdde03 | name() | view | 188 (0x00bc) |
| 63 | 0x095ea7b3 | approve(address,uint256) | nonpayable | 327 (0x0147) |
| 74 | 0x18160ddd | totalSupply() | view | 381 (0x017d) |
| 85 | 0x23b872dd | transferFrom(address,address,uint256) | nonpayable | 418 (0x01a2) |
| 96 | 0x313ce567 | decimals() | view | 478 (0x01de) |
| 107 | 0x4000aea0 | transferAndCall(address,uint256,bytes) | nonpayable | 519 (0x0207) |
| 118 | 0x66188463 | decreaseApproval(address,uint256) | nonpayable | 640 (0x0280) |
| 129 | 0x70a08231 | balanceOf(address) | view | 694 (0x02b6) |
| 140 | 0x95d89b41 | symbol() | view | 743 (0x02e7) |
| 151 | 0xa9059cbb | transfer(address,uint256) | nonpayable | 882 (0x0372) |
| 162 | 0xd73dd623 | increaseApproval(address,uint256) | nonpayable | 936 (0x03a8) |
| 173 | 0xdd62ed3e | allowance(address,address) | view | 990 (0x03de) |

Instructions: 2131; opcode counts: {"CALL": 1, "EQ": 16, "EXTCODESIZE": 2, "INVALID": 2, "JUMP": 51, "JUMPDEST": 122, "JUMPI": 47, "LOG3": 6, "RETURN": 12, "REVERT": 19, "SHA3": 29, "SLOAD": 10, "SSTORE": 9, "STOP": 1}.

## The keccak hypothesis of the supply theorems (added by the fix round of the ten-token audit)

Every per-call supply theorem (`supply_transfer`, `supply_preserved`, `supply_all`, ...) takes
`Sep (callKeys message)`: for the 3 address words of the call (caller and the first two
arguments), each of the 3 balance slots `mapSlot a 1` is the balance slot of no other address,
and none of the 9 allowance slots `mapSlot s (mapSlot o 2)` is a balance slot. It is a fact about
keccak256 that is never proved here, so no `supply_*` theorem has a closed machine-checked
instance. Under the usual heuristic that keccak256 behaves as a random function, the chance that
it fails for one call is about 12 * 2^-96 (12 slots, each against at most 2^160 balance slots of
256 bits). The global forms `SepAll` and `Reenter.NoCollision CODE` (every list of keys, every
byte string) are almost certainly FALSE by counting and are used only by theorems that carry
`_sepAll_noCollision`, `_sepAll` or `_of_global` in the name, or are named `*.toLocal`.

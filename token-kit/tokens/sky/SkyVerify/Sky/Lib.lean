import SkyVerify.Sky.Steps
import TokenKit.Evm.Env08

/-!
# Facts of the SKY bytecode that the block lemmas use

- `codeWord_4767`: the 32 bytes of the code from 4767 are the topic of the event
  `Transfer(address,address,uint256)`. The code reads it with CODECOPY (it is no PUSH32).
-/

namespace SkyVerify

open UsdtVerify
open TokenKit

open EthLib.Base (Fork U256 bytesToNat)
open EthLib.Execution
open EthLib.Execution.Evm
open EthLib.Execution.Evm.Logic

theorem codeWord_4767 : (⟨(bufferRead CODE 4767 32).toArray⟩ : ByteArray) =
    wordBytes (0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef : U256) := by
  simp only [bufferRead, byteAt_CODE]
  decide +kernel

end SkyVerify

import TokenKit.Evm.WitnessOpt

/-!
# Sanity: the address of WBTC on mainnet

The witnesses of `Sanity/Reclaim*.lean` run the contract at an address whose word is the word of
WBTC on mainnet. `WBTC_ADDRESS` is that address. Proved: its address word. Assumed: nothing.
Not covered: nothing else is said here.
-/

namespace WbtcVerify.Sanity

open TokenKit
open EthLib.Base (U256 Address)

/-- The address of the WBTC token on Ethereum mainnet. -/
def WBTC_ADDRESS : Address :=
  #v[0x22, 0x60, 0xfa, 0xc5, 0xe5, 0x54, 0x2a, 0x77, 0x3a, 0xa4, 0x4f, 0xbc, 0xfe, 0xdf, 0x7c,
    0x19, 0x3b, 0xc2, 0xc5, 0x99]

/-- The address word of `WBTC_ADDRESS`. -/
theorem wbtc_address_word :
    WBTC_ADDRESS.toU256 = (0x2260fac5e5542a773aa44fbcfedf7c193bc2c599 : U256) := by decide

end WbtcVerify.Sanity

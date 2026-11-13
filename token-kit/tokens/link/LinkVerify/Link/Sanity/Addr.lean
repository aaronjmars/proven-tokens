import TokenKit.Evm.WitnessOpt

/-!
# Sanity: the address of LINK on mainnet

The witnesses of `Sanity/Zero.lean` take the address word of the contract as a hypothesis `hC`.
`LINK_ADDRESS` is an address with that word, so the hypothesis holds for a real address.
-/

namespace LinkVerify.Sanity

open TokenKit
open EthLib.Base (U256 Address)

/-- The address of the LINK token on Ethereum mainnet. -/
def LINK_ADDRESS : Address :=
  #v[0x51, 0x49, 0x10, 0x77, 0x1a, 0xf9, 0xca, 0x65, 0x6a, 0xf8, 0x40, 0xdf, 0xf8, 0x3e, 0x82,
    0x64, 0xec, 0xf9, 0x86, 0xca]

/-- The address word of `LINK_ADDRESS`. -/
theorem link_address_word :
    LINK_ADDRESS.toU256 = (0x514910771af9ca656af840dff83e8264ecf986ca : U256) := by decide

end LinkVerify.Sanity

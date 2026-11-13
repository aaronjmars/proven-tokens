import Lake
open Lake DSL

/-! The shared Lean library of the token kit: EVM helper lemmas and tactics that are not about one
token (`TokenKit/Evm`). It stands on EthLib and on the general EVM lemmas of usdt-verify
(`UsdtVerify/Evm`), a checkout that must sit next to this folder as `../usdt-verify`. The packages
directory is the one of that already built checkout, so EthLib and Mathlib are not fetched or built
again. -/

package «TokenKit» where
  packagesDir := "../usdt-verify/.lake/packages"

require UsdtVerify from "../usdt-verify"

@[default_target]
lean_lib «TokenKit» where

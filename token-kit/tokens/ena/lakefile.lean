import Lake
open Lake DSL

/-! Properties of the deployed ENA runtime bytecode. The generic lemmas come from the shared
library of the kit (`TokenKit`, two folders up), which stands on EthLib and on usdt-verify. The
packages directory is the one of the already built usdt-verify checkout next to the kit, so EthLib
and Mathlib are not fetched or built again. -/

package «EnaVerify» where
  packagesDir := "../../../usdt-verify/.lake/packages"

require TokenKit from "../.."

@[default_target]
lean_lib «EnaVerify» where

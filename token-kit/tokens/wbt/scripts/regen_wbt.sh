#!/bin/bash
# Run every generator for WBT, in order. Like the kit's scripts/regen.sh, but the path, supply and
# readable generators are the local copies of this folder (see status.json, to_merge_into_kit),
# and gen_nomint.py writes NoMint.lean.
# Usage: bash scripts/regen_wbt.sh   (from anywhere)
# SUPERSEDED, DO NOT RUN (the ten-token audit, finding WBT-4): this local copy is merged into the kit
# (token-kit/scripts, see kit-status.json wbt_merge) and differs from it. The files of WBT are
# regenerated with the kit: bash token-kit/scripts/regen.sh tokens/wbt/config/wbt.json
echo "regen_wbt.sh is superseded (the ten-token audit, WBT-4): run bash token-kit/scripts/regen.sh tokens/wbt/config/wbt.json" >&2
exit 1
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KIT="$(cd "$ROOT/../.." && pwd)"
S="$KIT/scripts"
L="$ROOT/scripts"
CFG="$ROOT/config/wbt.json"
cd "$ROOT"
python3 "$S/gen_code.py" "$CFG"       # Code/Bytes.lean, Test/Hash.lean
python3 "$S/gen_dispatch.py" "$CFG"   # Code, Steps, Map, Complete/Dispatch
python3 "$L/fix_map_text.py" "$ROOT"  # one sentence of Map.lean that is wrong for unoptimized code
python3 "$L/gen_paths.py" "$CFG"      # Gen/B*.lean, Gen/P*.lean, Gen.lean, work/paths.json
python3 "$S/gen_loops.py" "$CFG"      # Gen/Loops.lean (name, symbol)
python3 "$L/gen_supply.py" "$CFG"     # Invariant.lean
python3 "$L/gen_readable.py" "$CFG"   # Readable.lean
python3 "$S/gen_sanity.py" "$CFG"     # Sanity/Zero.lean
python3 "$L/gen_nomint.py" "$CFG"     # NoMint.lean
python3 "$S/gen_axioms.py" "$CFG"     # Test/Axioms.lean
python3 "$S/kit_opens.py" "$ROOT"     # the `open TokenKit ...` lines

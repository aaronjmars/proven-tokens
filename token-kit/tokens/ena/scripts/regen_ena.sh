#!/bin/bash
# Local copy of the kit's scripts/regen.sh for ENA: it runs the generators of THIS folder
# (tokens/ena/scripts, copies of the kit's generators with the changes listed in status.json
# under to_merge_into_kit), in order. The files are written into the project of the token: the
# folder that holds config/<token>.json (<kit>/tokens/ena).
# Usage: regen_ena.sh <config/ena.json>   (a path, absolute or relative to the current folder)
# Then build (bash scripts/box.sh, which runs `lake build` in the project on the box) and run
# scripts/check_axioms.sh on the build log.
#
# Keys of the configuration that this script reads:
# - "generators": a list of code, dispatch, paths, loops, supply, readable, sanity, axioms that
#   limits the run to these; without it every generator runs.
# - "dispatch": {"generate": true}: gen_dispatch.py writes the dispatcher files (it does nothing
#   without the key).
# - "backing": "ether": gen_solvent.py (Solvent.lean) takes the place of gen_supply.py
#   (Invariant.lean).
# The last step, kit_opens.py, sets the `open TokenKit ...` line of every Lean file of the project
# (generated or hand-written) so the names of the shared library resolve.
# - "token_generators": scripts of the token itself (paths relative to its project), run after
#   the generators of the kit and before gen_axioms.py.
set -euo pipefail
KIT="$(cd "$(dirname "$0")/.." && pwd)"
CFG="${1:?usage: regen.sh <config/token.json>}"
CFG="$(cd "$(dirname "$CFG")" && pwd)/$(basename "$CFG")"
ROOT="$(dirname "$(dirname "$CFG")")"
S="$KIT/scripts"
cd "$ROOT"
want() {
  python3 - "$CFG" "$1" <<'PY'
import json, sys
g = json.load(open(sys.argv[1])).get('generators')
sys.exit(0 if g is None or sys.argv[2] in g else 1)
PY
}
if want code; then python3 "$S/gen_code.py" "$CFG"; fi          # Code/Bytes.lean, Test/Hash.lean
if want dispatch; then python3 "$S/gen_dispatch.py" "$CFG"; fi  # Code, Steps, Map, Enter, Spec/Dispatch, Complete/Dispatch (if dispatch.generate)
if want paths; then python3 "$S/gen_paths.py" "$CFG"; fi        # Gen/B*.lean, Gen/P*.lean, Gen.lean, paths.json
if want loops; then python3 "$S/gen_loops.py" "$CFG"; fi        # Gen/Loops.lean (functions of readonly_loops)
if want supply; then
  if grep -q '"backing": "ether"' "$CFG"; then
    python3 "$S/gen_solvent.py" "$CFG"                          # Solvent.lean (token backed by the ether of its contract)
  else
    python3 "$S/gen_supply.py" "$CFG"                           # Invariant.lean
  fi
fi
if want readable; then python3 "$S/gen_readable.py" "$CFG"; fi  # Readable.lean
if want sanity; then python3 "$S/gen_sanity.py" "$CFG"; fi      # Sanity/Zero.lean (or sanity.file)
python3 - "$CFG" <<'PY' | while IFS= read -r g; do python3 "$ROOT/$g" "$CFG"; done
import json, sys
for g in json.load(open(sys.argv[1])).get('token_generators', []):
    print(g)
PY
if want axioms; then python3 "$S/gen_axioms.py" "$CFG"; fi      # Test/Axioms.lean
python3 "$S/kit_opens.py" "$ROOT"                               # the `open TokenKit ...` lines

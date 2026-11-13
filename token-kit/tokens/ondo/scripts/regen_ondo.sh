#!/bin/bash
# Local copy of the kit's scripts/regen.sh for ONDO: it runs the generators of THIS folder
# (tokens/ondo/scripts, copies of the kit's generators with the changes listed in status.json
# under to_merge_into_kit), in order. The files are written into tokens/ondo.
# Usage: bash scripts/regen_ondo.sh [generator ...]   (in tokens/ondo; no argument = all of
# the "generators" of config/ondo.json). scripts/mk_config.py runs first and last (it reads the
# names of the generated theorems for the axioms list).
set -euo pipefail
S="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(dirname "$S")"
CFG="$ROOT/config/ondo.json"
cd "$ROOT"
python3 "$S/mk_config.py"
ONLY="$*"
want() {
  if [ -n "$ONLY" ]; then case " $ONLY " in *" $1 "*) return 0;; *) return 1;; esac; fi
  python3 - "$CFG" "$1" <<'PY'
import json, sys
g = json.load(open(sys.argv[1])).get('generators')
sys.exit(0 if g is None or sys.argv[2] in g else 1)
PY
}
if want code; then python3 "$S/gen_code.py" "$CFG"; fi
if want dispatch; then python3 "$S/gen_dispatch.py" "$CFG"; fi
if want paths; then python3 "$S/gen_paths.py" "$CFG"; fi
if want loops; then python3 "$S/gen_loops.py" "$CFG"; fi
if want supply; then python3 "$S/gen_supply.py" "$CFG"; fi
if want readable; then python3 "$S/gen_readable.py" "$CFG"; fi
if want sanity; then python3 "$S/gen_sanity.py" "$CFG"; fi
if want tokengen; then
python3 - "$CFG" <<'PY' | while IFS= read -r g; do python3 "$ROOT/$g" "$CFG"; done
import json, sys
for g in json.load(open(sys.argv[1])).get('token_generators', []):
    print(g)
PY
fi
python3 "$S/mk_config.py"
if want axioms; then python3 "$S/gen_axioms.py" "$CFG"; fi
python3 "$S/kit_opens.py" "$ROOT"

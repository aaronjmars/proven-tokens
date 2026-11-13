#!/bin/bash
# Regenerate the generated files of transferAndCall (LinkVerify/Link/Tac/BlocksA..E.lean,
# Paths.lean, Defs.lean) from the disassembly data/tac_dis.txt. gen_tac.py walks the code from
# pc 530 with a symbolic memory (tacsym.py) and writes the blocks and the paths; gen_defs.py
# writes the conditions and the names of the ends from work/tac_info.json (written by gen_tac.py).
# Then kit_opens.py sets the `open TokenKit ...` lines. Usage: bash scripts/regen_tac.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/scripts"
# gen_tac.py writes tac_info.json next to its input, so it runs on a copy in work/.
mkdir -p "$ROOT/work"
cp "$ROOT/data/tac_dis.txt" "$ROOT/work/tac_dis.txt"
python3 gen_tac.py "$ROOT/work/tac_dis.txt" "$ROOT/LinkVerify/Link/Tac"
python3 gen_defs.py "$ROOT/work/tac_info.json" "$ROOT/LinkVerify/Link/Tac"
python3 kit_opens.py "$ROOT"

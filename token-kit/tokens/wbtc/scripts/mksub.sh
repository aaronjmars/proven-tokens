#!/bin/bash
# Make a work copy of tokens/wbtc under sub/<name> (for work in parallel) and seed its build
# folder on the box from the one of tokens/wbtc, so only changed files are built again.
# The copy on the Mac is made once (a second run keeps the folder as it is and only seeds the box).
# Usage: bash scripts/mksub.sh <name>     then: TAG=<log> bash scripts/wb.sh sub/<name> [target ...]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
N="$1"
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
R=/home/user
if [ ! -d "$ROOT/sub/$N" ]; then
mkdir -p "$ROOT/sub/$N"
rsync -a --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store --exclude=sub --exclude=status.json "$ROOT/" "$ROOT/sub/$N/"
for f in lakefile.lean lake-manifest.json; do
  python3 - "$ROOT/sub/$N/$f" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
s = s.replace('"../../../usdt-verify', '"../../../../../usdt-verify').replace('"../.."', '"../../../.."')
open(p, 'w').write(s)
PY
done
fi
TGZ="$(mktemp -t wbtcsub).tgz"
(cd "$ROOT" && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store -czf "$TGZ" "sub/$N")
python3 "$VM" put "$BOX" "$TGZ" "$R/wbtc-sub-$N-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
cd $R/token-kit/tokens/wbtc && tar xzf $R/wbtc-sub-$N-push.tgz 2>/dev/null
if [ ! -d sub/$N/.lake ]; then cp -r .lake sub/$N/.lake; fi
du -sm sub/$N/.lake; df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'"

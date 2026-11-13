#!/bin/bash
# Copy tokens/ondo to the build box and build the given Lake targets there (default: the whole
# project). Only tokens/ondo is copied; KIT=1 also copies the shared kit (lakefile, TokenKit,
# scripts; no other token) and builds the library first.
# Usage: bash scripts/box.sh [target ...]   (for example: bash scripts/box.sh OndoVerify.Ondo.Gen)
# Environment: BOX (default lean-ondo), TAG (name of the log, default ondo), JOBS (the number of
# lake workers, passed as LEAN_NUM_THREADS; default 3),
# CLEAN=1 removes tokens/ondo/.lake/build first. SEQ="module ...": these modules are built
# first, one at a time. WAITS: seconds this call waits for the build (default 520); the build goes
# on detached on the box, scripts/boxw.sh waits again.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KITD="$(cd "$ROOT/../.." && pwd)"
BOX="${BOX:-lean-ondo}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-ondo}"
JOBS="${JOBS:-3}"
CLEAN="${CLEAN:-0}"
SEQ="${SEQ:-}"
R=/home/user
TGZ="$(mktemp -t ondo).tgz"
if [ "${KIT:-0}" = 1 ]; then
  (cd "$KITD/.." && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
    --exclude=statement-dumps --exclude='token-kit/tokens/*' -czf "$TGZ" token-kit)
  python3 "$VM" put "$BOX" "$TGZ" "$R/kit-push.tgz" >/dev/null
  python3 "$VM" exec "$BOX" --timeout 0 -- "export PATH=\$HOME/.elan/bin:\$PATH; mkdir -p $R/logs && cd $R && tar xzf kit-push.tgz 2>/dev/null; mkdir -p token-kit/tokens; cd token-kit && lake build > $R/logs/kit.log 2>&1; echo EXIT=\$? >> $R/logs/kit.log; tail -2 $R/logs/kit.log"
fi
(cd "$ROOT/.." && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
  -czf "$TGZ" ondo)
python3 "$VM" put "$BOX" "$TGZ" "$R/ondo-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs $R/token-kit/tokens/ondo && cd $R/token-kit/tokens && (cd ondo && ls -A | grep -v '^.lake\$' | xargs rm -rf) && tar xzf $R/ondo-push.tgz 2>/dev/null
if [ $CLEAN = 1 ]; then rm -rf ondo/.lake/build; fi
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
echo \$\$ > $R/logs/$TAG.pid
cd $R/token-kit/tokens/ondo
T0=\$(date +%s)
LAKE_JOBS=\$1; shift
: > $R/logs/$TAG.log
# the modules of SEQ one at a time first (the biggest generated files: two of them at once do
# not fit in the 8 GB of the box)
for t in $SEQ; do lake build \$t >> $R/logs/$TAG.log 2>&1 || true; done
LEAN_NUM_THREADS=\$LAKE_JOBS lake build \"\$@\" >> $R/logs/$TAG.log 2>&1
echo \"EXIT=\$?\" >> $R/logs/$TAG.log
echo \"DONE \$(( \$(date +%s) - T0 ))s\" > $R/logs/$TAG.done
B
setsid nohup bash $R/logs/$TAG.build.sh $JOBS $* >/dev/null 2>&1 </dev/null &
sleep 2
timeout ${WAITS:-520} tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null || echo STILL-RUNNING
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A14 '^error' | head -${LINES_MAX:-150}
grep -c '^error' $R/logs/$TAG.log
tail -3 $R/logs/$TAG.log; cat $R/logs/$TAG.done
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'; free -m | sed -n 2,3p
"

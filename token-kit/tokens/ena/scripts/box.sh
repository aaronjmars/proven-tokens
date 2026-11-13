#!/bin/bash
# Copy tokens/ena to the build box and build the given Lake targets there (default: the whole
# project). Only tokens/ena is copied; no other folder of the kit on the box is touched.
# Usage: bash scripts/box.sh [target ...]     (for example: bash scripts/box.sh EnaVerify.Ena.Gen)
# Environment: BOX (default lean-ethlib-build), TAG (the name of the log, default ena).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-ena}"
R=/home/user
TGZ="$(mktemp -t ena).tgz"
(cd "$ROOT/.." && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
  -czf "$TGZ" ena)
python3 "$VM" put "$BOX" "$TGZ" "$R/ena-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs && cd $R/token-kit/tokens && rm -rf ena/EnaVerify ena/scripts ena/config && tar xzf $R/ena-push.tgz 2>/dev/null
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
echo \$\$ > $R/logs/$TAG.pid
cd $R/token-kit/tokens/ena
lake build \"\$@\" > $R/logs/$TAG.log 2>&1
echo \"EXIT=\$?\" >> $R/logs/$TAG.log
B
setsid nohup bash $R/logs/$TAG.build.sh $* >/dev/null 2>&1 </dev/null &
sleep 2
tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A12 '^error' | head -${LINES_MAX:-120}
tail -3 $R/logs/$TAG.log
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'
"

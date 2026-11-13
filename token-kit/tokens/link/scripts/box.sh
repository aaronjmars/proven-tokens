#!/bin/bash
# Copy tokens/link to the build box and build the given Lake targets there (default: the whole
# project). Only tokens/link is copied; no other folder of the kit on the box is touched.
# Usage: bash scripts/box.sh [target ...]     (for example: bash scripts/box.sh LinkVerify.Usde.Gen)
# Environment: BOX (default lean-ethlib-build), TAG (the name of the log, default link).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-link}"
R=/home/user
TGZ="$(mktemp -t link).tgz"
(cd "$ROOT/.." && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store --exclude=reenter --exclude=tac --exclude=callin --exclude=rd --exclude=wit --exclude=rd2 \
  -czf "$TGZ" link)
python3 "$VM" put "$BOX" "$TGZ" "$R/link-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs && cd $R/token-kit/tokens && true && tar xzf $R/link-push.tgz 2>/dev/null
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
echo \$\$ > $R/logs/$TAG.pid
cd $R/token-kit/tokens/link
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

#!/bin/bash
# Copy one work folder of tokens/link (tac, callin, reenter) to the build box and build the given
# Lake targets there. Only that folder is copied.
# Usage: TAG=<log name> bash scripts/boxsub.sh <folder> [target ...]
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SUB="$1"; shift
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-link-$SUB}"
R=/home/user
TGZ="$(mktemp -t linksub).tgz"
(cd "$ROOT" && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
  -czf "$TGZ" "$SUB")
python3 "$VM" put "$BOX" "$TGZ" "$R/link-$SUB-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs && cd $R/token-kit/tokens/link && tar xzf $R/link-$SUB-push.tgz 2>/dev/null
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
echo \$\$ > $R/logs/$TAG.pid
cd $R/token-kit/tokens/link/$SUB
lake build \"\$@\" > $R/logs/$TAG.log 2>&1
echo \"EXIT=\$?\" >> $R/logs/$TAG.log
B
setsid nohup bash $R/logs/$TAG.build.sh $* >/dev/null 2>&1 </dev/null &
sleep 2
tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A${CTX:-25} '^error' | head -${LINES_MAX:-160}
tail -3 $R/logs/$TAG.log
free -m | awk 'NR==2{print \"mem available MB:\", \$7}'
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'
"

#!/bin/bash
# Copy tokens/sky and the kit files that SKY added (TokenKit/Evm/Env08.lean and the like, named
# in KITFILES) to the build box, and build the given Lake targets there (default: the project).
# Usage: bash scripts/box.sh [target ...]
# Environment: BOX (default lean-ethlib-build), TAG (the name of the log, default sky).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
KIT="$(cd "$ROOT/../.." && pwd)"
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-sky}"
KITFILES="${KITFILES:-TokenKit/Evm/Env08.lean TokenKit/Evm/SupplyUnchecked.lean TokenKit/Evm/TopByte.lean TokenKit/Evm/Tail.lean}"
R=/home/user
TGZ="$(mktemp -t sky).tgz"
(cd "$KIT" && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
  -czf "$TGZ" tokens/sky $KITFILES)
python3 "$VM" put "$BOX" "$TGZ" "$R/sky-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs && cd $R/token-kit && rm -rf tokens/sky/SkyVerify tokens/sky/scripts tokens/sky/config && tar xzf $R/sky-push.tgz 2>/dev/null
for m in ${KITIMPORTS:-TokenKit.Evm.Env08 TokenKit.Evm.SupplyUnchecked TokenKit.Evm.TopByte TokenKit.Evm.Tail}; do grep -q \"^import \$m\$\" TokenKit.lean || echo \"import \$m\" >> TokenKit.lean; done
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
echo \$\$ > $R/logs/$TAG.pid
cd $R/token-kit/tokens/sky
lake build \"\$@\" > $R/logs/$TAG.log 2>&1
echo \"EXIT=\$?\" >> $R/logs/$TAG.log
B
setsid nohup bash $R/logs/$TAG.build.sh $* >/dev/null 2>&1 </dev/null &
sleep 2
tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A${CTX:-14} '^error' | head -${LINES_MAX:-120}
tail -3 $R/logs/$TAG.log
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'
"

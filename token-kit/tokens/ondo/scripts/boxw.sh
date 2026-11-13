#!/bin/bash
# Wait again for the detached build that scripts/box.sh started on the box, then print the same
# summary. Usage: bash scripts/boxw.sh   (environment: BOX, TAG, WAITS as in box.sh)
set -euo pipefail
BOX="${BOX:-lean-ondo}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-ondo}"
R=/home/user
python3 "$VM" exec "$BOX" --timeout 0 -- "
timeout ${WAITS:-520} tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null || echo STILL-RUNNING
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A14 '^error' | head -${LINES_MAX:-150}
grep -c '^error' $R/logs/$TAG.log
grep -c '^✔' $R/logs/$TAG.log
tail -3 $R/logs/$TAG.log | cut -c1-300; cat $R/logs/$TAG.done 2>/dev/null
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'; free -m | sed -n 2,3p
"

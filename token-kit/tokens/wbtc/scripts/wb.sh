#!/bin/bash
# Copy tokens/wbtc (or one work folder under sub/) to the build box and build Lake targets there,
# one WBTC build at a time (a lock file on the box) and never when the box is short of memory
# (another agent builds on the same 8 GB box).
# Usage: TAG=<log name> bash scripts/wb.sh <folder> [target ...]
#   <folder> is `.` for tokens/wbtc itself or `sub/<name>` for a work copy.
# Environment: BOX (default lean-ethlib-build), TAG (log name, default wb), THREADS (Lean
# processes at once, default 3), MEM_CAP_MB (memory cap of one Lean process, default 2600; the
# watchdog stops a process of this build above it), CTX (lines shown after an error, default 25), LINES_MAX.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SUB="$1"; shift
BOX="${BOX:-lean-ethlib-build}"
VM="${VM:?set VM to your E2B box tool}"
TAG="${TAG:-wb}"
THREADS="${THREADS:-3}"
MEM_CAP_MB="${MEM_CAP_MB:-2600}"
R=/home/user
TGZ="$(mktemp -t wbtcwb).tgz"
if [ "$SUB" = "." ]; then
  (cd "$ROOT/.." && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
    --exclude=sub -czf "$TGZ" wbtc)
  UNPACK="cd $R/token-kit/tokens && tar xzf $R/wbtc-$TAG-push.tgz 2>/dev/null"
  DIR="$R/token-kit/tokens/wbtc"
else
  (cd "$ROOT" && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store \
    -czf "$TGZ" "$SUB")
  UNPACK="cd $R/token-kit/tokens/wbtc && tar xzf $R/wbtc-$TAG-push.tgz 2>/dev/null"
  DIR="$R/token-kit/tokens/wbtc/$SUB"
fi
python3 "$VM" put "$BOX" "$TGZ" "$R/wbtc-$TAG-push.tgz" >/dev/null
rm -f "$TGZ"
python3 "$VM" exec "$BOX" --timeout 0 -- "
mkdir -p $R/logs && $UNPACK
rm -f $R/wbtc-$TAG-push.tgz
cat > $R/logs/$TAG.build.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
export LEAN_NUM_THREADS=$THREADS
echo \$\$ > $R/logs/$TAG.pid
cd $DIR
exec 9>$R/logs/wbtc.lock
flock 9
: > $R/logs/$TAG.log
n=0
while [ \$(free -m | awk 'NR==2{print \$7}') -lt 3000 ] && [ \$n -lt 240 ]; do
  p=\$(pgrep -x lake | head -1)
  echo \"waiting for memory (other build pid \$p)\" >> $R/logs/$TAG.log
  if [ -n \"\$p\" ]; then timeout 600 tail --pid=\$p -f /dev/null; else sleep 30; fi
  n=\$((n+1))
done
: > $R/logs/$TAG.samp
: > $R/logs/$TAG.wd
# every 4 s: a sample (Lean processes, memory available) and the watchdog: a Lean process of THIS
# build (a descendant of this script, never a process of another build) that holds more than
# MEM_CAP_MB of memory (resident + swapped) is stopped, so one file cannot take the whole box.
( while kill -0 \$\$ 2>/dev/null; do
    echo \"\$(pgrep -x lean | wc -l) \$(free -m | awk 'NR==2{print \$7}')\" >> $R/logs/$TAG.samp
    todo=\$\$; mine=
    while [ -n \"\$todo\" ]; do
      next=
      for q in \$todo; do c=\$(pgrep -P \$q | tr '\\n' ' '); mine=\"\$mine \$c\"; next=\"\$next \$c\"; done
      todo=\$(echo \$next)
    done
    for q in \$mine; do
      [ \"\$(cat /proc/\$q/comm 2>/dev/null)\" = lean ] || continue
      kb=\$(awk '/^VmRSS|^VmSwap/{s+=\$2} END{print s+0}' /proc/\$q/status 2>/dev/null)
      if [ \"\${kb:-0}\" -gt \$(($MEM_CAP_MB * 1024)) ]; then
        echo \"WATCHDOG: stopped Lean process \$q of this build at \$((kb / 1024)) MB (cap $MEM_CAP_MB MB): \$(tr '\\0' ' ' < /proc/\$q/cmdline | grep -o '[A-Za-z0-9_/]*\\.lean' | head -1)\" >> $R/logs/$TAG.wd
        kill -9 \$q
      fi
    done
    sleep 4
  done ) &
lake build \"\$@\" >> $R/logs/$TAG.log 2>&1
echo \"EXIT=\$?\" >> $R/logs/$TAG.log
B
setsid nohup bash $R/logs/$TAG.build.sh $* >/dev/null 2>&1 </dev/null &
sleep 2
tail --pid=\$(cat $R/logs/$TAG.pid) -f /dev/null
grep -v 'module system\|^⚠\|^✔\|Replayed\|^warning: .*UsdtVerify\|^warning: .*EthLib' $R/logs/$TAG.log | grep -n -A${CTX:-25} '^error' | head -${LINES_MAX:-160}
tail -3 $R/logs/$TAG.log
cat $R/logs/$TAG.wd
sort -n -k1 $R/logs/$TAG.samp | tail -1 | awk '{print \"most Lean processes at once:\", \$1}'
sort -n -k2 $R/logs/$TAG.samp | head -1 | awk '{print \"least memory available MB:\", \$2}'
free -m | awk 'NR==2{print \"mem available MB:\", \$7}'
df -m / | tail -1 | awk '{print \"disk free MB:\", \$4}'
"

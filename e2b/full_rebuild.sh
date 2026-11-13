#!/bin/bash
# Run on the Mac: makes a fresh E2B box (lean-verify), pinned base build, pushes the kit, runs
# verify_all.sh there (full clean rebuild of every token), fetches the logs to logs/ (one
# <token>.log and <token>.axioms per token, plus kit.log; they replace the logs there).
# About 2 hours. The box is left running at the end: remove it with vm.py rm lean-verify.
set -uo pipefail
V="python3 ${VM:?set VM to your E2B box tool}"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
BOX=lean-verify
OUT=$REPO/logs
say() { echo "[$(date +%T)] $*"; }
say "create box"; $V create --name $BOX --template lean-ethlib --timeout 360 || exit 1
$V put $BOX $REPO/e2b/remote_build.sh /home/user/remote_build.sh || exit 1
$V put $BOX $REPO/e2b/verify_all.sh /home/user/verify_all.sh || exit 1
say "base build (pinned usdt-verify)"
$V exec $BOX --timeout 0 -- 'cd /home/user && git clone --quiet https://github.com/Giulio2002/usdt-verify && git -C usdt-verify checkout -q d0e684c5f20461b5816fa0a806e3888500535a51 && git -C usdt-verify rev-parse HEAD && bash remote_build.sh; tail -6 build.log; grep -h -A3 -i ethlib usdt-verify/lake-manifest.json | grep rev'
TMP=$(mktemp -d); TGZ=$TMP/token-kit.tgz
( cd $REPO && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ --exclude=.DS_Store --exclude=statement-dumps -czf $TGZ token-kit )
say "push kit $(du -h $TGZ | cut -f1)"; $V put $BOX $TGZ /home/user/token-kit.tgz || exit 1
$V exec $BOX --timeout 0 -- 'cd /home/user && tar xzf token-kit.tgz && ls token-kit/tokens | wc -l && df -m / | tail -1' || exit 1
$V exec $BOX --timeout 0 -- 'cd /home/user; setsid nohup bash verify_all.sh >/dev/null 2>&1 </dev/null & sleep 5; cat /home/user/logs/verify/pid'
say "verify_all started"
for i in $(seq 1 200); do
  $V exec $BOX --timeout 0 -- 'tail --pid=$(cat /home/user/logs/verify/pid) -f /dev/null; ls /home/user/logs/verify/' >/dev/null 2>&1
  if $V exec $BOX -- 'test -f /home/user/logs/verify/done' >/dev/null 2>&1; then break; fi
  say "wait dropped, re-attach ($i)"; sleep 20
done
say "fetch logs"
mkdir -p $OUT
$V exec $BOX -- 'cd /home/user/logs && tar czf verify.tgz verify && cat verify/done && for f in verify/*.log; do echo "$f $(tail -1 $f) $(grep -c "^error" $f)"; done; for f in verify/*.axioms; do echo "$f $(grep -E "theorems checked|AXRC|only standard" $f | tr "\n" " ")"; done; df -m / | tail -1'
$V get $BOX /home/user/logs/verify.tgz $TMP/verify.tgz && tar xzf $TMP/verify.tgz -C $OUT --strip-components 1 --exclude 'verify/done' --exclude 'verify/pid'
say "ALL DONE"

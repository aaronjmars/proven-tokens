#!/bin/bash
# Copy the kit to the build box and build the shared library and the given tokens there, then run
# check_axioms.sh on each build log. Lean is not needed on this machine.
# Usage: build_box.sh [--clean] <token> [<token> ...]      (for example: build_box.sh shib qnt)
#   --clean  removes the build outputs of the kit library and of the given tokens first.
# Environment: BOX (default lean-ethlib-build), REMOTE (default /home/user), VM (the vm.py of the
# e2b skill). The box must hold a built usdt-verify checkout at $REMOTE/usdt-verify: the lakefiles
# use ../usdt-verify (kit) and ../../../usdt-verify (tokens), and its packages directory, so EthLib
# and Mathlib are not fetched or built again.
# The build runs detached on the box (pid file and logs in $REMOTE/logs); this script waits for it.
set -euo pipefail
KIT="$(cd "$(dirname "$0")/.." && pwd)"
BOX="${BOX:-lean-ethlib-build}"
REMOTE="${REMOTE:-/home/user}"
VM="${VM:?set VM to your E2B box tool}"
CLEAN=0
if [ "${1:-}" = "--clean" ]; then CLEAN=1; shift; fi
TOKENS="$*"
TGZ="$(mktemp -t tokenkit).tgz"
(cd "$(dirname "$KIT")" && COPYFILE_DISABLE=1 tar --exclude=.lake --exclude=__pycache__ \
  --exclude=.DS_Store --exclude=statement-dumps -czf "$TGZ" "$(basename "$KIT")")
python3 "$VM" put "$BOX" "$TGZ" "$REMOTE/token-kit.tgz"
python3 "$VM" exec "$BOX" --timeout 0 -- "
cd $REMOTE && tar xzf token-kit.tgz 2>/dev/null; mkdir -p logs
cat > $REMOTE/logs/kitbuild.sh <<'B'
#!/bin/bash
export PATH=\$HOME/.elan/bin:\$PATH
R=\$1; CLEAN=\$2; shift 2
echo \$\$ > \$R/logs/kitbuild.pid
one() {  # <dir> <tag>
  cd \"\$1\" || return 1
  if [ \$CLEAN = 1 ]; then rm -rf .lake/build; fi
  lake build > \$R/logs/\$2.log 2>&1
  echo \"EXIT=\$?\" >> \$R/logs/\$2.log
}
one \$R/token-kit kit
for t in \"\$@\"; do one \$R/token-kit/tokens/\$t \$t; done
B
setsid nohup bash $REMOTE/logs/kitbuild.sh $REMOTE $CLEAN $TOKENS >/dev/null 2>&1 </dev/null &
sleep 2
tail --pid=\$(cat $REMOTE/logs/kitbuild.pid) -f /dev/null
for t in kit $TOKENS; do
  echo \"== \$t: \$(tail -2 $REMOTE/logs/\$t.log | tr '\n' ' ')\"
  grep -n '^error' $REMOTE/logs/\$t.log | head -20
  if [ \$t != kit ]; then bash $REMOTE/token-kit/scripts/check_axioms.sh $REMOTE/logs/\$t.log | grep -v '^ '; fi
done
df -m / | tail -1
"

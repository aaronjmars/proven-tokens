#!/bin/bash
# Fetch the build log of the box into logs/<token>.log of the repo and print its errors in short form (first lines only).
# Usage: bash scripts/errs.sh [lines of context, default 0]
cd "$(dirname "$0")/.."
LOG=../../../logs/${TAG:-ondo}.log
python3 "${VM:?set VM to your E2B box tool}" get "${BOX:-lean-ondo}" /home/user/logs/${TAG:-ondo}.log "$LOG" >/dev/null
grep -a -A${1:-0} '^error' "$LOG" | cut -c1-${COLS:-300} | head -${LINES_MAX:-80}
echo "errors: $(grep -a -c '^error' "$LOG")"; grep -a 'Built\|✖\|EXIT' "$LOG" | grep -v 'Gen\.' | tail -6

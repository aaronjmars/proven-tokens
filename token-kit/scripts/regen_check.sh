#!/bin/bash
# Check that the generators still write every token as it is: copy each project of tokens/ (no
# .lake) to a temporary folder, run scripts/regen.sh on the copy, and compare with the original.
# Usage: bash scripts/regen_check.sh [token ...]   (default: every folder of tokens/)
# Prints one line per token (SAME or DIFF with the files that differ) and N/N at the end.
set -uo pipefail
KIT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d 2>/dev/null || mktemp -d -t regencheck)"   # Linux, then macOS
if [ "$#" -gt 0 ]; then TOKS="$*"; else TOKS="$(ls "$KIT/tokens")"; fi
n=0
same=0
for t in $TOKS; do
  [ -f "$KIT/tokens/$t/config/$t.json" ] || continue
  n=$((n + 1))
  mkdir -p "$TMP/tokens"
  (cd "$KIT/tokens" && tar --exclude=.lake --exclude=__pycache__ -cf - "$t") | (cd "$TMP/tokens" && tar xf -)
  if bash "$KIT/scripts/regen.sh" "$TMP/tokens/$t/config/$t.json" >"$TMP/$t.log" 2>&1; then
    d="$(diff -rq -x .lake -x __pycache__ "$KIT/tokens/$t" "$TMP/tokens/$t")"
    if [ -z "$d" ]; then
      same=$((same + 1))
      echo "SAME $t"
    else
      echo "DIFF $t"
      echo "$d" | sed 's/^/  /' | head -20
    fi
  else
    echo "FAIL $t (regen.sh stopped: $(tail -1 "$TMP/$t.log"))"
  fi
done
echo "$same/$n identical"
rm -rf "$TMP"

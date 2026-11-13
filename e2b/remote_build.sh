#!/bin/bash
# Runs inside the E2B box: fetch usdt-verify (pinned EthLib), build, record time + peak memory.
export PATH="$HOME/.elan/bin:$PATH"
cd "$HOME" || exit 1
L=$HOME/build.log
echo $$ >"$HOME/build.pid"
{
  date -u +"START %FT%TZ"
  nproc
  free -m | sed -n 2p
  sudo swapoff /swapfile 2>/dev/null; sudo rm -f /swapfile
  if sudo fallocate -l 3G /swapfile && sudo chmod 600 /swapfile && sudo mkswap /swapfile >/dev/null && sudo swapon /swapfile; then
    echo "swap on"
  else
    echo "swap FAILED"
  fi
  [ -d usdt-verify ] || git clone --quiet https://github.com/Giulio2002/usdt-verify
  cd usdt-verify || exit 1
  (while true; do
    echo "MEM $(date -u +%T) $(free -m | awk 'NR==2{print $3} NR==3{print "swap",$3}' | tr '\n' ' ') disk $(df -m / | awk 'NR==2{print $3}')"
    sleep 60
  done) &
  S=$!
  T0=$(date +%s)
  lake exe cache get 2>&1 | tail -5
  echo "CACHE_DONE $(($(date +%s) - T0))s"
  lake build 2>&1 | grep -v '^✔' | tail -200
  RC=${PIPESTATUS[0]}
  kill $S
  echo "BUILD_RC=$RC ELAPSED $(($(date +%s) - T0))s"
  du -sm .lake 2>/dev/null
  date -u +"DONE %FT%TZ"
} >>"$L" 2>&1

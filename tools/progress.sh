#!/bin/bash
# Progress of a `lake build -v` log: modules built, rate over the last hour, lower-bound ETA.
# Usage: tools/progress.sh [out.log]   (default: the baseline job log)
LOG=${1:-/home/alastair/claude-compute/cfsg-baseline-1102a/out.log}
[ -f "$LOG" ] || { echo "no log at $LOG"; exit 1; }
echo "log: $LOG  ($(du -h "$LOG" | cut -f1))"
grep -E '^===' "$LOG" | tail -5
total=$(tr '\r' '\n' < "$LOG" | grep -oE '\[[0-9]+/[0-9]+\]' | tail -1 | sed 's/.*\///; s/\]//')
built=$(find "$(dirname "$0")/../.lake/build/lib/lean" -name '*.olean' 2>/dev/null | wc -l)
errs=$(tr '\r' '\n' < "$LOG" | grep -cE '^✖|error:')
echo "repo oleans built: $built   (lake job counter total: ${total:-?})   error lines: $errs"
# rate over the last hour from file mtime snapshots kept in /tmp
snap=/tmp/cfsg-progress-$(id -u).snap
now=$(date +%s)
if [ -f "$snap" ]; then
  read -r t0 b0 < "$snap"
  dt=$((now - t0))
  if [ "$dt" -gt 60 ]; then
    rate=$(( (built - b0) * 3600 / dt ))
    echo "rate since last call ($((dt/60)) min ago): $rate oleans/hour"
    if [ -n "$total" ] && [ "$rate" -gt 0 ]; then
      echo "ETA at this rate for 226885 modules: $(( (226885 - built) / rate )) h"
    fi
  fi
fi
echo "$now $built" > "$snap"
free -g | sed -n 2p
tmux has-session -t =cfsg-baseline-1102a 2>/dev/null && echo "tmux job: running" || echo "tmux job: not running (status: $(cat /home/alastair/claude-compute/cfsg-baseline-1102a/status 2>/dev/null))"

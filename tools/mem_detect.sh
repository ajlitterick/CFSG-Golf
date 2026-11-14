#!/bin/bash
# Detector pipeline: build under the memory guard, report, re-measure flagged modules alone,
# write the findings file the fixer agent consumes.   Run from anywhere; uses the repo root.
#   tools/mem_detect.sh [--no-build] [--top K] [--ram-gb N] [-- <lake build args>]
#     --no-build   skip the full build; analyse the newest .cache/membench/build-*.jsonl
#     --top K      re-measure at most K flagged modules in isolation (default 5)
#     --ram-gb N   memory budget used in the advice section (default: MemTotal)
# Output: .cache/membench/findings.json  (schema: tools/MEMORY_AGENTS.md)
set -u
cd "$(dirname "$0")/.." || exit 1
BUILD=1; TOP=5; RAM=(); ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) BUILD=0;;
    --top) TOP=$2; shift;;
    --ram-gb) RAM=(--ram-gb "$2"); shift;;
    --) shift; ARGS=("$@"); break;;
    *) echo "unknown option $1"; exit 2;;
  esac
  shift
done
D=.cache/membench; mkdir -p "$D"
if [ $BUILD -eq 1 ]; then
  python3 -I tools/mem_watch.py run --guard --interval 1 --label build -- lake build "${ARGS[@]}"
  echo "lake build exit: $?"
fi
LOG=$(ls -t "$D"/build-*.jsonl 2>/dev/null | head -1)
[ -n "$LOG" ] || { echo "no build log in $D"; exit 1; }
python3 -I tools/mem_report.py "$LOG" "${RAM[@]}" --json "$D/findings.json" > "$D/report.txt"
echo "report: $D/report.txt"
# isolated re-measurement of the flagged modules (needs their imports built)
mapfile -t FLAGGED < <(python3 -I -c '
import json,sys
d=json.load(open(sys.argv[1]))
for m in [m for m in d["modules"] if m["flagged"]][:int(sys.argv[2])]: print(m["module"])
' "$D/findings.json" "$TOP")
for m in "${FLAGGED[@]}"; do
  echo "== isolated: $m"
  python3 -I tools/mem_watch.py module "$m" --threads 1 --interval 1 | tail -1
done
if [ ${#FLAGGED[@]} -gt 0 ]; then
  python3 -I tools/mem_report.py "$LOG" "$D"/module-*.jsonl "${RAM[@]}" --json "$D/findings.json" > "$D/report.txt"
fi
echo "findings: $D/findings.json  ($(python3 -I -c 'import json;d=json.load(open("'"$D"'/findings.json"));print(d["summary"]["modules_flagged"],"flagged")'))"

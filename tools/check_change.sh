#!/bin/bash
# Verify a golf branch against the built baseline tree.
#   tools/check_change.sh [--allow-interface] [--no-downstream] [range]
# range defaults to main...HEAD.  Steps:
#   1. list changed Lean modules (and flag non-Lean data edits, which Lake does not trace);
#   2. snapshot artefact hashes, `lake build` the changed modules, snapshot again, classify
#      (public-unchanged / private-changed / public-changed); refuse public changes unless
#      --allow-interface;
#   3. lake build +Comparator.Solution (downstream), reporting how many modules rebuilt;
#   4. tools/verify_final.sh (axioms + statement);
#   5. score diff against tools/baseline.json.
# Serialised with flock so only one build runs in this checkout at a time.
set -u
cd "$(dirname "$0")/.." || exit 1
ALLOW=0; DOWN=1; RANGE="main...HEAD"
for a in "$@"; do
  case "$a" in
    --allow-interface) ALLOW=1;;
    --no-downstream) DOWN=0;;
    *) RANGE="$a";;
  esac
done
J=${J:-3}
LOCK=/home/alastair/claude-compute/cfsg-build.lock
exec 9>"$LOCK"; flock 9 || exit 1
R=report.md; : > $R
log() { echo "$*" | tee -a $R; }

log "# check_change $RANGE  ($(git rev-parse --short HEAD), $(date -Is))"
mapfile -t LEAN < <(git diff --name-only "$RANGE" -- '*.lean' | grep -E '^(CFSG|Certificates|Comparator)/' )
mapfile -t DATA < <(git diff --name-only "$RANGE" | grep -vE '\.lean$|^tools/|^\.github/|^docs/' )
MODS=()
for f in "${LEAN[@]}"; do [ -f "$f" ] && MODS+=("${f%.lean}") ; done
MODS=("${MODS[@]//\//.}")
log "changed Lean modules: ${#MODS[@]}; deleted/renamed files: $(git diff --name-only --diff-filter=D "$RANGE" -- '*.lean' | wc -l)"
if [ ${#DATA[@]} -gt 0 ]; then
  log "WARNING: non-Lean files changed (Lake does not trace these; consumers rebuilt with -H):"
  printf '  %s\n' "${DATA[@]}" | tee -a $R
  REHASH=-H
else
  REHASH=
fi

if [ ${#MODS[@]} -gt 0 ]; then
  python3 -I tools/olean_snapshot.py snap --modules "${MODS[@]}" --out /tmp/snap_before.json >/dev/null
  log "## building changed modules"
  TARGETS=(); for m in "${MODS[@]}"; do TARGETS+=("+$m"); done
  LEAN_NUM_THREADS=$J lake build $REHASH "${TARGETS[@]}" 2>&1 | tail -20 | tee -a $R
  rc=${PIPESTATUS[0]}
  [ "$rc" -ne 0 ] && { log "FAIL: changed modules do not build"; exit 1; }
  python3 -I tools/olean_snapshot.py snap --modules "${MODS[@]}" --out /tmp/snap_after.json >/dev/null
  log "## interface classification"
  python3 -I tools/olean_snapshot.py diff /tmp/snap_before.json /tmp/snap_after.json | tee -a $R
  cls=${PIPESTATUS[0]}
  if [ "$cls" -eq 2 ] && [ $ALLOW -eq 0 ]; then
    log "REFUSED: public interface changed; rerun with --allow-interface to rebuild downstream"
    exit 2
  fi
fi

if [ $DOWN -eq 1 ]; then
  log "## downstream build (+Comparator.Solution)"
  t0=$(date +%s)
  LEAN_NUM_THREADS=$J lake build +Comparator.Solution -v > /tmp/downstream.log 2>&1
  rc=$?
  log "rebuilt modules: $(grep -cE '^✔ \[[0-9]+/[0-9]+\] Built' /tmp/downstream.log)   wall: $(( $(date +%s) - t0 )) s   exit: $rc"
  [ "$rc" -ne 0 ] && { grep -E '^✖|error:' /tmp/downstream.log | head -20 | tee -a $R; log "FAIL: downstream build"; exit 1; }
  log "## final checks"
  bash tools/verify_final.sh 2>&1 | tail -8 | tee -a $R
  grep -q 'VERIFY_FINAL: PASS' $R || { log "FAIL: verify_final"; exit 1; }
fi

log "## score"
python3 -I tools/cfsg_score.py --diff tools/baseline.json 2>&1 | sed -n '/score vs baseline/,$p' | tee -a $R
log "CHECK_CHANGE: PASS (report in $R)"

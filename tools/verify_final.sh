#!/bin/bash
# Final checks on a built tree: axioms of the final theorem and its statement.
# Exit 0 only if both pass.  Run from the repository root.
set -u
cd "$(dirname "$0")/.." || exit 1
ok=0
echo "--- axioms"
ax=$(lake env lean tools/axiom_check.lean 2>&1)
echo "$ax"
allowed=$(python3 -I -c 'import json,sys; print(" ".join(sorted(json.load(open("comparator.json")).get("permitted_axioms", json.load(open("comparator.json")).get("allowed_axioms", [])))))' 2>/dev/null)
got=$(echo "$ax" | grep -oE 'depends on axioms: \[.*\]' | sed 's/.*\[//; s/\]//; s/,/ /g' | tr -s ' ' '\n' | sort | tr '\n' ' ' | sed 's/ $//')
echo "allowed: $allowed"
echo "got:     $got"
if echo "$ax" | grep -q 'sorryAx'; then echo "FAIL: sorryAx"; ok=1; fi
for a in $got; do
  case " $allowed " in *" $a "*) ;; *) echo "FAIL: axiom $a not permitted"; ok=1;; esac
done
echo "--- statement"
st=$(lake env lean tools/statement_check.lean 2>&1)
echo "$st"
echo "$st" | grep -q 'statement OK' || { echo "FAIL: statement check"; ok=1; }
echo "--- challenge text"
norm() { grep -vE '^(public |meta )?import|^$' "$1" | sed '/:=/,$d'; }
if diff <(norm Comparator/Challenge.lean) <(norm Comparator/Solution.lean) >/dev/null; then
  echo "Solution.lean header matches Challenge.lean"
else
  echo "FAIL: Solution.lean header differs from Challenge.lean"; ok=1
fi
[ $ok -eq 0 ] && echo "VERIFY_FINAL: PASS" || echo "VERIFY_FINAL: FAIL"
exit $ok

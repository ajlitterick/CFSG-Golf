## What this changes

<!-- One paragraph: what was removed or shortened, and why it is a genuine shortening
     (dead code, duplicate layer, shorter mathematics), not repackaging. -->

## Score

Output of `python3 -I tools/cfsg_score.py --diff tools/baseline.json`:

```
(paste)
```

- [ ] `tools/baseline.json` updated in this PR

## Verification

Output of `tools/check_change.sh` (`report.md`):

```
(paste)
```

- [ ] changed modules classified (public-unchanged / private-changed / public-changed)
- [ ] `lake build +Comparator.Solution` green; rebuilt module count and wall time stated
- [ ] `#print axioms CFSGComparator.classification` is within `propext`, `Quot.sound`, `Classical.choice`
- [ ] statement check passes (`VERIFY_FINAL: PASS`)
- [ ] for interface changes: full rebuild in the second checkout is green

## Notes

<!-- Anything a reviewer should know: mathematical justification for a re-routing,
     modules left alone and why, follow-ups this unlocks. -->

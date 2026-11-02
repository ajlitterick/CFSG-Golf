"""Inventory of the Input/Holds hypothesis-threading layer.

    python3 -I tools/inputs_inventory.py [--repo .] [--out inputs.tsv] [--dirs CFSG/LocalAnalysis ...]

Finds every `def NAME : Prop :=` whose NAME ends in Input/Known/Hyp/Statement/Cited (the
generated "input" props), the theorem(s) proving it (`theorem X : NAME :=`, typically
`name_holds`), whether that theorem takes explicit arguments, and how many files mention NAME
outside its defining file and its holds file.

Output TSV columns:
  name, def file, #antecedent arrows in the def body (rough: count of 'Input ->' style
  antecedents on the first lines), holds theorem name, holds file, holds-has-args, #other files
  referencing, class
where class is one of
  orphan      no holds theorem, no other reference
  proved-only holds theorem exists, no other reference
  used-unproved referenced elsewhere but no holds theorem found (a genuine hypothesis)
  live        holds theorem and references elsewhere
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict

DEF_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?def\s+([A-Za-z0-9_'.]+(?:Input|Known|Hyp|Statement|Cited))\s*(?:\([^)]*\)\s*)*:\s*Prop\s*:=", re.M)
THM_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:public\s+)?theorem\s+([A-Za-z0-9_'.]+)\s*((?:\([^)]*\)\s*|\{[^}]*\}\s*|\[[^\]]*\]\s*)*):\s*([A-Za-z0-9_'.]+(?:Input|Known|Hyp|Statement|Cited))\s*:=", re.M)
WORD = re.compile(r"[A-Za-z0-9_'.]+")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--out", default="inputs.tsv")
    ap.add_argument("--dirs", nargs="*", default=["CFSG"])
    a = ap.parse_args()
    defs: dict[str, tuple[str, int]] = {}
    holds: dict[str, list[tuple[str, str, bool]]] = defaultdict(list)
    files: list[tuple[str, str]] = []
    for d in a.dirs:
        for dp, _dn, fn in os.walk(os.path.join(a.repo, d)):
            for f in fn:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    with open(p, encoding="utf-8", errors="replace") as fh:
                        text = fh.read()
                    rel = os.path.relpath(p, a.repo)
                    files.append((rel, text))
                    for m in DEF_RE.finditer(text):
                        name = m.group(1).split(".")[-1]
                        # count antecedents: lines after := up to the first ∀ that end with '→'
                        tail = text[m.end():m.end() + 4000]
                        pre = tail.split("∀", 1)[0]
                        arrows = pre.count("→")
                        defs[name] = (rel, arrows)
                    for m in THM_RE.finditer(text):
                        tname, binders, target = m.group(1), m.group(2), m.group(3).split(".")[-1]
                        has_args = bool(re.search(r"\(", binders))
                        holds[target].append((tname, rel, has_args))
    # reference counts: files mentioning the bare name (word match) other than def/holds files
    refs: dict[str, set[str]] = defaultdict(set)
    names = set(defs)
    for rel, text in files:
        for w in set(WORD.findall(text)):
            w = w.split(".")[-1]
            if w in names:
                refs[w].add(rel)
    rows = []
    cls_count = defaultdict(int)
    for name, (dfile, arrows) in defs.items():
        hs = holds.get(name, [])
        hfiles = {h[1] for h in hs}
        other = refs[name] - {dfile} - hfiles
        if hs and other:
            cls = "live"
        elif hs:
            cls = "proved-only"
        elif other:
            cls = "used-unproved"
        else:
            cls = "orphan"
        cls_count[cls] += 1
        h0 = hs[0] if hs else ("", "", "")
        rows.append((name, dfile, arrows, h0[0], h0[1], h0[2] if hs else "", len(other), cls))
    rows.sort(key=lambda r: (-r[6], r[0]))
    with open(a.out, "w") as fh:
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")
    print(f"input props: {len(defs)}   " + "  ".join(f"{k}: {v}" for k, v in sorted(cls_count.items())))
    argfree = sum(1 for r in rows if r[3] and r[5] is False)
    print(f"holds theorems found: {sum(1 for r in rows if r[3])}  argument-free: {argfree}")
    print(f"antecedent arrows: total {sum(r[2] for r in rows)}, max {max((r[2] for r in rows), default=0)}")
    print("most referenced:")
    for r in rows[:15]:
        print(f"  {r[6]:5d} files  {r[0]}  ({r[7]})")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

"""Classify the Finite4 copies in CFSG/GH74/QTGen4/DCopy against their originals.

    python3 -I tools/f4pairs.py [--repo .] [--out f4pairs.tsv] [--show MODULE]

For each DCopy file, the original is the file with the `CFSG/GH74/QTGen4/DCopy/` prefix
removed.  The copy is normalised (strip the DCopy namespace prefix, `[CFSG.GH74.QTGen4.Finite4 G]`
-> `[Finite G]`, drop `_F4` suffixes) and compared with the original:

  identical   normalised copy == original (modulo whitespace)
  subset      every non-import line of the normalised copy occurs in the original
              (copy imports the original and restates a subset)
  drift       lines in the copy that are not in the original (count reported)
  no-original the original path does not exist

Output TSV: class, copy path, original path, #copy lines, #lines not in original, uses gen4.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import Counter

PREFIX = "CFSG/GH74/QTGen4/DCopy/"
NS = "CFSG.GH74.QTGen4.DCopy."


def normalise(text: str) -> list[str]:
    text = text.replace(NS, "")
    text = text.replace("[CFSG.GH74.QTGen4.Finite4 G]", "[Finite G]")
    text = text.replace("[QTGen4.Finite4 G]", "[Finite G]").replace("[Finite4 G]", "[Finite G]")
    text = re.sub(r"_F4\b", "", text)
    return [re.sub(r"\s+", " ", l).strip() for l in text.split("\n")]


def body(lines: list[str]) -> list[str]:
    return [l for l in lines if l and not re.match(r"^(public |meta |public meta )?import ", l)
            and l != "module" and not l.startswith("--")]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--out", default="f4pairs.tsv")
    ap.add_argument("--show")
    a = ap.parse_args()
    root = os.path.join(a.repo, PREFIX)
    rows = []
    for dp, _dn, fn in os.walk(root):
        for f in fn:
            if not f.endswith(".lean"):
                continue
            copy = os.path.join(dp, f)
            rel = os.path.relpath(copy, root)
            orig = os.path.join(a.repo, rel)
            with open(copy, encoding="utf-8") as fh:
                ctext = fh.read()
            uses_gen4 = "gen4" in ctext or "Gen4" in ctext.replace("QTGen4", "")
            if rel.startswith("Roots/") or not os.path.exists(orig):
                rows.append(("no-original", PREFIX + rel, rel, len(ctext.split("\n")), -1, uses_gen4))
                continue
            with open(orig, encoding="utf-8") as fh:
                otext = fh.read()
            cl, ol = normalise(ctext), normalise(otext)
            cb, ob = body(cl), body(ol)
            if cb == ob:
                cls, missing = "identical", 0
            else:
                oset = set(ob)
                missing = sum(1 for l in cb if l not in oset)
                cls = "subset" if missing == 0 else "drift"
            rows.append((cls, PREFIX + rel, rel, len(cb), missing, uses_gen4))
    rows.sort()
    with open(a.out, "w") as fh:
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")
    c = Counter(r[0] for r in rows)
    print(f"DCopy files: {len(rows)}  " + "  ".join(f"{k}: {v}" for k, v in sorted(c.items())))
    print(f"files using gen4: {sum(1 for r in rows if r[5])}")
    drift = [r for r in rows if r[0] == "drift"]
    if drift:
        import statistics
        print(f"drift: median {statistics.median(r[4] for r in drift)} lines not in original, "
              f"max {max(r[4] for r in drift)}")
        print("largest drifts:")
        for r in sorted(drift, key=lambda r: -r[4])[:10]:
            print(f"  {r[4]:5d}/{r[3]:5d}  {r[1]}")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

"""Who uses a subtree?  For a set S of modules (given by path regex), list the modules
outside S that import S directly, and which declarations of S their text mentions.

    python3 -I tools/subtree_users.py --sub 'REGEX' [--out users.tsv] [--min-len 6]

REGEX is matched (re.search) against module names, e.g.
    'QiuzhenCFSG\\.FeitThompson\\.(PF|BG)(section|appendix)'

Declarations of S are found textually (theorem/lemma/def/abbrev/structure/class/inductive/
instance names, last name component).  A direct importer "uses" a declaration if the bare name
occurs as a whole word in its text.  Short names (< --min-len) are reported separately as
ambiguous because they collide with ordinary identifiers.

Output: summary on stdout; TSV with columns importer, #S-imports, used names (space separated).
This is a textual over-approximation in one direction only (notation, instances and
anonymous-constructor uses are invisible), so a removal must still be confirmed by building.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+|nonrec\s+|"
    r"unsafe\s+|partial\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|"
    r"alias|opaque)\s+([^\s:({\[]+)", re.M)
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--sub", required=True)
    ap.add_argument("--out", default="users.tsv")
    ap.add_argument("--min-len", type=int, default=6)
    ap.add_argument("--root", default="Comparator.Solution")
    a = ap.parse_args()
    g = Graph.load(a.repo)
    pat = re.compile(a.sub)
    live = g.reachable(a.root)
    S = {m for m in g.mods if pat.search(m)}
    if not S:
        sys.exit("no module matches")
    sbytes = sum(g.mods[m].bytes for m in S)
    print(f"subtree: {len(S)} modules, {sbytes/1e6:.2f} MB  ({len(S & live)} reachable from {a.root})")

    names: dict[str, str] = {}
    private: set[str] = set()
    for m in S:
        with open(os.path.join(a.repo, g.mods[m].path), encoding="utf-8", errors="replace") as f:
            text = f.read()
        for mm in DECL_RE.finditer(text):
            full = mm.group(2)
            last = full.split(".")[-1]
            if "private" in mm.group(0).split(mm.group(1))[0]:
                private.add(last)
                continue
            names.setdefault(last, m)
    for n in list(names):
        if len(n) < a.min_len:
            pass
    long_names = {n for n in names if len(n) >= a.min_len}
    short_names = set(names) - long_names
    print(f"public declarations in subtree: {len(names)}  (short/ambiguous: {len(short_names)})")

    rows = []
    used_count: Counter[str] = Counter()
    short_count: Counter[str] = Counter()
    importers = [m for m in g.mods if m not in S and any(x in S for _k, x in g.mods[m].imports)]
    unused_importers = 0
    for m in importers:
        with open(os.path.join(a.repo, g.mods[m].path), encoding="utf-8", errors="replace") as f:
            text = f.read()
        words = set(WORD.findall(text))
        used = sorted(words & long_names)
        short = sorted(words & short_names)
        nimp = sum(1 for _k, x in g.mods[m].imports if x in S)
        for u in used:
            used_count[u] += 1
        for u in short:
            short_count[u] += 1
        if not used:
            unused_importers += 1
        rows.append((m, nimp, m in live, " ".join(used), " ".join(short)))
    rows.sort(key=lambda r: (-len(r[3].split()), r[0]))
    with open(a.out, "w") as f:
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"direct importers outside the subtree: {len(importers)}  "
          f"({sum(1 for r in rows if r[2])} live); mentioning no long subtree name: {unused_importers}")
    print(f"distinct subtree names mentioned by importers: {len(used_count)}")
    for n, c in used_count.most_common(60):
        print(f"  {c:5d}  {n}   [{names[n]}]")
    if short_count:
        print("short names mentioned (ambiguous): " +
              ", ".join(f"{n}({c})" for n, c in short_count.most_common(25)))
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

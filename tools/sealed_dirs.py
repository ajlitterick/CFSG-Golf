"""Find "sealed" directories: big subtrees that the rest of the repository consumes through
very few modules.  These are the candidates for replacing a whole development by a shorter
argument or by another proof of the same statements that is already in the repository.

    python3 -I tools/sealed_dirs.py [--min-mb 0.5] [--max-depth 5] [--max-ports 12] [--out sealed.tsv]

For each directory D (module-name prefix) it reports
  bytes, modules   size of the live part of D
  ports            modules of D imported by some live module outside D
  importers        live modules outside D importing a module of D
  exclusive        bytes (anywhere) that become unreachable from the root if the ports' own
                   imports are cut, i.e. what a replacement of the ports' proofs would free
Sorted by exclusive bytes.  Nested directories are all listed; read the table top-down.
"""
from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--min-mb", type=float, default=0.5)
    ap.add_argument("--max-depth", type=int, default=5)
    ap.add_argument("--max-ports", type=int, default=12)
    ap.add_argument("--out", default="sealed.tsv")
    a = ap.parse_args()
    g = Graph.load(a.repo)
    live = g.reachable(a.root)
    total = sum(g.mods[m].bytes for m in live)

    size: dict[str, int] = defaultdict(int)
    count: dict[str, int] = defaultdict(int)
    for m in live:
        parts = m.split(".")
        for d in range(1, min(len(parts), a.max_depth + 1)):
            p = ".".join(parts[:d])
            size[p] += g.mods[m].bytes
            count[p] += 1
    cands = [p for p, b in size.items() if b >= a.min_mb * 1e6 and count[p] >= 2]

    # ports / importers per candidate: one pass over live edges
    ports: dict[str, set[str]] = defaultdict(set)
    importers: dict[str, set[str]] = defaultdict(set)
    candset = set(cands)
    for m in live:
        mp = m.split(".")
        for _k, x in g.mods[m].imports:
            if x not in live:
                continue
            xp = x.split(".")
            for d in range(1, min(len(xp), a.max_depth + 1)):
                p = ".".join(xp[:d])
                if p in candset and mp[:d] != xp[:d]:
                    ports[p].add(x)
                    importers[p].add(m)

    rows = []
    for p in cands:
        np = len(ports[p])
        if np == 0 or np > a.max_ports:
            continue
        override = {x: [] for x in ports[p]}
        after = g.reachable(a.root, override)
        freed = total - sum(g.mods[m].bytes for m in after)
        rows.append((freed, size[p], count[p], np, len(importers[p]), p,
                     " ".join(sorted(ports[p]))[:400]))
    rows.sort(reverse=True)
    with open(a.out, "w") as f:
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"live total {total/1e6:.1f} MB; {len(rows)} sealed directories "
          f"(>= {a.min_mb} MB, <= {a.max_ports} ports)")
    print(f"{'excl MB':>8} {'dir MB':>8} {'mods':>6} {'ports':>5} {'imps':>5}  directory")
    for r in rows[:80]:
        print(f"{r[0]/1e6:8.2f} {r[1]/1e6:8.2f} {r[2]:6d} {r[3]:5d} {r[4]:5d}  {r[5]}")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

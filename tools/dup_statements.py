"""Theorems stated more than once (same statement, different proofs), weighted by what each
proof carries.

    python3 -I tools/dup_statements.py --dom DECL.dom.tsv [--jobs 3] [--out dupstmt.tsv]

DECL.dom.tsv is the dominator table of tools/domtree (run with MIN_BYTES 0), which gives for
every reachable declaration the bytes that exist only to prove it.  Here every theorem/lemma
statement (text before the first `:=`, own name blanked, whitespace collapsed, binder names
kept) is hashed; clusters with at least two members are statements proved more than once.
Keeping the cheapest proof and deriving the others from it frees the dominated bytes of the
others (an upper bound: dominated sets of different copies can overlap only if one dominates
the other, in which case the pair is skipped).

Output TSV: saving, copies, statement bytes, then per copy "dominated:own:name:path:line"
(cheapest first).
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import sys
from collections import defaultdict
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import text_reach as T  # noqa: E402
from cfsg_modules import Graph  # noqa: E402

WS = re.compile(r"\s+")


def work(path: str):
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    ch, _ = T.chunks_of(text)
    out = []
    for (s, e, kind, kw, name, body) in ch:
        if kind != T.KIND_DECL or kw not in ("theorem", "lemma"):
            continue
        norm = WS.sub(" ", T.PREFIX_RE.sub("", body)).strip()
        m = T.HEAD_RE.match(norm)
        if not m:
            continue
        i = norm.find(":=", m.end(4))
        if i < 0:
            continue
        stmt = norm[m.end(4):i].strip()
        if len(stmt) < 40:
            continue
        h = hashlib.blake2b(stmt.encode(), digest_size=8).digest()
        out.append((h, len(stmt), name, s + 1))
    return path, out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--dom", required=True)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--out", default="dupstmt.tsv")
    a = ap.parse_args()
    dom: dict[str, tuple[int, int, str]] = {}
    with open(a.dom, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            dom[p[5]] = (int(p[0]), int(p[1]), p[7])
    g = Graph.load(a.repo)
    live = sorted(g.reachable(a.root))
    paths = [os.path.join(a.repo, g.mods[m].path) for m in live]
    clusters: dict[bytes, list] = defaultdict(list)
    with Pool(a.jobs) as pool:
        for path, lst in pool.imap_unordered(work, paths, chunksize=300):
            rel = os.path.relpath(path, a.repo)
            for (h, n, name, line) in lst:
                loc = f"{rel}:{line}"
                d = dom.get(loc)
                if d is None:
                    continue  # unreachable declaration
                clusters[h].append((d[0], d[1], name, loc, n, d[2]))
    rows = []
    total = 0
    for h, lst in clusters.items():
        if len(lst) < 2:
            continue
        lst.sort()
        locs = {x[3] for x in lst}
        # drop copies whose dominating parent is another copy (a wrapper of it)
        indep = [x for x in lst if x[5] not in locs]
        if len(indep) < 2:
            continue
        saving = sum(x[0] for x in indep[1:])
        total += saving
        rows.append((saving, len(indep), lst[0][4], indep))
    rows.sort(key=lambda r: -r[0])
    with open(a.out, "w", encoding="utf-8") as f:
        for (saving, k, n, lst) in rows:
            f.write(f"{saving}\t{k}\t{n}\t" +
                    "\t".join(f"{x[0]}:{x[1]}:{x[2]}:{x[3]}" for x in lst[:10]) + "\n")
    print(f"statements proved more than once: {len(rows)} clusters; "
          f"dominated bytes of the non-cheapest copies: {total/1e6:.1f} MB")
    for (saving, k, n, lst) in rows[:50]:
        print(f"  {saving/1e3:9.1f} kB  x{k:<4d} stmt {n:5d}b  " +
              " | ".join(f"{x[2][:34]} {x[0]/1e3:.0f}k {x[3]}" for x in lst[:3]))
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

"""Check that removing imports did not hide a declaration that a file mentions.

    python3 -I tools/check_import_removal.py --old OLDREPO --new NEWREPO --graph GRAPHDIR
                                             [--out lost.tsv]

GRAPHDIR is a mention graph of NEWREPO written by `text_reach.py --save` (chunks, the names each
chunk mentions, and which chunks declare each name).  For every module whose import list differs
between the two trees, the import closures before and after are compared.  A reference is
reported as lost when a chunk of the file mentions a name that had a declaration in the old
closure but has none in the new closure (nor in the file itself).

Instances and notation provided by a removed import are invisible to this check, as they are
to any textual analysis; a build is the final word.
"""
from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402
from graphq import G  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--old", required=True)
    ap.add_argument("--new", required=True)
    ap.add_argument("--graph", required=True)
    ap.add_argument("--out", default="lost.tsv")
    a = ap.parse_args()
    go, gn = Graph.load(a.old), Graph.load(a.new)
    q = G(a.graph)
    pidx = {p: i for i, p in enumerate(q.paths)}
    changed = [m for m in gn.mods if m in go.mods and
               sorted(x for _k, x in go.mods[m].imports) != sorted(x for _k, x in gn.mods[m].imports)]
    print(f"modules with a changed import list: {len(changed)}")
    # name id -> files declaring it
    decl = np.nonzero(q.kind[:] == 0)[0]
    names = np.asarray(q.name[:])[decl]
    files = np.asarray(q.file[:])[decl]
    order = np.argsort(names, kind="stable")
    sn, sf = names[order], files[order]
    file_first = np.searchsorted(np.asarray(q.file[:]), np.arange(len(q.paths)), side="left")
    file_last = np.searchsorted(np.asarray(q.file[:]), np.arange(len(q.paths)), side="right")
    lost_rows = []
    nfiles_lost = 0
    for k, m in enumerate(changed):
        path = gn.mods[m].path
        fi = pidx.get(path)
        if fi is None:
            continue
        old_clo = go.reachable(m)
        new_clo = gn.reachable(m)
        gone = old_clo - new_clo
        if not gone:
            continue
        gone_f = {pidx[go.mods[x].path] for x in gone if x in go.mods and go.mods[x].path in pidx}
        new_f = {pidx[gn.mods[x].path] for x in new_clo if gn.mods[x].path in pidx}
        c0, c1 = int(file_first[fi]), int(file_last[fi])
        ids = np.unique(q.toks[q.indptr[c0]:q.indptr[c1]])
        bad = []
        for x in ids:
            lo, hi = np.searchsorted(sn, x, side="left"), np.searchsorted(sn, x, side="right")
            fs = set(int(v) for v in sf[lo:hi])
            if fs & gone_f and not (fs & new_f):
                bad.append(q.names[int(x)])
        if bad:
            nfiles_lost += 1
            lost_rows.append((path, len(gone), " ".join(bad[:40])))
        if k % 500 == 0:
            print(f"  {k}/{len(changed)} checked, {nfiles_lost} files with lost references", flush=True)
    with open(a.out, "w", encoding="utf-8") as f:
        for r in lost_rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"files with lost references: {nfiles_lost}")
    for r in lost_rows[:30]:
        print(f"  {r[0]}  (-{r[1]} modules)  {r[2][:160]}")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

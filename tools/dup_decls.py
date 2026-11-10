"""Duplicate declarations and a breakdown of non-declaration text.

    python3 -I tools/dup_decls.py [--jobs 3] [--out dups.tsv] [--min-bytes 200]

Uses the chunker of text_reach.py.  For every declaration chunk in a live module it hashes the
text with the declaration's own name blanked and whitespace collapsed, so the same lemma
restated under another name (or as a private copy in another file) lands in one cluster.
Reports the bytes that are redundant (all copies but one per cluster), the largest clusters,
and, separately, how the non-declaration bytes split by leading keyword (import, open,
set_option, variable, namespace, ...).

Output TSV: cluster hash, copies, bytes per copy, kind, one name, then "path:line" of each copy
(first 12).
"""
from __future__ import annotations

import argparse
import hashlib
import os
import re
import sys
from collections import Counter, defaultdict
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import text_reach as T  # noqa: E402
from cfsg_modules import Graph  # noqa: E402

WS = re.compile(r"\s+")
FIRST = re.compile(r"\A(?:@\[[^\]]*\]\s*)*((?:public\s+|private\s+|noncomputable\s+|meta\s+|scoped\s+|local\s+)*\S+)")


def work(path: str):
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    ch, _ = T.chunks_of(text)
    decls = []
    other: Counter[str] = Counter()
    for (s, e, kind, kw, name, body) in ch:
        if kind == T.KIND_DECL and name:
            norm = WS.sub(" ", T.PREFIX_RE.sub("", body)).strip()
            # blank the declaration's own (possibly qualified) name where it is declared
            m = T.HEAD_RE.match(norm)
            if m:
                norm = norm[:m.start(4)] + "?" + norm[m.end(4):]
            norm = re.sub(r"^(?:public |private |protected )+", "", norm)
            h = hashlib.blake2b(norm.encode(), digest_size=8).digest()
            decls.append((h, len(norm), kw, name, s + 1))
        elif kind == T.KIND_OTHER:
            m = FIRST.match(body)
            key = m.group(1).split()[-1] if m else "?"
            if kw:
                key = "attr-tagged " + kw
            other[key] += len(body.encode("utf-8"))
    return path, decls, other


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--out", default="dups.tsv")
    ap.add_argument("--min-bytes", type=int, default=200)
    a = ap.parse_args()
    g = Graph.load(a.repo)
    live = sorted(g.reachable(a.root))
    paths = [g.mods[m].path for m in live]
    clusters: dict[bytes, list] = defaultdict(list)
    other: Counter[str] = Counter()
    total_decl = 0
    with Pool(a.jobs) as pool:
        for path, decls, oth in pool.imap_unordered(work, [os.path.join(a.repo, p) for p in paths],
                                                    chunksize=300):
            rel = os.path.relpath(path, a.repo)
            other.update(oth)
            for (h, n, kw, name, line) in decls:
                total_decl += n
                clusters[h].append((n, kw, name, rel, line))
    red = 0
    red_big = 0
    rows = []
    for h, lst in clusters.items():
        if len(lst) > 1:
            n = lst[0][0]
            r = n * (len(lst) - 1)
            red += r
            if n >= a.min_bytes:
                red_big += r
                rows.append((r, len(lst), n, lst[0][1], lst[0][2], h.hex(),
                             " ".join(f"{x[3]}:{x[4]}" for x in lst[:12])))
    rows.sort(reverse=True)
    with open(a.out, "w", encoding="utf-8") as f:
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")
    print(f"declaration text (normalised): {total_decl/1e6:.1f} MB in {sum(len(v) for v in clusters.values())} declarations")
    print(f"redundant copies: {red/1e6:.1f} MB; in declarations of >= {a.min_bytes} bytes: {red_big/1e6:.1f} MB "
          f"({len(rows)} clusters)")
    print("largest clusters (redundant bytes, copies, bytes each, kind, name, first copy):")
    for r in rows[:40]:
        print(f"  {r[0]/1e3:9.1f} kB  x{r[1]:<5d} {r[2]:6d}  {r[3]:8s} {r[4][:50]:50s} {r[6].split(' ')[0]}")
    print("non-declaration text by leading keyword (MB):")
    for k, v in other.most_common(25):
        print(f"  {v/1e6:8.2f}  {k}")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

"""Theorems with the same statement up to presentation, weighted by what each proof carries.

    python3 -I tools/similar_statements.py --dom DECL.dom.tsv [--repo .] [--out similar.tsv]
                                           [--min-tokens 8] [--jobs 3]

Two statements are put in one cluster when they agree as bags of tokens after
  * dropping binder punctuation, `∀`, `→`, `:` and commas, so `(G : Type*) [Group G] (h : P G) : Q G`
    and `∀ (G : Type u) [Group G], P G → Q G` coincide;
  * replacing bound variable names by one placeholder and dropping names used only once
    (hypothesis names);
  * identifying `Type*`, `Type u`, `Type _`, `Sort*`.
Only self-contained statements are considered (they bind a type with a `Group`-like class or a
`Type`), so theorems that depend on section variables are not confused with each other.

DECL.dom.tsv is the dominator table of tools/domtree (MIN_BYTES 0).  A cluster's saving is the
dominated bytes of every copy except the cheapest, skipping copies that lie below another copy
in the dominator tree (wrappers).  This is how the two proofs of the odd order theorem show up.

Output TSV: saving, copies, tokens, then per copy "dominated:name:path:line" (cheapest first).
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
TOK = re.compile(r"[^\W\d][\w'.!?]*|\d+|[^\s\w]")
BINDER = re.compile(r"[({\[⦃]\s*((?:[^\W\d][\w']*\s+)*[^\W\d][\w']*)\s*:")
QUANT = re.compile(r"(?:∀|∃|fun|λ|Σ|∑|∏|⋃|⋂)\s+((?:[^\W\d][\w']*\s*)+)[,:∈]")
DROP = set("(){}[]⦃⦄:,∀→") | {"*"}
MIN_TOK = 8


def canon(stmt: str):
    stmt = re.sub(r"\b(?:Type|Sort)\s*(?:\*|_|[a-z]\b|\(\s*[^)]*\))?", "Type", stmt)
    vars_: set[str] = set()
    for m in BINDER.finditer(stmt):
        vars_.update(m.group(1).split())
    for m in QUANT.finditer(stmt):
        vars_.update(m.group(1).split())
    toks = TOK.findall(stmt)
    cnt = Counter(toks)
    bag: Counter[str] = Counter()
    for t in toks:
        if t in DROP:
            continue
        if t in vars_:
            if cnt[t] > 1:
                bag["ν"] += 1
            continue
        bag[t] += 1
    return bag


def work(path: str):
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    ch, _ = T.chunks_of(text)
    out = []
    for (s, e, kind, kw, name, body) in ch:
        if kind != T.KIND_DECL or kw not in ("theorem", "lemma"):
            continue
        lines = [l.strip() for l in body.split("\n") if l.strip()]
        norm = T.PREFIX_RE.sub("", "\n".join(lines))
        norm = WS.sub(" ", norm)
        m = T.HEAD_RE.match(norm)
        if not m:
            continue
        i = norm.find(":=", m.end(4))
        if i < 0:
            continue
        stmt = norm[m.end(4):i]
        if "Type" not in stmt and "Group" not in stmt:
            continue
        bag = canon(stmt)
        nt = sum(v for k, v in bag.items() if k != "ν")
        if nt < MIN_TOK:
            continue
        key = " ".join(f"{k}*{v}" for k, v in sorted(bag.items()))
        h = hashlib.blake2b(key.encode(), digest_size=8).digest()
        out.append((h, nt, name, s + 1))
    return path, out


def main() -> None:
    global MIN_TOK
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--dom", required=True)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--min-tokens", type=int, default=8)
    ap.add_argument("--out", default="similar.tsv")
    a = ap.parse_args()
    MIN_TOK = a.min_tokens
    dom: dict[str, tuple[int, str]] = {}
    with open(a.dom, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            dom[p[5]] = (int(p[0]), p[7])
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
                if d is not None:
                    clusters[h].append((d[0], name, loc, n))

    def ancestors(loc: str) -> set[str]:
        out = set()
        cur = dom.get(loc, (0, "-"))[1]
        k = 0
        while cur != "-" and k < 200:
            out.add(cur)
            cur = dom.get(cur, (0, "-"))[1]
            k += 1
        return out

    rows = []
    total = 0
    for h, lst in clusters.items():
        if len(lst) < 2 or len(lst) > 40:
            continue
        lst.sort()
        locs = {x[2] for x in lst}
        indep = [x for x in lst if not (ancestors(x[2]) & locs)]
        if len(indep) < 2:
            continue
        saving = sum(x[0] for x in indep[1:])
        total += saving
        rows.append((saving, len(indep), lst[0][3], indep))
    rows.sort(key=lambda r: -r[0])
    with open(a.out, "w", encoding="utf-8") as f:
        for (saving, k, n, lst) in rows:
            f.write(f"{saving}\t{k}\t{n}\t" + "\t".join(f"{x[0]}:{x[1]}:{x[2]}" for x in lst[:10]) + "\n")
    print(f"clusters of equivalent-looking statements: {len(rows)}; dominated bytes of the "
          f"non-cheapest copies: {total/1e6:.1f} MB")
    for (saving, k, n, lst) in rows[:60]:
        print(f"  {saving/1e3:9.1f} kB x{k:<3d} tok {n:3d}  " +
              " | ".join(f"{x[1][:36]} {x[0]/1e3:.0f}k {x[2]}" for x in lst[:3]))
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

"""Queries on the mention graph saved by `text_reach.py --save DIR`.

    python3 -I tools/graphq.py DIR who NAME [--limit 30]     chunks mentioning NAME
    python3 -I tools/graphq.py DIR decl NAME                  chunks declaring NAME
    python3 -I tools/graphq.py DIR uses NAME                  declaration names NAME's chunk(s) mention
    python3 -I tools/graphq.py DIR rootkinds                  byte totals of always-live chunks by keyword
"""
from __future__ import annotations

import os
import sys

import numpy as np


class G:
    def __init__(self, d: str):
        mm = lambda n, t: np.memmap(os.path.join(d, n), dtype=t, mode="r")
        self.indptr = mm("indptr.i64", np.int64)
        self.toks = mm("toks.u32", np.uint32)
        self.kind = mm("kind.i8", np.int8)
        self.name = mm("name.i64", np.int64)
        self.bytes = mm("bytes.i64", np.int64)
        self.file = mm("file.i64", np.int64)
        self.sline = mm("sline.i64", np.int64)
        self.eline = mm("eline.i64", np.int64)
        with open(os.path.join(d, "paths.txt"), encoding="utf-8") as f:
            self.paths = f.read().split("\n")
        with open(os.path.join(d, "names.txt"), encoding="utf-8") as f:
            self.names = f.read().split("\n")
        with open(os.path.join(d, "kw.txt"), encoding="utf-8") as f:
            self.kw = f.read().split("\n")
        self._nid = None

    def nid(self, name: str) -> int:
        if self._nid is None:
            self._nid = {n: i for i, n in enumerate(self.names)}
        return self._nid.get(name, -1)

    def chunk_of_tokpos(self, pos: np.ndarray) -> np.ndarray:
        return np.searchsorted(self.indptr, pos, side="right") - 1

    def who(self, name: str) -> np.ndarray:
        x = self.nid(name)
        if x < 0:
            return np.zeros(0, dtype=np.int64)
        pos = np.nonzero(self.toks == x)[0]
        return self.chunk_of_tokpos(pos)

    def decl(self, name: str) -> np.ndarray:
        x = self.nid(name)
        return np.nonzero((self.name == x) & (self.kind == 0))[0]

    def label(self, c: int) -> str:
        nm = self.names[self.name[c]] if self.name[c] >= 0 else ""
        k = {0: "decl", 1: "live", 2: "example"}[int(self.kind[c])]
        return f"{k:5s} {self.kw[c] or '-':9s} {nm[:50]:50s} {self.paths[self.file[c]]}:{self.sline[c]+1}"


def main() -> None:
    d, cmd = sys.argv[1], sys.argv[2]
    g = G(d)
    limit = 30
    if "--limit" in sys.argv:
        limit = int(sys.argv[sys.argv.index("--limit") + 1])
    if cmd == "who":
        cs = g.who(sys.argv[3])
        print(f"{len(cs)} chunks mention {sys.argv[3]}")
        live = [c for c in cs if g.kind[c] == 1]
        print(f"  of which always-live: {len(live)}")
        for c in (live + [c for c in cs if g.kind[c] != 1])[:limit]:
            print("  " + g.label(int(c)))
    elif cmd == "decl":
        for c in g.decl(sys.argv[3])[:limit]:
            print("  " + g.label(int(c)), g.bytes[c], "bytes")
    elif cmd == "uses":
        for c in g.decl(sys.argv[3])[:3]:
            ids = g.toks[g.indptr[c]:g.indptr[c + 1]]
            print(g.label(int(c)))
            print("   " + " ".join(g.names[i] for i in ids[:limit * 10]))
    elif cmd == "rootkinds":
        from collections import Counter
        cnt: Counter[str] = Counter()
        num: Counter[str] = Counter()
        live = np.nonzero(g.kind == 1)[0]
        ntok = g.indptr[live + 1] - g.indptr[live]
        for c, t in zip(live, ntok):
            if t == 0:
                continue
            k = g.kw[c] or "(command)"
            cnt[k] += int(t)
            num[k] += 1
        for k, v in cnt.most_common(20):
            print(f"  {k:12s} chunks {num[k]:8d}  mentions {v}")


if __name__ == "__main__":
    main()

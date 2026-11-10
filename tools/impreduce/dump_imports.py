"""Dump the import graph (repository + external packages) for tools/impreduce/impreduce.rs.

    python3 -I tools/impreduce/dump_imports.py --repo REPO --packages REPO_WITH_LAKE/.lake/packages --out DIR

Writes in DIR:
    names.txt      one module per line; the first `nrepo` lines are repository modules
    meta.txt       "nrepo <n>"
    ptr.i64        CSR offsets (n+1)
    tgt.u32        import targets
    kind.u8        0 = `import`, 1 = `public import`, 2 = anything else (meta / all)
External modules that are not module-system files re-export everything they import, so all
their edges are written as public.  Modules without source (Init, Std, Lean) are leaves.
"""
from __future__ import annotations

import argparse
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from cfsg_modules import Graph, parse_imports  # noqa: E402


def is_module_file(path: str) -> bool:
    in_block = False
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if in_block:
                if "-/" in s:
                    in_block = False
                continue
            if s.startswith("/-"):
                if "-/" not in s:
                    in_block = True
                continue
            if not s or s.startswith("--"):
                continue
            return s.split("--")[0].strip() == "module"
    return False


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--packages", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    g = Graph.load(a.repo)
    names = sorted(g.mods)
    nrepo = len(names)
    idx = {m: i for i, m in enumerate(names)}
    imports: list[list[tuple[int, str]]] = []
    for m in names:
        lst = []
        for k, x in g.mods[m].imports:
            lst.append((1 if k == "public" else 0 if k == "private" else 2, x))
        imports.append(lst)
    # external packages
    ext: dict[str, list[tuple[int, str]]] = {}
    for pkg in sorted(os.listdir(a.packages)):
        root = os.path.join(a.packages, pkg)
        for dp, dn, fn in os.walk(root):
            dn[:] = [d for d in dn if d not in (".lake", ".git", "test", "MathlibTest", "docs", "scripts")]
            for f in fn:
                if not f.endswith(".lean"):
                    continue
                full = os.path.join(dp, f)
                mod = os.path.relpath(full, root)[:-5].replace(os.sep, ".")
                if mod in idx or mod in ext or mod.startswith("lakefile"):
                    continue
                try:
                    ims = parse_imports(full)
                    ism = is_module_file(full)
                except OSError:
                    continue
                ext[mod] = [((1 if k == "public" else 0 if k == "private" else 2) if ism else 1, x)
                            for k, x in ims]
    for m in sorted(ext):
        idx[m] = len(names)
        names.append(m)
        imports.append(ext[m])
    # leaves
    for lst in list(imports):
        for _k, x in lst:
            if x not in idx:
                idx[x] = len(names)
                names.append(x)
                imports.append([])
    ptr = np.zeros(len(names) + 1, dtype=np.int64)
    tgt: list[int] = []
    kind: list[int] = []
    for i, lst in enumerate(imports):
        for k, x in lst:
            tgt.append(idx[x])
            kind.append(k)
        ptr[i + 1] = len(tgt)
    os.makedirs(a.out, exist_ok=True)
    ptr.tofile(os.path.join(a.out, "ptr.i64"))
    np.array(tgt, dtype=np.uint32).tofile(os.path.join(a.out, "tgt.u32"))
    np.array(kind, dtype=np.uint8).tofile(os.path.join(a.out, "kind.u8"))
    with open(os.path.join(a.out, "names.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(names))
    with open(os.path.join(a.out, "meta.txt"), "w") as f:
        f.write(f"nrepo {nrepo}\n")
    print(f"modules: {len(names)} (repository {nrepo}, external with source {len(ext)}); edges {len(tgt)}")


if __name__ == "__main__":
    main()

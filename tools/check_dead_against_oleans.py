"""Test the source-level dead list against compiled terms.

    python3 -I tools/check_dead_against_oleans.py --edges edges.tsv --dead decl.dead.tsv
                                                   [--out conflicts.tsv]

edges.tsv comes from tools/DeclEdges.lean (constants of the modules built so far and the
constants each one mentions).  Every constant is attributed to the source declaration that
owns it: the innermost name component that is declared (by tools/text_reach's chunker) in the
module's source file, so `Ns.foo._proof_1` and `_private.M.0.Ns.foo` both belong to `foo`.

A conflict is an edge U -> V where V's owner is on the dead list and U's owner is not (or U has
no owner: an instance, an attribute-generated constant, ...).  Conflicts are declarations the
text analysis would delete although a surviving compiled constant refers to them.  Names that
are declared twice in a file with different fates are ignored.

Prints the number of dead declarations that could be checked (their module is built), the
conflicts found, and writes them to --out.
"""
from __future__ import annotations

import argparse
import os
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import text_reach as T  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--edges", required=True)
    ap.add_argument("--dead", required=True)
    ap.add_argument("--out", default="conflicts.tsv")
    a = ap.parse_args()

    dead: dict[str, set[str]] = defaultdict(set)      # path -> dead names
    with open(a.dead, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[4] not in ("ctx", "example") and p[5]:
                dead[p[0]].add(p[5])

    cmod: dict[int, str] = {}
    cname: dict[int, str] = {}
    edges: list[tuple[int, int]] = []
    with open(a.edges, encoding="utf-8", errors="replace") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[0] == "C" and len(p) >= 4:
                k = int(p[1])
                cmod[k] = p[2]
                cname[k] = p[3].strip()
            elif p[0] == "E" and len(p) >= 3:
                edges.append((int(p[1]), int(p[2])))
    mods = sorted(set(cmod.values()))
    print(f"built modules with constants: {len(mods)}; constants: {len(cmod)}; edges: {len(edges)}")

    # per module: declared names with fate
    declared: dict[str, dict[str, str]] = {}
    for m in mods:
        path = m.replace(".", "/") + ".lean"
        full = os.path.join(a.repo, path)
        if not os.path.exists(full):
            declared[m] = {}
            continue
        with open(full, encoding="utf-8", errors="replace") as f:
            ch, _ = T.chunks_of(f.read())
        cnt: dict[str, int] = defaultdict(int)
        for c in ch:
            if c[4]:
                cnt[c[4]] += 1
        d = {}
        dn = dead.get(path, set())
        for n, k in cnt.items():
            if k > 1 and n in dn:
                d[n] = "ambiguous"
            else:
                d[n] = "dead" if n in dn else "live"
        declared[m] = d

    owner_cache: dict[int, tuple[str, str] | None] = {}
    key_of_name = {n: k for k, n in cname.items()}
    AUX = ("eq_", "_proof_", "match_", "_sunfold", "_unsafe_rec", "proof_", "_simp_", "_eq_")

    def owner(k: int):
        if k in owner_cache:
            return owner_cache[k]
        m = cmod.get(k)
        res = None
        if m is not None:
            d = declared[m]
            for comp in reversed(cname[k].split(".")):
                if comp in d:
                    res = (comp, d[comp])
                    break
        owner_cache[k] = res
        return res

    checked = {(cmod[k], owner(k)[0]) for k in cmod if owner(k) and owner(k)[1] == "dead"}
    conflicts: dict[tuple[str, str], list[str]] = defaultdict(list)
    for (u, v) in edges:
        ov = owner(v)
        if ov is None or ov[1] != "dead":
            continue
        # auxiliary constants (`foo._proof_1`, `foo.match_1`, ...) are cached and reused by
        # later declarations of the module; without `foo` they are simply regenerated
        if cname[v].split(".")[-1] != ov[0]:
            continue
        ou = owner(u)
        if ou is not None and ou[1] in ("dead", "ambiguous"):
            continue
        if ou is not None and cmod[u] == cmod[v] and ou[0] == ov[0]:
            continue
        if ou is None and ov[0] in cname[u].split("."):
            continue  # equation lemma / auxiliary of V itself, generated in a later module
        if ou is None:
            # auxiliary of a declaration of another module (equation lemma made on demand):
            # judge it by the declaration it belongs to
            comps = cname[u].split(".")
            if comps[-1].startswith(AUX) or comps[-1] == "eq_def":
                pk = key_of_name.get(".".join(comps[:-1]))
                po = owner(pk) if pk is not None else None
                if po is not None and po[1] in ("dead", "ambiguous"):
                    continue
        conflicts[(cmod[v], ov[0])].append(f"{cmod[u]}:{cname[u]}")
    print(f"dead declarations in built modules: {len(checked)}; conflicts: {len(conflicts)}")
    with open(a.out, "w", encoding="utf-8") as f:
        for (m, n), us in sorted(conflicts.items()):
            f.write(f"{m}\t{n}\t{len(us)}\t" + " ".join(us[:5]) + "\n")
    for (m, n), us in list(sorted(conflicts.items()))[:40]:
        print(f"  {m}  {n}   <- {us[0]}  (+{len(us)-1})")
    print(f"wrote {a.out}")


if __name__ == "__main__":
    main()

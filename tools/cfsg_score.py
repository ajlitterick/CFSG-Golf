"""Golf score: repo-local .lean bytes/lines transitively imported by the final theorem.

    python3 -I tools/cfsg_score.py [--root Comparator.Solution] [--by-dir N]
                                   [--json OUT] [--diff BASELINE] [--dead] [--no-cache]

Default report: totals, per top-level directory (CFSG/<Sub> for CFSG), and the number
of external (Mathlib/TauCeti) modules in the closure.  `--diff tools/baseline.json`
prints the change against a stored report.  `--dead` writes the modules not reachable
from the root to dead_modules.txt (one per line).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402


def dir_key(mod: str, depth: int) -> str:
    parts = mod.split(".")
    if parts[0] == "CFSG":
        return "/".join(parts[: depth + 1]) if len(parts) > 1 else "CFSG"
    return "/".join(parts[:depth])


def report(g: Graph, root: str, depth: int) -> dict:
    reach = g.reachable(root)
    dirs: dict[str, dict] = defaultdict(lambda: {"modules": 0, "bytes": 0, "lines": 0})
    tot = {"modules": 0, "bytes": 0, "lines": 0}
    for m in reach:
        v = g.mods[m]
        d = dirs[dir_key(m, depth)]
        for k, val in (("modules", 1), ("bytes", v.bytes), ("lines", v.lines)):
            d[k] += val
            tot[k] += val
    ext = g.external_reachable(reach)
    ext_by = defaultdict(int)
    for e in ext:
        ext_by[e.split(".")[0]] += 1
    dead = sorted(set(g.mods) - reach)
    try:
        rev = subprocess.run(["git", "-C", g.repo, "rev-parse", "--short", "HEAD"],
                             capture_output=True, text=True).stdout.strip()
    except Exception:
        rev = "?"
    return {"root": root, "git_rev": rev, "depth": depth, "totals": tot,
            "dirs": dict(sorted(dirs.items(), key=lambda kv: -kv[1]["bytes"])),
            "external": dict(ext_by), "dead": dead}


def fmt_mb(b: int) -> str:
    return f"{b / 1e6:9.2f} MB"


def print_report(r: dict) -> None:
    t = r["totals"]
    print(f"root {r['root']}  rev {r['git_rev']}")
    print(f"TOTAL  {fmt_mb(t['bytes'])}  {t['lines']:>10} lines  {t['modules']:>7} modules")
    print(f"external modules in closure: " + ", ".join(f"{k} {v}" for k, v in sorted(r['external'].items())))
    print(f"unreachable repo modules: {len(r['dead'])}")
    print()
    for d, v in r["dirs"].items():
        print(f"  {fmt_mb(v['bytes'])}  {v['lines']:>10}  {v['modules']:>7}  {d}")


def print_diff(new: dict, old: dict) -> None:
    tn, to = new["totals"], old["totals"]
    print(f"score vs baseline ({old['git_rev']} -> {new['git_rev']}):")
    for k in ("bytes", "lines", "modules"):
        d = tn[k] - to[k]
        pct = 100.0 * d / to[k] if to[k] else 0.0
        unit = fmt_mb(d) if k == "bytes" else f"{d:+d}"
        print(f"  {k:8} {unit:>14}  ({pct:+.3f}%)   now {tn[k]}")
    keys = set(new["dirs"]) | set(old["dirs"])
    rows = []
    for k in keys:
        nb = new["dirs"].get(k, {}).get("bytes", 0)
        ob = old["dirs"].get(k, {}).get("bytes", 0)
        if nb != ob:
            rows.append((nb - ob, k, new["dirs"].get(k, {}).get("modules", 0) - old["dirs"].get(k, {}).get("modules", 0)))
    rows.sort()
    if rows:
        print("  per directory (bytes, modules):")
        for d, k, dm in rows:
            print(f"    {fmt_mb(d)}  {dm:+6d}  {k}")
    print(f"  unreachable modules: {len(old['dead'])} -> {len(new['dead'])}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--by-dir", type=int, default=1, dest="depth")
    ap.add_argument("--json")
    ap.add_argument("--diff")
    ap.add_argument("--dead", action="store_true")
    ap.add_argument("--no-cache", action="store_true")
    a = ap.parse_args()
    g = Graph.load(a.repo, use_cache=not a.no_cache)
    r = report(g, a.root, a.depth)
    print_report(r)
    if a.diff:
        with open(a.diff) as f:
            old = json.load(f)
        print()
        print_diff(r, old)
    if a.json:
        with open(a.json, "w") as f:
            json.dump(r, f, indent=1)
        print(f"\nwrote {a.json}")
    if a.dead:
        with open("dead_modules.txt", "w") as f:
            f.write("\n".join(r["dead"]) + "\n")
        print(f"wrote dead_modules.txt ({len(r['dead'])} modules)")


if __name__ == "__main__":
    main()

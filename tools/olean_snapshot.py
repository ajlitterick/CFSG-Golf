"""Snapshot or compare the hashes of built module artefacts.

    python3 -I tools/olean_snapshot.py snap  --modules M1 M2 ... --out snap.json
    python3 -I tools/olean_snapshot.py diff  before.json after.json

Each module records the sha256 of its `.olean` (public interface), `.olean.private`
and `.olean.server` files under .lake/build/lib/lean.  `diff` classifies each module:
  public-unchanged  proof-only change: no importer needs recompiling
  private-changed   only `import all` / `meta import` consumers see it
  public-changed    interface change: everything importing it rebuilds
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys

LIB = os.path.join(".lake", "build", "lib", "lean")
PARTS = (".olean", ".olean.private", ".olean.server")


def sha(path: str) -> str | None:
    if not os.path.exists(path):
        return None
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def snap(modules: list[str]) -> dict:
    out = {}
    for m in modules:
        base = os.path.join(LIB, *m.split("."))
        out[m] = {p: sha(base + p) for p in PARTS}
    return out


def classify(before: dict, after: dict) -> dict[str, str]:
    res = {}
    for m, a in after.items():
        b = before.get(m)
        if b is None:
            res[m] = "new"
        elif a[".olean"] != b[".olean"]:
            res[m] = "public-changed"
        elif a[".olean.private"] != b[".olean.private"] or a[".olean.server"] != b[".olean.server"]:
            res[m] = "private-changed"
        else:
            res[m] = "public-unchanged"
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("snap")
    s.add_argument("--modules", nargs="+", required=True)
    s.add_argument("--out", required=True)
    d = sub.add_parser("diff")
    d.add_argument("before")
    d.add_argument("after")
    a = ap.parse_args()
    if a.cmd == "snap":
        with open(a.out, "w") as f:
            json.dump(snap(a.modules), f, indent=1)
        print(f"wrote {a.out} ({len(a.modules)} modules)")
    else:
        with open(a.before) as f:
            b = json.load(f)
        with open(a.after) as f:
            af = json.load(f)
        res = classify(b, af)
        for m, c in sorted(res.items(), key=lambda kv: kv[1]):
            print(f"{c:18} {m}")
        worst = "public-changed" if "public-changed" in res.values() else (
            "private-changed" if "private-changed" in res.values() else "public-unchanged")
        print(f"SUMMARY: {worst}")
        sys.exit(2 if worst == "public-changed" else 0)


if __name__ == "__main__":
    main()

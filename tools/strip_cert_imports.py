"""Remove `import Certificates.CertificateN[Base]` lines from files whose body never mentions
a certificate.

    python3 -I tools/strip_cert_imports.py [--apply] [--min-lines N] [paths...]

Without --apply it only reports.  A file qualifies when (a) it imports at least --min-lines
(default 1) certificate modules and (b) its non-import text contains neither
`Certificates.` nor `certificate` (case-insensitive).  `public meta import` lines are never
touched.  Prints per-file counts and the total number of lines removed.
"""
from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402

CERT_IMPORT = re.compile(r"^(public\s+)?import\s+Certificates\.Certificate\d+(Base)?\s*$")
HEADER_LINE = re.compile(r"^(public\s+|meta\s+|public\s+meta\s+)?import\s+|^module\s*$|^\s*$|^--|^/-|^-/")


def split_header(text: str) -> tuple[list[str], list[str]]:
    lines = text.split("\n")
    i = 0
    in_comment = False
    while i < len(lines):
        s = lines[i].strip()
        if in_comment:
            if "-/" in s:
                in_comment = False
            i += 1
            continue
        if s.startswith("/-") and "-/" not in s:
            in_comment = True
            i += 1
            continue
        if HEADER_LINE.match(lines[i]) or s.startswith(("set_option", "prelude", "#")):
            i += 1
            continue
        break
    return lines[:i], lines[i:]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--min-lines", type=int, default=1)
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("paths", nargs="*")
    a = ap.parse_args()
    g = Graph.load(a.repo)
    paths = a.paths or [os.path.join(a.repo, m.path) for m in g.mods.values()
                        if any(x.startswith("Certificates.Certificate") for _k, x in m.imports)]
    total_removed = 0
    files = 0
    rows = []
    for p in paths:
        with open(p, encoding="utf-8") as f:
            text = f.read()
        header, body = split_header(text)
        body_text = "\n".join(body)
        if re.search(r"Certificates\.|certificate", body_text, re.I):
            continue
        keep, removed = [], 0
        for line in header:
            if CERT_IMPORT.match(line):
                removed += 1
            else:
                keep.append(line)
        if removed < a.min_lines:
            continue
        files += 1
        total_removed += removed
        rows.append((removed, os.path.relpath(p, a.repo)))
        if a.apply:
            with open(p, "w", encoding="utf-8") as f:
                f.write("\n".join(keep + body))
    rows.sort(reverse=True)
    for r, p in rows[:40]:
        print(f"{r:6d}  {p}")
    if len(rows) > 40:
        print(f"  ... {len(rows) - 40} more files")
    print(f"files: {files}   certificate import lines {'removed' if a.apply else 'removable'}: {total_removed}")


if __name__ == "__main__":
    main()

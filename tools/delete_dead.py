"""Delete the declarations listed by tools/domtree (`*.dead.tsv`) from a checkout.

    python3 -I tools/delete_dead.py --dead decl.dead.tsv --repo WORKTREE [--apply]
                                    [--only-prefix CFSG/LocalAnalysis ...] [--report out.tsv]

Each row of the dead list is (path, first line, last line, bytes, kind, name).  For every file:
  * the line range of each dead declaration is removed, without the blank / comment-only lines
    at its end (they may hold the doc comment of the next declaration);
  * a doc comment (`/-- ... -/`) that ends directly above a dead declaration is removed with it,
    because a doc comment must be followed by a declaration;
  * dead context commands (`variable`, `include`, `omit`, `open ... (names)`) are removed too;
  * files containing a `mutual` block are left alone;
  * a file is never deleted, so that modules importing it keep its transitive imports.
The source file is re-chunked and each row is checked against it (same start line, same
declared name) before anything is removed; mismatching rows are skipped and counted.

Without --apply nothing is written.  Prints bytes removed per top-level directory.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import text_reach as T  # noqa: E402

DOC_RE = re.compile(r'"(?:\\.|[^"\\\n])*"|--[^\n]*|/-.*?-/', re.S)


def process(path: str, rows: list[tuple[int, int, str, str]], apply: bool):
    with open(path, encoding="utf-8") as f:
        text = f.read()
    lines = text.split("\n")
    stripped = T.strip(text).split("\n")
    if any(l.startswith("mutual") for l in stripped):
        return 0, 0, len(rows)
    ch, _ = T.chunks_of(text)
    by_start = {c[0]: c for c in ch}
    # doc comments: last line -> first line
    doc_end: dict[int, int] = {}
    for m in DOC_RE.finditer(text):
        if m.group(0).startswith("/--"):
            a = text.count("\n", 0, m.start())
            b = a + m.group(0).count("\n")
            # only a doc comment that starts its line and ends its line
            ls = text.rfind("\n", 0, m.start()) + 1
            le = text.find("\n", m.end())
            le = len(text) if le < 0 else le
            if text[ls:m.start()].strip() == "" and text[m.end():le].strip() == "":
                doc_end[b] = a
    kill = [False] * len(lines)
    skipped = 0
    done = 0
    for (s1, e, kw, name) in rows:
        s = s1 - 1
        c = by_start.get(s)
        if c is None or c[1] != e:
            skipped += 1
            continue
        if kw == "ctx":
            if c[2] != T.KIND_OTHER or c[3]:
                skipped += 1
                continue
        elif kw == "example":
            if c[2] != T.KIND_EXAMPLE:
                skipped += 1
                continue
        elif c[2] != T.KIND_DECL or c[4] != name or c[3] != kw:
            skipped += 1
            continue
        while e > s and stripped[e - 1].strip() == "":
            e -= 1
        j = s - 1
        while j >= 0 and lines[j].strip() == "":
            j -= 1
        if j >= 0 and j in doc_end:
            s = doc_end[j]
        for i in range(s, e):
            kill[i] = True
        done += 1
    if not any(kill):
        return 0, 0, skipped
    out: list[str] = []
    blank_run = 0
    for i, l in enumerate(lines):
        if kill[i]:
            continue
        if l.strip() == "":
            blank_run += 1
            if blank_run > 2:
                continue
        else:
            blank_run = 0
        out.append(l)
    new = "\n".join(out)
    removed = len(text.encode("utf-8")) - len(new.encode("utf-8"))
    if apply:
        tmp = path + ".dd_tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(new)
        os.replace(tmp, path)
    return removed, done, skipped


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dead", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--only-prefix", nargs="*", default=[])
    a = ap.parse_args()
    per_file: dict[str, list] = defaultdict(list)
    with open(a.dead, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if a.only_prefix and not any(p[0].startswith(x) for x in a.only_prefix):
                continue
            per_file[p[0]].append((int(p[1]), int(p[2]), p[4], p[5]))
    tot = 0
    ndone = 0
    nskip = 0
    by_dir: dict[str, int] = defaultdict(int)
    for path, rows in per_file.items():
        full = os.path.join(a.repo, path)
        if not os.path.exists(full):
            nskip += len(rows)
            continue
        removed, done, skipped = process(full, rows, a.apply)
        tot += removed
        ndone += done
        nskip += skipped
        parts = path.split("/")
        by_dir["/".join(parts[:2]) if len(parts) > 2 else parts[0]] += removed
    print(f"files touched: {len(per_file)}  declarations removed: {ndone}  rows skipped: {nskip}")
    print(f"bytes {'removed' if a.apply else 'removable'}: {tot/1e6:.2f} MB")
    for d, b in sorted(by_dir.items(), key=lambda x: -x[1])[:25]:
        print(f"  {b/1e6:8.2f} MB  {d}")


if __name__ == "__main__":
    main()

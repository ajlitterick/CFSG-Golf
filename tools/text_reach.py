"""Source-level declaration reachability (no build needed).

    python3 -I tools/text_reach.py [--root-files Comparator/Solution.lean ...]
                                   [--root-names NAME ...] [--out text_reach.tsv] [--jobs 3]

Every live module (import-reachable from Comparator.Solution) is cut into top-level chunks:
one chunk per column-0 command.  Declaration chunks (theorem / lemma / def / abbrev / structure /
class / inductive / opaque / alias) get the last component of their name; everything else
(instances, notation, open, variable, attribute commands, declarations carrying non-trivial
attributes such as simp or ext) is an always-live chunk.

A chunk "mentions" a name if the name occurs as an identifier component in its text (comments
and strings stripped).  Reachability is the least set containing the always-live chunks and the
root chunks, closed under: a reached chunk reaches every declaration whose last name component
it mentions.  Name collisions make this an over-approximation of what is used, so chunks left
unreached are dead-code candidates of high precision; they still have to be confirmed by a build
(elaboration can use a declaration without naming it only through instances / attributes, which
are kept here).

Output TSV: one line per unreached declaration: path, first line, last line, bytes, kind, name.
Summary: dead bytes per top-level directory and the number of files with no reached declaration.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402

STRIP_RE = re.compile(r'"(?:\\.|[^"\\\n])*"|--[^\n]*|/-.*?-/', re.S)
TOKEN_RE = re.compile(r"[^\W\d][\w'!?]*")
DECL_KW = ("theorem", "lemma", "def", "abbrev", "structure", "class", "inductive", "opaque",
           "alias", "instance", "example", "axiom")
MODIFIERS = ("public", "private", "protected", "noncomputable", "nonrec", "unsafe", "partial",
             "meta", "scoped", "local")
HEAD_RE = re.compile(
    r"^((?:@\[[^\]]*\]\s*)*)((?:(?:" + "|".join(MODIFIERS) + r")\s+)*)(" + "|".join(DECL_KW) +
    r")\b\s*([^\s:({\[⦃]*)")
# attributes that do not make a declaration implicitly used by elaboration
HARMLESS_ATTR = {"expose", "reducible", "irreducible", "semireducible", "inline", "noinline",
                 "specialize", "macro_inline", "always_inline", "implicit_reducible",
                 "deprecated", "nolint", "inherit_doc", "instance_reducible"}
CONT_PREFIX = ("|", "termination_by", "decreasing_by", "where", "deriving", ")", "]", "}", "⟩",
               "with", ":=", "from", "at ", "<;>", "·", "then", "else")
# `set_option ... in`, `open ... in`, `omit ... in`, `include ... in` lines before a declaration
PREFIX_LINE_RE = re.compile(r"^(?:set_option|open|omit|include|variable)\b[^\n]*\bin\s*$")
PREFIX_RE = re.compile(r"\A(?:(?:set_option|open|omit|include|variable)\b[^\n]*\bin\s*\n)+")
INERT_RE = re.compile(r"\A(?:(?:public\s+)?(?:meta\s+)?import\b|module\b|prelude\b|namespace\b|end\b|"
                      r"(?:public\s+|noncomputable\s+|private\s+)*section\b|universe\b|"
                      r"open\b(?![^\n]*\bin[ \t]*(?:\n|\Z))(?![^\n]*(?:\(|\bhiding\b|\brenaming\b)))")
NAME_OK = re.compile(r"[\w.'!?«»]+")
KIND_DECL, KIND_OTHER, KIND_EXAMPLE = 0, 1, 2


def strip(text: str) -> str:
    """Remove comments and strings, keeping the line structure."""
    return STRIP_RE.sub(lambda m: "\n" * m.group(0).count("\n"), text)


# indented lines that start a command: declarations (their keywords cannot occur inside a
# term) and section-structure commands
IND_START_RE = re.compile(
    r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*(?:" + "|".join(DECL_KW) + r")\s+[^\W\d:=]"
    r"|instance\b|example\b"
    r"|(?:namespace|end|variable|universe|attribute|mutual|export)\b"
    r"|(?:(?:public|noncomputable|private)\s+)*section\b")


def chunks_of(text: str):
    """Return ([(first_line, last_line_exclusive, kind, kw, name, text_of_chunk)], lines).

    A chunk starts at a column-0 line (unless it continues the previous command) or at an
    indented line that begins a declaration or a section command; attribute lines and
    `... in` prefix lines directly above a declaration belong to it.
    """
    lines = strip(text).split("\n")
    n = len(lines)
    starts: list[int] = []
    pending = -1          # index in `starts` of an attribute / prefix line awaiting its command
    for i, line in enumerate(lines):
        if not line.strip():
            continue
        indented = line[0] in " \t"
        ls = line.lstrip() if indented else line
        is_attr_only = ls.startswith("@[") and HEAD_RE.match(ls) is None
        is_prefix = PREFIX_LINE_RE.match(ls) is not None
        if pending >= 0:
            # the line after an attribute / prefix line continues that chunk
            if is_attr_only or is_prefix:
                continue
            if indented and not (IND_START_RE.match(ls) or HEAD_RE.match(ls)):
                # an indented prefix that was not followed by a command: not a chunk start
                if starts and starts[-1] == pending and lines[pending][0] in " \t":
                    starts.pop()
            pending = -1
            continue
        if indented:
            if IND_START_RE.match(ls) or (ls.startswith("@[") and HEAD_RE.match(ls)):
                starts.append(i)
            elif is_attr_only or is_prefix:
                starts.append(i)
                pending = i
            continue
        if line.startswith(CONT_PREFIX):
            continue
        starts.append(i)
        if is_attr_only or is_prefix:
            pending = i
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else n
        body = "\n".join(lines[s:e])
        # first non-blank lines, dedented (a stripped doc comment may sit between a
        # `set_option ... in` line and its declaration)
        head = "\n".join([l.lstrip() for l in lines[s:e] if l.strip()][:8])
        m = HEAD_RE.match(PREFIX_RE.sub("", head))
        if m is None:
            out.append((s, e, KIND_OTHER, "", "", body))
            continue
        attrs = set()
        for a in re.findall(r"@\[([^\]]*)\]", m.group(1)):
            for part in a.split(","):
                w = part.strip().split(" ")[0].split("(")[0]
                if w:
                    attrs.add(w)
        kw, name = m.group(3), m.group(4)
        if kw == "example":
            out.append((s, e, KIND_EXAMPLE, kw, "", body))
        elif (kw in ("instance", "axiom") or not name or (attrs - HARMLESS_ATTR)
              or NAME_OK.fullmatch(name) is None):
            out.append((s, e, KIND_OTHER, kw, name.split(".")[-1], body))
        else:
            out.append((s, e, KIND_DECL, kw, name.split(".")[-1], body))
    return out, lines


_NAMES: dict[str, int] = {}


def _init(names_path: str) -> None:
    global _NAMES
    with open(names_path, encoding="utf-8") as f:
        _NAMES = {n: i for i, n in enumerate(f.read().split("\n")) if n}


def pass1(path: str):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return []
    ch, _ = chunks_of(text)
    return [c[4] for c in ch if c[4]]


def pass2(path: str):
    with open(path, encoding="utf-8", errors="replace") as f:
        text = f.read()
    raw_lines = text.split("\n")
    ch, _ = chunks_of(text)
    res = []
    for (s, e, kind, kw, name, body) in ch:
        if kind == KIND_OTHER and INERT_RE.match(body.lstrip()):
            ids = set()   # imports, namespace/section brackets and plain `open` use nothing
        else:
            ids = {_NAMES[t] for t in set(TOKEN_RE.findall(body)) if t in _NAMES}
        nid = _NAMES.get(name, -1) if name else -1
        if kind == KIND_DECL:
            ids.discard(nid)
        nbytes = sum(len(l.encode("utf-8")) + 1 for l in raw_lines[s:e])
        # first word after any `open ... in` / `set_option ... in` prefix lines, so that
        # `open Lean in elab ...` is seen as an `elab` command, not as an `open`
        rest = PREFIX_RE.sub("", "\n".join([l.lstrip() for l in body.split("\n") if l.strip()][:8]))
        fw = rest.split(None, 1)[0] if rest.strip() else (body.split(None, 1)[0] if body.strip() else "")
        res.append((s, e, kind, kw, nid, nbytes, np.fromiter(ids, dtype=np.uint32, count=len(ids)), fw))
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default=os.getcwd())
    ap.add_argument("--root", default="Comparator.Solution")
    ap.add_argument("--root-files", nargs="*", default=["Comparator/Solution.lean"])
    ap.add_argument("--root-names", nargs="*", default=[])
    ap.add_argument("--all-modules", action="store_true",
                    help="every module outside the root's import closure is a root file "
                         "(nothing they use is reported dead)")
    ap.add_argument("--extra-roots", nargs="*", default=[],
                    help="further root modules; files only they reach are root files")
    ap.add_argument("--out", default="text_reach.tsv")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--tmp", default=None)
    ap.add_argument("--save", default=None, help="directory for the mention graph (binary arrays)")
    ap.add_argument("--limit", type=int, default=0, help="only the first N live files (testing)")
    a = ap.parse_args()
    g = Graph.load(a.repo)
    primary = g.reachable(a.root)
    extra: set[str] = set()
    for r in a.extra_roots:
        extra |= g.reachable(r)
    if a.all_modules:
        extra = set(g.mods)
    extra -= primary
    live = sorted(primary | extra)
    a.root_files = list(a.root_files) + [g.mods[m].path for m in sorted(extra)]
    if extra:
        print(f"extra root files: {len(extra)}", flush=True)
    if a.limit:
        live = live[:a.limit]
    paths = [g.mods[m].path for m in live]
    full = [os.path.join(a.repo, p) for p in paths]
    print(f"live modules: {len(paths)}", flush=True)

    with Pool(a.jobs) as pool:
        names: set[str] = set()
        for lst in pool.imap_unordered(pass1, full, chunksize=500):
            names.update(lst)
    names_list = sorted(names)
    tmp = a.tmp or os.path.join(a.repo, ".cache")
    os.makedirs(tmp, exist_ok=True)
    names_path = os.path.join(tmp, "text_reach_names.txt")
    with open(names_path, "w", encoding="utf-8") as f:
        f.write("\n".join(names_list))
    name_id = {n: i for i, n in enumerate(names_list)}
    print(f"distinct declaration names (last component): {len(names_list)}", flush=True)

    # chunk table
    c_file, c_s, c_e, c_kind, c_kw, c_name, c_bytes = [], [], [], [], [], [], []
    tok_parts, tok_len = [], []
    c_first: list[str] = []
    with Pool(a.jobs, initializer=_init, initargs=(names_path,)) as pool:
        for fi, res in enumerate(pool.imap(pass2, full, chunksize=200)):
            for (s, e, kind, kw, nid, nbytes, ids, fw) in res:
                c_first.append(fw)
                c_file.append(fi); c_s.append(s); c_e.append(e); c_kind.append(kind)
                c_kw.append(kw); c_name.append(nid); c_bytes.append(nbytes)
                tok_parts.append(ids); tok_len.append(len(ids))
            if fi % 20000 == 0:
                print(f"  parsed {fi} files, {len(c_file)} chunks", flush=True)
    n = len(c_file)
    c_kind_a = np.array(c_kind, dtype=np.int8)
    c_name_a = np.array(c_name, dtype=np.int64)
    c_bytes_a = np.array(c_bytes, dtype=np.int64)
    c_file_a = np.array(c_file, dtype=np.int64)
    indptr = np.zeros(n + 1, dtype=np.int64)
    np.cumsum(np.array(tok_len, dtype=np.int64), out=indptr[1:])
    toks = np.concatenate(tok_parts) if tok_parts else np.zeros(0, dtype=np.uint32)
    del tok_parts
    print(f"chunks: {n}  (declarations {int((c_kind_a == KIND_DECL).sum())}, always-live "
          f"{int((c_kind_a == KIND_OTHER).sum())}, examples {int((c_kind_a == KIND_EXAMPLE).sum())}); "
          f"mention edges: {len(toks)}", flush=True)

    if a.save:
        os.makedirs(a.save, exist_ok=True)
        root0 = c_kind_a == KIND_OTHER
        rf = {i for i, p in enumerate(paths) if p in set(a.root_files)}
        if rf:
            root0 = root0 | np.isin(c_file_a, np.array(sorted(rf)))
        for nm, arr in (("indptr.i64", indptr), ("toks.u32", toks),
                        ("kind.i8", c_kind_a), ("name.i64", c_name_a),
                        ("bytes.i64", c_bytes_a), ("file.i64", c_file_a),
                        ("sline.i64", np.array(c_s, dtype=np.int64)),
                        ("eline.i64", np.array(c_e, dtype=np.int64)),
                        ("root.u8", root0.astype(np.uint8))):
            arr.tofile(os.path.join(a.save, nm))
        with open(os.path.join(a.save, "paths.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(paths))
        with open(os.path.join(a.save, "names.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(names_list))
        with open(os.path.join(a.save, "kw.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(c_kw))
        with open(os.path.join(a.save, "first.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(w.replace("\n", " ") for w in c_first))
        # file-level import graph over the live modules (indices into paths)
        midx = {m: i for i, m in enumerate(live)}
        fptr = np.zeros(len(live) + 1, dtype=np.int64)
        fimp: list[int] = []
        for i, m in enumerate(live):
            fimp.extend(sorted({midx[x] for _k, x in g.mods[m].imports if x in midx}))
            fptr[i + 1] = len(fimp)
        fptr.tofile(os.path.join(a.save, "fimp_ptr.i64"))
        np.array(fimp, dtype=np.uint32).tofile(os.path.join(a.save, "fimp.u32"))
        print(f"saved graph to {a.save}", flush=True)

    # name id -> declaration chunks carrying it
    decl_idx = np.nonzero(c_kind_a == KIND_DECL)[0]
    order = decl_idx[np.argsort(c_name_a[decl_idx], kind="stable")]
    sorted_names = c_name_a[order]
    nn = len(names_list)
    first = np.searchsorted(sorted_names, np.arange(nn), side="left")
    last = np.searchsorted(sorted_names, np.arange(nn), side="right")

    reached = c_kind_a == KIND_OTHER
    root_fi = {i for i, p in enumerate(paths) if p in set(a.root_files)}
    if root_fi:
        reached |= np.isin(c_file_a, np.array(sorted(root_fi)))
    for rn in a.root_names:
        if rn in name_id:
            reached |= (c_name_a == name_id[rn]) & (c_kind_a == KIND_DECL)
    name_seen = np.zeros(nn, dtype=bool)
    frontier = np.nonzero(reached)[0]
    rounds = 0
    while len(frontier):
        rounds += 1
        # names mentioned by the frontier
        segs = [toks[indptr[i]:indptr[i + 1]] for i in frontier]
        ment = np.unique(np.concatenate(segs)) if segs else np.zeros(0, dtype=np.uint32)
        new_names = ment[~name_seen[ment]]
        name_seen[new_names] = True
        nxt = [order[first[x]:last[x]] for x in new_names]
        cand = np.unique(np.concatenate(nxt)) if nxt else np.zeros(0, dtype=np.int64)
        cand = cand[~reached[cand]]
        reached[cand] = True
        frontier = cand
        print(f"  round {rounds}: +{len(cand)} declarations", flush=True)

    dead = np.nonzero(~reached & (c_kind_a != KIND_OTHER))[0]
    total_bytes = sum(g.mods[m].bytes for m in live)
    dead_bytes = int(c_bytes_a[dead].sum())
    print(f"\nunreached declarations: {len(dead)} of {len(decl_idx)}  "
          f"({dead_bytes/1e6:.1f} MB of {total_bytes/1e6:.1f} MB live source, "
          f"{100*dead_bytes/total_bytes:.2f}%)")
    by_dir: dict[str, int] = defaultdict(int)
    file_dead: dict[int, int] = defaultdict(int)
    for i in dead:
        p = paths[c_file[i]]
        parts = p.split("/")
        by_dir["/".join(parts[:2]) if len(parts) > 2 else parts[0]] += c_bytes[i]
        file_dead[c_file[i]] += 1
    # files with no reached declaration chunk at all
    decl_per_file: dict[int, int] = defaultdict(int)
    for i in np.nonzero(c_kind_a != KIND_OTHER)[0]:
        decl_per_file[c_file[i]] += 1
    all_dead_files = [fi for fi, k in file_dead.items() if k == decl_per_file[fi]]
    adf_bytes = sum(g.mods[live[fi]].bytes for fi in all_dead_files)
    print(f"files whose declarations are all unreached: {len(all_dead_files)} ({adf_bytes/1e6:.1f} MB)")
    print("dead bytes by directory:")
    for d, b in sorted(by_dir.items(), key=lambda x: -x[1])[:40]:
        print(f"  {b/1e6:8.2f} MB  {d}")
    with open(a.out, "w", encoding="utf-8") as f:
        for i in dead:
            nm = names_list[c_name[i]] if c_name[i] >= 0 else ""
            f.write(f"{paths[c_file[i]]}\t{c_s[i]+1}\t{c_e[i]}\t{c_bytes[i]}\t{c_kw[i]}\t{nm}\n")
    with open(a.out + ".files", "w", encoding="utf-8") as f:
        for fi in sorted(all_dead_files):
            f.write(paths[fi] + "\n")
    print(f"wrote {a.out} and {a.out}.files")


if __name__ == "__main__":
    main()

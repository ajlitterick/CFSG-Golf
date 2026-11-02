"""Import graph of the CFSG repository (repo-local modules only).

Parses the import header of every .lean file under the module roots, builds the
directed import graph, and offers reachability queries.  Mathlib / TauCeti /
other external modules are recorded as edges but have no node data.

Usage as a library:
    from cfsg_modules import Graph
    g = Graph.load(repo)            # cached in <repo>/.cache/graph.json
    g.reachable("Comparator.Solution")

Run with `python3 -I` from the repository root (or pass the root).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from collections import deque
from dataclasses import dataclass, field

ROOT_DIRS = ("CFSG", "Certificates", "Comparator")
ROOT_FILES = (
    "CFSG", "Certificates", "CFSGWithCertificates", "CertifiedMilestones",
    "CertifiedResults", "CertifiedYardstones", "YardstoneContract",
)
IMPORT_RE = re.compile(r"^(public\s+)?(meta\s+)?import(\s+all)?\s+([\w.«»]+)")
EXTERNAL_PREFIXES = ("Mathlib", "TauCeti", "Lean", "Init", "Std", "Batteries",
                     "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient",
                     "ImportGraph", "Cli")


@dataclass
class Module:
    path: str
    bytes: int
    lines: int
    imports: list[tuple[str, str]] = field(default_factory=list)  # (kind, module)
    # kind in {"public", "private", "meta", "all", "public all", "public meta", ...}


def parse_imports(path: str) -> list[tuple[str, str]]:
    """Return (kind, module) pairs for the import header of a Lean file."""
    out = []
    with open(path, encoding="utf-8", errors="replace") as f:
        for line in f:
            s = line.strip()
            if not s or s == "module" or s.startswith("--") or s.startswith("/-") or s.startswith("-/"):
                continue
            m = IMPORT_RE.match(s)
            if m:
                kind = " ".join(k for k in (
                    "public" if m.group(1) else "",
                    "meta" if m.group(2) else "",
                    "all" if m.group(3) else "") if k) or "private"
                out.append((kind, m.group(4)))
            elif s.startswith(("prelude", "set_option", "#")):
                continue
            else:
                break  # first non-import token ends the header
    return out


def module_of_path(path: str) -> str:
    assert path.endswith(".lean")
    return path[:-5].replace(os.sep, ".")


def path_of_module(mod: str) -> str:
    return mod.replace(".", os.sep) + ".lean"


def is_external(mod: str) -> bool:
    return mod.split(".")[0] in EXTERNAL_PREFIXES


def git_tree_hash(repo: str) -> str:
    try:
        return subprocess.run(["git", "-C", repo, "rev-parse", "HEAD^{tree}"],
                              capture_output=True, text=True, check=True).stdout.strip()
    except Exception:
        return "nogit"


class Graph:
    def __init__(self, repo: str):
        self.repo = repo
        self.mods: dict[str, Module] = {}
        self._rev: dict[str, list[str]] | None = None

    # ---------- construction ----------
    @classmethod
    def build(cls, repo: str) -> "Graph":
        g = cls(repo)
        for root in ROOT_DIRS:
            top = os.path.join(repo, root)
            for dp, _dn, fn in os.walk(top):
                for f in fn:
                    if f.endswith(".lean"):
                        g._add(os.path.relpath(os.path.join(dp, f), repo))
        for name in ROOT_FILES:
            p = name + ".lean"
            if os.path.exists(os.path.join(repo, p)):
                g._add(p)
        return g

    def _add(self, rel: str) -> None:
        full = os.path.join(self.repo, rel)
        with open(full, "rb") as f:
            data = f.read()
        self.mods[module_of_path(rel)] = Module(
            path=rel, bytes=len(data), lines=data.count(b"\n"),
            imports=parse_imports(full))

    @classmethod
    def load(cls, repo: str, use_cache: bool = True) -> "Graph":
        cache_dir = os.path.join(repo, ".cache")
        cache = os.path.join(cache_dir, "graph.json")
        key = git_tree_hash(repo)
        if use_cache and os.path.exists(cache):
            with open(cache) as f:
                d = json.load(f)
            if d.get("key") == key and not _dirty(repo):
                g = cls(repo)
                g.mods = {m: Module(**v) for m, v in d["mods"].items()}
                for v in g.mods.values():
                    v.imports = [tuple(x) for x in v.imports]
                return g
        g = cls.build(repo)
        if use_cache and not _dirty(repo):
            os.makedirs(cache_dir, exist_ok=True)
            with open(cache, "w") as f:
                json.dump({"key": key, "mods": {m: v.__dict__ for m, v in g.mods.items()}}, f)
        return g

    # ---------- queries ----------
    def imports_of(self, mod: str, internal_only: bool = True) -> list[str]:
        m = self.mods.get(mod)
        if m is None:
            return []
        return [x for _k, x in m.imports if (x in self.mods) or not internal_only]

    def reachable(self, root: str = "Comparator.Solution",
                  override: dict[str, list[str]] | None = None) -> set[str]:
        """Internal modules transitively imported by `root` (including root)."""
        seen: set[str] = set()
        dq = deque([root])
        while dq:
            m = dq.popleft()
            if m in seen or m not in self.mods:
                continue
            seen.add(m)
            nxt = override.get(m) if override and m in override else self.imports_of(m)
            dq.extend(x for x in nxt if x not in seen)
        return seen

    def external_reachable(self, internal: set[str]) -> set[str]:
        ext: set[str] = set()
        for m in internal:
            for _k, x in self.mods[m].imports:
                if x not in self.mods:
                    ext.add(x)
        return ext

    def reverse(self) -> dict[str, list[str]]:
        if self._rev is None:
            rev: dict[str, list[str]] = {m: [] for m in self.mods}
            for m, v in self.mods.items():
                for _k, x in v.imports:
                    if x in rev:
                        rev[x].append(m)
            self._rev = rev
        return self._rev

    def dependents(self, mod: str) -> set[str]:
        """Modules that transitively import `mod` (excluding mod)."""
        rev = self.reverse()
        seen: set[str] = set()
        dq = deque(rev.get(mod, []))
        while dq:
            m = dq.popleft()
            if m in seen:
                continue
            seen.add(m)
            dq.extend(rev[m])
        return seen

    def is_downstream(self, a: str, b: str) -> bool:
        """True if module a transitively imports module b."""
        return b in self.reachable(a)


def _dirty(repo: str) -> bool:
    try:
        r = subprocess.run(["git", "-C", repo, "status", "--porcelain", "--", "*.lean"],
                           capture_output=True, text=True, check=True)
        return bool(r.stdout.strip())
    except Exception:
        return True


if __name__ == "__main__":
    repo = sys.argv[1] if len(sys.argv) > 1 else os.getcwd()
    g = Graph.load(repo)
    r = g.reachable()
    print(f"modules: {len(g.mods)}  reachable from Comparator.Solution: {len(r)}  "
          f"edges: {sum(len(m.imports) for m in g.mods.values())}")

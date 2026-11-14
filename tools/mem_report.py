"""Summarise one or more tools/mem_watch.py JSONL files.

    python3 -I tools/mem_report.py .cache/membench/full-*.jsonl [--top 40] [--csv out.csv]

Sections:
  1. headline: duration, lowest MemAvailable, peak swap, worst memory pressure (PSI);
  2. biggest modules by peak anonymous memory (with source lines/bytes and, if built, the
     olean size, so you can see whether size predicts memory);
  3. pressure episodes (MemAvailable low, swapping, or PSI full) and the lean processes that
     were running during each -- the usual culprits for thrashing are *combinations* of
     large modules built concurrently, not one module alone;
  4. concurrency: how total lean memory grows with the number of parallel lean processes;
  5. advice: the largest safe `-j`/`--threads` for your RAM given the observed peaks.

Multiple files are merged per module by taking the maximum.  Files named module-*.jsonl
(from `mem_watch.py module`) are kept apart: they supply each module's *isolated* peak.

    --json findings.json   machine-readable hand-off for a fixer (schema: docs in
                           tools/MEMORY_AGENTS.md)
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cfsg_modules import Graph  # noqa: E402

LIB = os.path.join(".lake", "build", "lib", "lean")


def load(paths):
    for p in paths:
        with open(p) as f:
            for line in f:
                try:
                    yield json.loads(line)
                except json.JSONDecodeError:
                    continue  # truncated last line of an interrupted run


def olean_mb(mod: str) -> float | None:
    p = os.path.join(LIB, mod.replace(".", os.sep) + ".olean")
    try:
        return os.path.getsize(p) / 2**20
    except OSError:
        return None


def episodes(samples, avail_gb, psi, gap=10.0):
    """Group consecutive 'bad' samples into episodes."""
    out, cur = [], None
    for r in samples:
        s = r["sys"]
        bad = (s["avail_mb"] < avail_gb * 1024 or (s.get("psi_full") or 0) >= psi
               or (s.get("pswpin_ps") or 0) > 1000)
        if bad:
            if cur and r["t"] - cur["end"] <= gap:
                cur["end"] = r["t"]
            else:
                cur = {"start": r["t"], "end": r["t"], "min_avail": 1e18, "psi": 0.0,
                       "swap": 0.0, "mods": {}, "peak_anon": 0.0}
                out.append(cur)
            cur["min_avail"] = min(cur["min_avail"], s["avail_mb"])
            cur["psi"] = max(cur["psi"], s.get("psi_full") or 0)
            cur["swap"] = max(cur["swap"], s["swap_used_mb"])
            cur["peak_anon"] = max(cur["peak_anon"], sum(p["anon"] for p in r["lean"]))
            for p in r["lean"]:
                cur["mods"][p["mod"]] = max(cur["mods"].get(p["mod"], 0), p["anon"])
    return out


def write_findings(a, samples, rows, mods, eps, gev, isolated, total_mb) -> None:
    flag_mb = a.flag_gb * 1024
    ep_top: dict[str, int] = {}
    for e in eps:
        for mname, _v in sorted(e["mods"].items(), key=lambda kv: -kv[1])[:3]:
            ep_top[mname] = ep_top.get(mname, 0) + 1
    forced = {e["mod"] for _t, e in gev if e["ev"] == "resume" and e["forced"]}
    paused_s: dict[str, float] = {}
    for _t, e in gev:
        if e["ev"] == "resume":
            paused_s[e["mod"]] = paused_s.get(e["mod"], 0) + e["held_s"]
    out_mods = []
    for r in rows:
        name = r["module"]
        reasons = []
        if r["peak_anon_mb"] >= flag_mb:
            reasons.append(f"peak_anon>={a.flag_gb:g}GB")
        if name in ep_top:
            reasons.append("top3_in_pressure_episode")
        if name in forced:
            reasons.append("forced_resume")
        if not reasons and r["peak_anon_mb"] < flag_mb / 3:
            continue  # keep the list short: unflagged modules well below the threshold
        iso = isolated.get(name)
        out_mods.append({
            **{k: r[k] for k in ("module", "peak_anon_mb", "peak_rss_mb", "cpu_s", "seen_s",
                                 "cpu_per_wall", "lines", "bytes", "olean_mb")},
            "flagged": bool(reasons), "reasons": reasons,
            "isolated_peak_anon_mb": iso,
            "alone_vs_together": (None if iso is None else
                                  "problem_is_concurrency" if iso < 0.6 * r["peak_anon_mb"]
                                  else "big_alone"),
            "pressure_episodes_top3": ep_top.get(name, 0),
            "guard_paused_s": paused_s.get(name, 0),
            "co_running_at_peak": [{"module": m, "anon_mb": v} for m, v in mods[name]["co"]],
        })
    out_mods.sort(key=lambda m: (not m["flagged"], -m["peak_anon_mb"]))
    f = {
        "version": 1,
        "created": __import__("time").strftime("%Y-%m-%dT%H:%M:%S%z"),
        "inputs": a.files,
        "host": {"mem_total_gb": round(total_mb / 1024, 1)},
        "thresholds": {"flag_gb": a.flag_gb, "pressure_avail_gb": a.avail_gb,
                       "pressure_psi_full": a.psi},
        "summary": {
            "hours": round(samples[-1]["t"] / 3600, 2),
            "min_avail_gb": round(min(r["sys"]["avail_mb"] for r in samples) / 1024, 1),
            "peak_swap_gb": round(max(r["sys"]["swap_used_mb"] for r in samples) / 1024, 1),
            "max_psi_full": max((r["sys"].get("psi_full") or 0) for r in samples),
            "peak_lean_anon_gb": round(max(sum(p["anon"] for p in r["lean"])
                                           for r in samples) / 1024, 1),
            "pressure_episodes": len(eps),
            "guard_pauses": sum(1 for _t, e in gev if e["ev"] == "pause"),
            "modules_seen": len(rows),
            "modules_flagged": sum(1 for m in out_mods if m["flagged"]),
        },
        "modules": out_mods,
        "episodes": [{"start_s": e["start"], "end_s": e["end"],
                      "min_avail_gb": round(e["min_avail"] / 1024, 1),
                      "peak_lean_anon_gb": round(e["peak_anon"] / 1024, 1),
                      "modules": [{"module": m, "anon_mb": v} for m, v in
                                  sorted(e["mods"].items(), key=lambda kv: -kv[1])[:6]]}
                     for e in eps],
    }
    with open(a.json, "w") as fh:
        json.dump(f, fh, indent=1)


def pearson(xs, ys):
    n = len(xs)
    if n < 3:
        return None
    mx, my = sum(xs) / n, sum(ys) / n
    sx = math.sqrt(sum((x - mx) ** 2 for x in xs))
    sy = math.sqrt(sum((y - my) ** 2 for y in ys))
    return None if sx == 0 or sy == 0 else sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / (sx * sy)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="+")
    ap.add_argument("--top", type=int, default=30)
    ap.add_argument("--csv", help="write the full per-module table here")
    ap.add_argument("--avail-gb", type=float, default=3.0,
                    help="MemAvailable below this counts as pressure (default 3)")
    ap.add_argument("--psi", type=float, default=5.0,
                    help="PSI memory 'full' avg10 %% counted as pressure (default 5)")
    ap.add_argument("--ram-gb", type=float, help="budget for the advice section "
                    "(default: MemTotal seen in the log)")
    ap.add_argument("--repo", default=".")
    ap.add_argument("--json", help="write findings for an automated fixer to this file")
    ap.add_argument("--flag-gb", type=float, default=6.0,
                    help="flag modules whose peak anonymous memory is at least this (default 6)")
    a = ap.parse_args()

    iso_files = [f for f in a.files if os.path.basename(f).startswith("module-")]
    full_files = [f for f in a.files if f not in iso_files]
    isolated: dict[str, float] = {}
    for f in iso_files:
        name = os.path.basename(f)[len("module-"):].rsplit("-", 2)[0]
        peak = max((p["anon"] for r in load([f]) for p in r["lean"]), default=0)
        isolated[name] = max(isolated.get(name, 0), peak)
    samples = list(load(full_files))  # file order; t restarts per file
    if not samples:
        sys.exit("no full-build samples (only module-*.jsonl given?)")
    mods: dict[str, dict] = {}
    for r in samples:
        for p in r["lean"]:
            m = mods.setdefault(p["mod"], {"anon": 0, "rss": 0, "file": 0, "swap": 0,
                                           "hwm": 0, "seen": 0, "thr": 0, "cpu": 0, "co": []})
            for k in ("anon", "rss", "file", "swap", "hwm", "thr"):
                m[k] = max(m[k], p[k])
            m["cpu"] = max(m["cpu"], p.get("cpu") or 0)  # cumulative, so max = last seen
            if p["anon"] >= m["anon"]:  # at this module's peak: who else was running?
                m["co"] = sorted(((q["mod"], q["anon"]) for q in r["lean"] if q is not p),
                                 key=lambda x: -x[1])[:5]
            m["seen"] += 1
    interval = (samples[-1]["t"] - samples[0]["t"]) / max(1, len(samples) - 1)

    total_mb = samples[0]["sys"]["total_mb"]
    print(f"== {len(samples)} samples over {samples[-1]['t'] / 3600:.2f} h "
          f"(~{interval:.1f}s apart), {len(mods)} distinct modules seen, "
          f"MemTotal {total_mb / 1024:.1f} GB")
    print(f"   lowest MemAvailable {min(r['sys']['avail_mb'] for r in samples) / 1024:.1f} GB, "
          f"peak swap {max(r['sys']['swap_used_mb'] for r in samples) / 1024:.1f} GB, "
          f"max PSI full avg10 {max((r['sys'].get('psi_full') or 0) for r in samples):.1f}%, "
          f"peak total lean anon {max(sum(p['anon'] for p in r['lean']) for r in samples) / 1024:.1f} GB")
    oth = max(samples, key=lambda r: r["other_rss"])
    if oth["other_rss"] > 1024:
        print(f"   non-lean build processes peaked at {oth['other_rss'] / 1024:.1f} GB "
              f"(largest: {oth['other_top']}) -- linking/C compilation of precompiled modules?")

    g = None
    try:
        g = Graph.load(a.repo)
    except Exception as e:  # not run from the repo, or no sources
        print(f"   (no source info: {e})", file=sys.stderr)

    rows = []
    for name, m in mods.items():
        gm = g.mods.get(name) if g else None
        rows.append({"module": name, "peak_anon_mb": m["anon"], "peak_rss_mb": m["rss"],
                     "peak_file_mb": m["file"], "swap_mb": m["swap"], "vmhwm_mb": m["hwm"],
                     "samples": m["seen"], "seen_s": round(m["seen"] * interval, 1),
                     "cpu_s": m["cpu"], "threads": m["thr"],
                     "cpu_per_wall": round(m["cpu"] / (m["seen"] * interval), 2)
                     if m["seen"] and m["cpu"] else None,
                     "lines": gm.lines if gm else None, "bytes": gm.bytes if gm else None,
                     "olean_mb": olean_mb(name)})
    rows.sort(key=lambda r: -r["peak_anon_mb"])

    print(f"\n== top {a.top} modules by peak anonymous memory")
    print(f"{'peak anon':>10} {'rss':>8} {'swap':>7} {'seen s':>7} {'cpu s':>7} {'cpu/wall':>8} "
          f"{'lines':>8} {'olean':>7}  module")
    for r in rows[:a.top]:
        print(f"{r['peak_anon_mb']:>8.0f}MB {r['peak_rss_mb']:>6.0f}MB {r['swap_mb']:>5.0f}MB "
              f"{r['seen_s']:>7.0f} {r['cpu_s']:>7.0f} "
              f"{(format(r['cpu_per_wall'], '.1f') if r['cpu_per_wall'] is not None else '-'):>8} "
              f"{r['lines'] if r['lines'] is not None else '-':>8} "
              f"{(format(r['olean_mb'], '.1f') + 'M') if r['olean_mb'] is not None else '-':>7}  "
              f"{r['module']}")
    print(f"\n== top {a.top} modules by CPU time (cpu s is a lower bound: last sample before exit)")
    print("   cpu/wall << threads while MemAvailable is low means the module was stalled on "
          "swap, not computing")
    for r in sorted(rows, key=lambda r: -r["cpu_s"])[:a.top]:
        print(f"  {r['cpu_s']:>7.0f}s cpu  {r['seen_s']:>6.0f}s wall  "
              f"{(format(r['cpu_per_wall'], '.1f') if r['cpu_per_wall'] is not None else '-'):>5} cpu/wall"
              f"  peak {r['peak_anon_mb']:>6.0f}MB  {r['module']}")
    print(f"   total CPU across modules seen: {sum(r['cpu_s'] for r in rows) / 3600:.1f} h")
    xs = [(math.log1p(r["lines"]), math.log1p(r["peak_anon_mb"])) for r in rows if r["lines"]]
    c = pearson([x for x, _ in xs], [y for _, y in xs])
    if c is not None:
        print(f"   corr(log lines, log peak anon) = {c:.2f}"
              + ("  (source size predicts memory poorly: look at the tactics/terms, not length)"
                 if c < 0.5 else ""))
    buckets = [(0, 500), (500, 1000), (1000, 2000), (2000, 4000), (4000, 8000), (8000, 1e9)]
    print("   distribution (peak anon): " + ", ".join(
        f"{lo / 1000:g}-{(hi / 1000 if hi < 1e8 else float('inf')):g}G: "
        f"{sum(1 for r in rows if lo <= r['peak_anon_mb'] < hi)}" for lo, hi in buckets))

    eps = episodes(samples, a.avail_gb, a.psi)
    print(f"\n== pressure episodes (MemAvailable < {a.avail_gb:g} GB, PSI full >= {a.psi:g}%, "
          f"or swap-in > 1000 pages/s): {len(eps)}")
    for e in sorted(eps, key=lambda e: e["min_avail"])[:10]:
        ms = sorted(e["mods"].items(), key=lambda kv: -kv[1])[:5]
        print(f"  t={e['start']:.0f}-{e['end']:.0f}s  min avail {e['min_avail'] / 1024:.1f}G  "
              f"swap {e['swap'] / 1024:.1f}G  psi {e['psi']:.0f}%  lean anon {e['peak_anon'] / 1024:.1f}G")
        for mname, v in ms:
            print(f"      {v / 1024:5.1f}G  {mname}")

    gev = [(r["t"], e) for r in samples for e in r.get("guard", [])]
    if gev:
        held: dict[str, float] = {}
        for _t, e in gev:
            if e["ev"] == "resume":
                held[e["mod"]] = held.get(e["mod"], 0) + e["held_s"]
        npause = sum(1 for _t, e in gev if e["ev"] == "pause")
        print(f"\n== guard: {npause} pauses, {sum(held.values()):.0f}s total paused time "
              f"(wall time traded for memory)")
        for mname, v in sorted(held.items(), key=lambda kv: -kv[1])[:10]:
            print(f"  {v:7.0f}s paused  {mname}")
        forced = sum(1 for _t, e in gev if e["ev"] == "resume" and e["forced"])
        if forced:
            print(f"  {forced} forced resume(s): the paused process was the only one left to "
                  "run; if memory was still low then, that module alone is too big")

    print("\n== concurrency (samples grouped by number of live lean processes)")
    by_n: dict[int, list[float]] = {}
    for r in samples:
        by_n.setdefault(len(r["lean"]), []).append(sum(p["anon"] for p in r["lean"]))
    for n in sorted(by_n):
        v = sorted(by_n[n])
        print(f"  {n:2d} procs: {len(v):6d} samples  median {v[len(v) // 2] / 1024:5.1f}G  "
              f"max {v[-1] / 1024:5.1f}G")

    ram = (a.ram_gb or total_mb / 1024)
    budget = ram * 0.8
    peaks = sorted((r["peak_anon_mb"] for r in rows), reverse=True)
    print(f"\n== advice (budget {budget:.0f} GB = 80% of {ram:.0f} GB)")
    for k in [k for k in (1, 2, 3, 4, 6, 8) if k <= len(peaks)]:
        worst = sum(peaks[:k]) / 1024
        print(f"  {k} concurrent: worst case = {k} biggest modules together = {worst:.1f} GB "
              f"{'OK' if worst <= budget else 'EXCEEDS budget'}")
    print("  (worst case is pessimistic: Lake rarely schedules the k biggest at once; compare "
          "with the observed maxima above.)")

    if a.json:
        write_findings(a, samples, rows, mods, eps, gev if gev else [], isolated, total_mb)
        print(f"\nwrote {a.json}")

    if a.csv:
        with open(a.csv, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(rows[0]))
            w.writeheader()
            w.writerows(rows)
        print(f"\nwrote {a.csv}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

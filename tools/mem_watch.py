"""Sample memory use of a Lean/Lake build, per module, to find modules that blow up RAM.

Stdlib only, Linux/WSL only (reads /proc).  Writes one JSON object per sample to a JSONL
file (default .cache/membench/<label>.jsonl); analyse it with tools/mem_report.py.

    # run a command under the sampler (sampler follows that command's process tree)
    python3 -I tools/mem_watch.py run --label full -- lake build
    python3 -I tools/mem_watch.py run --label sub -- lake build +Comparator.Solution

    # or attach to an already-running build (every process whose executable is `lean`)
    python3 -I tools/mem_watch.py attach --label full

    # same, but pause the biggest lean process when memory runs low (slower, no thrashing)
    python3 -I tools/mem_watch.py run --guard --interval 1 -- lake build
    python3 -I tools/mem_watch.py resume      # emergency: un-freeze lean if the sampler was killed

    # measure ONE module in isolation (single thread, imports must already be built)
    python3 -I tools/mem_watch.py module CFSG.Foo.Bar [-- extra lean args]

What is recorded per sample (every --interval seconds, default 2):
  * system: MemAvailable, swap used, PSI memory some/full avg10, swap-in/out and major-fault
    rates, cgroup memory.current/max if present;
  * every `lean` process: pid, module being compiled (from its command line), VmRSS, RssAnon,
    RssFile, VmSwap, VmHWM, thread count and cumulative CPU seconds (user+sys);
  * every other process in the build tree (lake, cc, ld, ...): summed RSS and the largest one.

RssAnon is the number to watch: oleans are mmapped, so RssFile is reclaimable cache, while
anonymous memory (elaboration state) must fit in RAM+swap or the machine thrashes.

Caveat: modules that finish in well under one interval can be missed; that is fine, they are
not the problem.  Lower --interval (e.g. 0.5) if you need them.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import resource
import signal
import subprocess
import sys
import time

PAGE = os.sysconf("SC_PAGE_SIZE")
TICK = os.sysconf("SC_CLK_TCK")
OUT_DIR = os.path.join(".cache", "membench")


# ---------------------------------------------------------------- /proc readers
def read(path: str) -> str | None:
    try:
        with open(path, "rb") as f:
            return f.read().decode("utf-8", "replace")
    except OSError:
        return None


def kv_kb(text: str | None) -> dict[str, int]:
    out: dict[str, int] = {}
    for line in (text or "").splitlines():
        k, _, v = line.partition(":")
        m = re.match(r"\s*(\d+)", v)
        if m:
            out[k] = int(m.group(1))
    return out


def mb(kb: int | None) -> float:
    return round((kb or 0) / 1024, 1)


def sysinfo(prev: dict | None, dt: float) -> dict:
    mi = kv_kb(read("/proc/meminfo"))
    vm = {}
    for line in (read("/proc/vmstat") or "").splitlines():
        k, _, v = line.partition(" ")
        if k in ("pswpin", "pswpout", "pgmajfault"):
            vm[k] = int(v)
    s = {
        "avail_mb": mb(mi.get("MemAvailable")),
        "total_mb": mb(mi.get("MemTotal")),
        "swap_used_mb": mb(mi.get("SwapTotal", 0) - mi.get("SwapFree", 0)),
        "cache_mb": mb(mi.get("Cached")),
    }
    for kind in ("some", "full"):
        s["psi_" + kind] = None
    for line in (read("/proc/pressure/memory") or "").splitlines():
        m = re.match(r"(some|full) avg10=([\d.]+)", line)
        if m:
            s["psi_" + m.group(1)] = float(m.group(2))
    for base in ("/sys/fs/cgroup",):
        cur, mx = read(base + "/memory.current"), read(base + "/memory.max")
        if cur:
            s["cg_cur_mb"] = round(int(cur) / 2**20, 1)
            if mx and mx.strip().isdigit():
                s["cg_max_mb"] = round(int(mx) / 2**20, 1)
    if prev and dt > 0:
        for k in ("pswpin", "pswpout", "pgmajfault"):
            if k in vm and k in prev["vm"]:
                s[k + "_ps"] = round((vm[k] - prev["vm"][k]) / dt, 1)
    s["vm"] = vm
    return s


def proc_table() -> dict[int, tuple[int, str]]:
    """pid -> (ppid, comm) for every process."""
    out = {}
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        st = read(f"/proc/{name}/stat")
        if not st:
            continue
        # comm may contain spaces/parens; split on the last ')'
        r = st.rfind(")")
        comm = st[st.find("(") + 1:r]
        rest = st[r + 2:].split()
        out[int(name)] = (int(rest[1]), comm)
    return out


def descendants(table: dict[int, tuple[int, str]], root: int) -> set[int]:
    kids: dict[int, list[int]] = {}
    for pid, (ppid, _c) in table.items():
        kids.setdefault(ppid, []).append(pid)
    seen, stack = set(), [root]
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        stack.extend(kids.get(p, []))
    return seen


def is_lean(pid: int, comm: str) -> bool:
    if comm == "lean":
        return True
    # interpreter-wrapped lean (tests, shims): look at argv[0..1]
    args = (read(f"/proc/{pid}/cmdline") or "").split("\0")[:2]
    return any(os.path.basename(x) == "lean" for x in args)


def module_from_cmdline(pid: int) -> str:
    raw = read(f"/proc/{pid}/cmdline") or ""
    args = [a for a in raw.split("\0") if a]
    root = "."
    for i, a in enumerate(args):
        if a in ("-R", "--root") and i + 1 < len(args):
            root = args[i + 1]
        elif a.startswith("--root="):
            root = a[7:]
    for a in args[1:]:
        if a.endswith(".lean"):
            rel = os.path.relpath(a, root) if os.path.isabs(a) or root != "." else a
            if rel.startswith(".."):
                rel = a
            return rel[:-5].replace(os.sep, ".").lstrip(".")
    return "?"


def proc_sample(pid: int) -> dict | None:
    st = kv_kb(read(f"/proc/{pid}/status"))
    if "VmRSS" not in st:
        return None  # kernel thread or exited
    cpu = None
    stat = read(f"/proc/{pid}/stat")
    if stat:
        f = stat[stat.rfind(")") + 2:].split()
        cpu = round((int(f[11]) + int(f[12])) / TICK, 2)  # utime+stime, cumulative seconds
    return {
        "cpu": cpu,
        "rss": mb(st.get("VmRSS")), "anon": mb(st.get("RssAnon")),
        "file": mb(st.get("RssFile")), "swap": mb(st.get("VmSwap")),
        "hwm": mb(st.get("VmHWM")), "thr": st.get("Threads", 0),
    }


# ---------------------------------------------------------------- memory guard
class Guard:
    """Pause (SIGSTOP) the biggest running lean process under memory pressure; resume it later.

    A stopped process keeps its memory, but it stops touching it, so the kernel can swap its
    cold pages out while the remaining processes make progress on a working set that fits in
    RAM.  Trades wall time for not thrashing.  It cannot help if ONE module needs more than
    RAM+swap: only the last runnable lean process is never paused (that would deadlock).
    """

    def __init__(self, pause_gb: float, resume_gb: float, psi: float, min_running: int,
                 hold: float, cooldown: float):
        assert resume_gb > pause_gb, "--resume-above-gb must exceed --pause-below-gb"
        self.pause_mb, self.resume_mb = pause_gb * 1024, resume_gb * 1024
        self.psi, self.min_running = psi, min_running
        self.hold, self.cooldown = hold, cooldown
        self.paused: dict[int, dict] = {}
        self.last = -1e9

    def _signal(self, pid: int, sig) -> bool:
        try:
            os.kill(pid, sig)
            return True
        except ProcessLookupError:
            return False

    def step(self, now: float, sysd: dict, lean: list[dict]) -> list[dict]:
        ev = []
        live = {p["pid"]: p for p in lean}
        for pid in [k for k in self.paused if k not in live]:
            ev.append({"ev": "gone", "pid": pid, "mod": self.paused.pop(pid)["mod"]})
        running = [p for p in lean if p["pid"] not in self.paused]
        avail = sysd["avail_mb"]
        pressure = avail < self.pause_mb or (self.psi > 0 and (sysd.get("psi_full") or 0) >= self.psi)
        ready = now - self.last >= self.cooldown
        if pressure and len(running) > self.min_running and ready:
            v = max(running, key=lambda p: p["anon"])
            if self._signal(v["pid"], signal.SIGSTOP):
                self.paused[v["pid"]] = {"t": now, "mod": v["mod"]}
                self.last = now
                ev.append({"ev": "pause", "pid": v["pid"], "mod": v["mod"], "anon": v["anon"],
                           "avail": avail})
        elif self.paused and ready:
            pid = min(self.paused, key=lambda k: self.paused[k]["t"])
            info = self.paused[pid]
            forced = not running  # nothing else can make progress: must continue
            # a resumed process pages its swapped part back in: leave room for that
            room = avail - live[pid]["swap"] > self.resume_mb
            if forced or (not pressure and now - info["t"] >= self.hold and room):
                if self._signal(pid, signal.SIGCONT):
                    self.last = now
                ev.append({"ev": "resume", "pid": pid, "mod": info["mod"],
                           "held_s": round(now - info["t"], 1), "forced": forced,
                           "avail": avail})
                del self.paused[pid]
        return ev

    def resume_all(self) -> None:
        for pid in list(self.paused):
            self._signal(pid, signal.SIGCONT)
        self.paused.clear()


GUARD: Guard | None = None


# ---------------------------------------------------------------- sampling loop
def sample_loop(out, interval: float, root_pid: int | None, stop, live: bool,
                warn_avail_gb: float) -> None:
    try:
        _sample_loop(out, interval, root_pid, stop, live, warn_avail_gb)
    finally:
        if GUARD:
            GUARD.resume_all()  # never leave a build frozen


def _sample_loop(out, interval: float, root_pid: int | None, stop, live: bool,
                 warn_avail_gb: float) -> None:
    prev, t_prev = None, time.time()
    t0 = t_prev
    last_live = 0.0
    names: dict[int, str] = {}  # pid -> module, cached (cmdline is stable)
    while not stop():
        now = time.time()
        sysd = sysinfo(prev, now - t_prev)
        prev, t_prev = {"vm": sysd["vm"]}, now
        table = proc_table()
        scope = descendants(table, root_pid) if root_pid else set(table)
        lean, other_rss, other_top = [], 0.0, ("", 0.0)
        for pid in scope:
            comm = table.get(pid, (0, ""))[1]
            if root_pid and pid == os.getpid():
                continue
            s = proc_sample(pid)
            if s is None:
                continue
            if pid in names or is_lean(pid, comm):
                if pid not in names:
                    names[pid] = module_from_cmdline(pid)
                s.update(pid=pid, mod=names[pid])
                lean.append(s)
            elif root_pid:
                other_rss += s["rss"]
                if s["rss"] > other_top[1]:
                    other_top = (comm, s["rss"])
        del sysd["vm"]
        rec = {"t": round(now - t0, 2), "sys": sysd, "lean": lean,
               "other_rss": round(other_rss, 1), "other_top": other_top[0]}
        if GUARD:
            events = GUARD.step(now, sysd, lean)
            if events:
                rec["guard"] = events
                for e in events:
                    print(f"[mem GUARD] {e['ev']} {e['mod']} (pid {e['pid']}) "
                          f"avail={e.get('avail', sysd['avail_mb']) / 1024:.1f}G"
                          + (f" held {e['held_s']}s{' (forced)' if e['forced'] else ''}"
                             if e["ev"] == "resume" else ""), file=sys.stderr)
            rec["paused"] = sorted(GUARD.paused)
        out.write(json.dumps(rec, separators=(",", ":")) + "\n")
        out.flush()
        if live and now - last_live >= 10:
            last_live = now
            tot = sum(p["anon"] for p in lean)
            big = max(lean, key=lambda p: p["anon"], default=None)
            print(f"[mem {rec['t']:7.0f}s] lean={len(lean)} anon={tot / 1024:.1f}G "
                  f"avail={sysd['avail_mb'] / 1024:.1f}G swap={sysd['swap_used_mb'] / 1024:.1f}G "
                  f"psi_full={sysd['psi_full']} "
                  + (f"biggest={big['mod']} {big['anon'] / 1024:.1f}G" if big else ""),
                  file=sys.stderr)
        if sysd["avail_mb"] / 1024 < warn_avail_gb:
            big = max(lean, key=lambda p: p["anon"], default=None)
            print(f"[mem WARN] MemAvailable {sysd['avail_mb'] / 1024:.1f}G < {warn_avail_gb}G; "
                  f"largest lean: {big['mod'] + ' ' + str(big['anon']) + 'MB' if big else '-'}",
                  file=sys.stderr)
        time.sleep(max(0.0, interval - (time.time() - now)))


def open_out(label: str, outdir: str):
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, f"{label}-{time.strftime('%Y%m%d-%H%M%S')}.jsonl")
    return open(path, "w"), path


def cmd_run(a) -> int:
    if not a.cmd:
        sys.exit("give a command after --")
    out, path = open_out(a.label, a.outdir)
    print(f"[mem] sampling to {path}", file=sys.stderr)
    child = subprocess.Popen(a.cmd, start_new_session=True)

    def fwd(sig, _f):
        if GUARD:
            GUARD.resume_all()  # a stopped process would not see SIGINT/SIGTERM
        try:
            os.killpg(child.pid, sig)
        except ProcessLookupError:
            pass
    for s in (signal.SIGINT, signal.SIGTERM):
        signal.signal(s, fwd)
    sample_loop(out, a.interval, child.pid, lambda: child.poll() is not None, True,
                a.warn_avail_gb)
    out.close()
    print(f"[mem] exit {child.returncode}; report: python3 -I tools/mem_report.py {path}",
          file=sys.stderr)
    return child.returncode


def cmd_attach(a) -> int:
    out, path = open_out(a.label, a.outdir)
    print(f"[mem] attached; sampling to {path} (Ctrl-C to stop)", file=sys.stderr)
    done = []
    signal.signal(signal.SIGINT, lambda *_: done.append(1))
    signal.signal(signal.SIGTERM, lambda *_: done.append(1))
    if GUARD is None:
        print("[mem] note: attach without --guard only observes", file=sys.stderr)
    sample_loop(out, a.interval, None, lambda: bool(done), True, a.warn_avail_gb)
    out.close()
    print(f"[mem] report: python3 -I tools/mem_report.py {path}", file=sys.stderr)
    return 0


def cmd_module(a) -> int:
    """Elaborate one module with `lean` directly (no .olean written), single-threaded."""
    rel = a.module.replace(".", os.sep) + ".lean"
    if not os.path.exists(rel):
        sys.exit(f"{rel} not found (run from the repository root)")
    cmd = ["lake", "env", "lean", "-R", ".", f"--threads={a.threads}", *a.cmd, rel]
    out, path = open_out("module-" + a.module, a.outdir)
    print(f"[mem] {' '.join(cmd)}\n[mem] sampling to {path}", file=sys.stderr)
    t0 = time.time()
    child = subprocess.Popen(cmd, start_new_session=True)
    sample_loop(out, a.interval, child.pid, lambda: child.poll() is not None, False,
                a.warn_avail_gb)
    out.close()
    peaks = {}
    for line in open(path):
        r = json.loads(line)
        for p in r["lean"]:
            peaks[p["pid"]] = max(peaks.get(p["pid"], (0, 0)), (p["anon"], p["hwm"]))
    anon, hwm = max(peaks.values(), default=(0, 0))
    wall = time.time() - t0
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)  # exact: our only child tree
    print(f"{a.module}: exit {child.returncode}, {wall:.1f}s wall, "
          f"{ru.ru_utime + ru.ru_stime:.1f}s CPU (user {ru.ru_utime:.1f} + sys {ru.ru_stime:.1f}), "
          f"peak anon {anon:.0f} MB (sampled), max RSS {ru.ru_maxrss / 1024:.0f} MB (exact), "
          f"threads={a.threads}")
    return child.returncode


def cmd_resume(a) -> int:
    """Emergency: SIGCONT every stopped lean process (e.g. the sampler was SIGKILLed)."""
    n = 0
    for pid, (_pp, comm) in proc_table().items():
        st = read(f"/proc/{pid}/stat") or ""
        state = st[st.rfind(")") + 2:].split()[:1]
        if state == ["T"] and is_lean(pid, comm):
            os.kill(pid, signal.SIGCONT)
            n += 1
            print(f"continued pid {pid}: {module_from_cmdline(pid)}")
    print(f"{n} process(es) continued")
    return 0


def main() -> int:
    global GUARD
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("--interval", type=float, default=2.0, help="seconds between samples")
    common.add_argument("--outdir", default=OUT_DIR)
    common.add_argument("--warn-avail-gb", type=float, default=2.0,
                        help="print a warning when MemAvailable drops below this")
    gd = argparse.ArgumentParser(add_help=False)
    gd.add_argument("--guard", action="store_true",
                    help="pause the biggest lean process under memory pressure (see Guard)")
    gd.add_argument("--pause-below-gb", type=float, default=4.0,
                    help="pause when MemAvailable falls below this (default 4)")
    gd.add_argument("--resume-above-gb", type=float, default=8.0,
                    help="resume when MemAvailable (minus the process's swapped part) is above "
                    "this (default 8)")
    gd.add_argument("--pause-psi", type=float, default=0.0,
                    help="also pause when PSI memory 'full' avg10 %% reaches this (0 = off)")
    gd.add_argument("--min-running", type=int, default=1,
                    help="never pause below this many running lean processes (default 1)")
    gd.add_argument("--hold", type=float, default=20.0,
                    help="minimum seconds a process stays paused (default 20)")
    gd.add_argument("--cooldown", type=float, default=5.0,
                    help="minimum seconds between pause/resume actions (default 5)")
    sub = ap.add_subparsers(dest="mode", required=True)
    sub.add_parser("resume").set_defaults(fn=cmd_resume)
    for name, fn in (("run", cmd_run), ("attach", cmd_attach), ("module", cmd_module)):
        p = sub.add_parser(name, parents=[common] + ([gd] if name != "module" else []))
        p.set_defaults(fn=fn)
        if name != "module":
            p.add_argument("--label", default="build")
        if name == "module":
            p.add_argument("module")
            p.add_argument("--threads", type=int, default=1)
        if name != "attach":
            p.add_argument("cmd", nargs=argparse.REMAINDER)
    a = ap.parse_args()
    if getattr(a, "cmd", None) and a.cmd[:1] == ["--"]:
        a.cmd = a.cmd[1:]
    if getattr(a, "guard", False):
        GUARD = Guard(a.pause_below_gb, a.resume_above_gb, a.pause_psi, a.min_running,
                      a.hold, a.cooldown)
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())

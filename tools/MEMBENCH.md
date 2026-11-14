# Memory benchmarking for `lake build`

Goal: find which modules (alone, or together with whatever Lake builds in parallel) push a
64 GB machine / 48 GB WSL VM into swap, so they can be split or slimmed later.
Tools are stdlib-only Python, Linux/WSL only.  Run from the repository root.

## 1. Record a build

    python3 -I tools/mem_watch.py run --label full -- lake build
    # or, in another terminal, attach to a build that is already running:
    python3 -I tools/mem_watch.py attach --label full

Samples go to `.cache/membench/<label>-<time>.jsonl` (about 2 s apart; `--interval 0.5`
catches shorter modules).  A status line prints every 10 s and a warning whenever
`MemAvailable` drops under `--warn-avail-gb` (default 2) with the biggest lean process.
Killing the sampler or the build leaves a usable file.

## 2. Read the report

    python3 -I tools/mem_report.py .cache/membench/full-*.jsonl --top 40 --csv mem.csv

* top modules by peak **anonymous** memory (`RssAnon`; oleans are mmapped and show up as
  reclaimable `RssFile`), with lines/bytes and olean size for comparison;
* top modules by CPU time, plus `cpu/wall` (CPU seconds per observed wall second): well below
  the thread count while MemAvailable is low means the module was stalled on swap, not
  computing.  CPU figures from a full build are a lower bound (last sample before exit);
  `module` mode reports exact wall time, CPU time and max RSS from `getrusage`;
* pressure episodes (low MemAvailable, high PSI `full`, heavy swap-in) and the lean
  processes live at the time -- thrashing is usually several big modules at once;
* total lean memory vs. number of concurrent lean processes, and a worst-case estimate for
  `-j`/`--threads` choices against your RAM budget (`--ram-gb 48`).

## 3. Measure one module in isolation

    python3 -I tools/mem_watch.py module CFSG.Some.Module --threads 1 [-- -Dprofiler=true]

Runs `lake env lean -R . --threads=N file.lean` (nothing is written to `.lake`), so its
imports must already be built.  Compare peak with the full-build figure: if isolated is
much smaller, the cost is concurrency; if similar, the module itself is the problem.

## 4. Memory guard (trade time for not thrashing)

    python3 -I tools/mem_watch.py run --guard --interval 1 -- lake build
    # tune: --pause-below-gb 4 --resume-above-gb 8 --pause-psi 20 --hold 20 --cooldown 5

Under pressure (MemAvailable below `--pause-below-gb`, or PSI `full` above `--pause-psi`) it
SIGSTOPs the biggest running `lean` process.  A stopped process keeps its memory but stops
touching it, so the kernel swaps its cold pages out and the others run on a working set that
fits in RAM.  It resumes the longest-paused process once MemAvailable (less that process's
swapped part) is above `--resume-above-gb` and it has been held `--hold` seconds.

Limits, so you know what to expect:
* It cannot help if a single module needs more than RAM+swap.  The last running `lean` is
  never paused (deadlock), and when nothing else is running the paused one is resumed
  (logged as a "forced resume" in the report -- that module is your real problem).
* It needs swap to do any good (WSL: set `swap=` in `.wslconfig`).
* Only `lean` processes are paused, not `cc`/`ld` steps of precompiled modules.
* Every exit path (normal, Ctrl-C, SIGTERM, errors) continues paused processes.  If the sampler
  is SIGKILLed, a paused `lean` stays frozen and the build looks hung:
  run `python3 -I tools/mem_watch.py resume`.
* Thresholds are in absolute GB; defaults suit a ~48 GB VM.  Check the report's "guard" section
  and episode list to see whether it kicked in and whether pressure persisted.

## Suggested workflow

1. Baseline: `lake build` with `LEAN_NUM_THREADS`/`weakLeanArgs` as you run it today.
2. Report; take the top modules and the episodes' module lists.
3. Re-run each top module with `module` to separate "big alone" from "big together".
4. Re-record with less parallelism and see how far peak memory falls; then split the
   offenders.  Knobs this repo already uses: `LEAN_NUM_THREADS=N` in the environment and
   `weakLeanArgs = ["--threads=3"]` in `lakefile.toml`.  Check `lake build --help` for a job
   limit (this repo uses a patched Lake, so I have not verified one exists).

## WSL notes

* `%UserProfile%\.wslconfig`: `[wsl2] memory=48GB`, `swap=64GB` (or more), then
  `wsl --shutdown`.  Swap on the Windows SSD turns overshoot into slowness rather than an
  OOM kill; PSI `full` > 5% in the report is the sign you are in that regime.
* `[experimental] autoMemoryReclaim=gradual` returns page cache to Windows.
* Keep the checkout on the WSL ext4 filesystem (not `/mnt/c`): oleans are mmapped.
* `/proc/pressure/memory` needs a WSL2 kernel with PSI; if absent, those fields are null and
  the swap/MemAvailable signals still work.

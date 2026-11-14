# Two-agent memory workflow: detector -> fixer

**Priorities, in order**
1. `lake build` must complete on a 64 GB desktop (48 GB WSL) without thrashing, so others can
   contribute.  Wall time is an acceptable price.
2. Then minimise the repository: fewer lines/bytes in the closure of the final theorem, and
   genuinely better mathematics (shorter or more conceptual arguments, removed detours), not
   repackaging.  See `.github/PULL_REQUEST_TEMPLATE.md`.

These conflict only when a memory fix costs score (e.g. splitting a module adds headers).
Rule: priority 1 wins for a **blocker**, but the score cost must be minimal and recorded;
for a **non-blocker** a fix is accepted only if it is score-neutral or reduces the score.

Both agents run on the machine that does the builds (WSL), one build at a time: two
concurrent builds on 48 GB recreate the thrashing.  `tools/check_change.sh` serialises with
`flock` on a hard-coded path (`/home/alastair/claude-compute/cfsg-build.lock`): change `LOCK`
to a path valid on your machine and take the same lock around every measurement run.

## Agent A: detector

    tools/mem_detect.sh [--no-build] [--top K] [--ram-gb 48]

Full build under `mem_watch.py --guard`, `mem_report.py`, then `mem_watch.py module` on the
top flagged modules, writing `.cache/membench/findings.json` and `report.txt`.  A is done
when findings.json exists; it makes no edits to Lean files.  (Use `--no-build` to re-analyse
an existing log; partial logs from an interrupted build are fine.)

### findings.json (version 1)

    summary:  hours, min_avail_gb, peak_swap_gb, max_psi_full, peak_lean_anon_gb,
              pressure_episodes, guard_pauses, modules_seen, modules_flagged
    modules[] (flagged first, then by peak): module, flagged, reasons[], peak_anon_mb,
              peak_rss_mb, isolated_peak_anon_mb (null if not measured), alone_vs_together
              ("big_alone" | "problem_is_concurrency" | null), cpu_s, seen_s, cpu_per_wall,
              lines, bytes, olean_mb, pressure_episodes_top3, guard_paused_s,
              co_running_at_peak[{module, anon_mb}]
    episodes[]: start_s, end_s, min_avail_gb, peak_lean_anon_gb, modules[{module, anon_mb}]

`reasons` are `peak_anon>=<flag>GB`, `top3_in_pressure_episode`, `forced_resume` (the guard
had to resume it because nothing else was runnable: that module alone is too big).
Memory figures are anonymous memory (RssAnon), in MB.

### Classifying a finding
* **blocker**: `forced_resume`, or `alone_vs_together == "big_alone"` with peak above the
  flag threshold.  Fix the module itself.
* **concurrency**: `alone_vs_together == "problem_is_concurrency"`.  The module is fine
  alone; reduce parallelism (`LEAN_NUM_THREADS`, `weakLeanArgs` in `lakefile.toml`) or fix
  the biggest co-runners.  Not a reason to touch this module.
* **unknown** (`isolated_peak_anon_mb` null): measure it alone first.

## Agent B: fixer

Input: one flagged module from findings.json.  Work on a branch, one module per attempt.

1. Baseline: `python3 -I tools/mem_watch.py module <Mod> --threads 1`, three times; keep the
   median peak and CPU time.  (Imports must be built.)
2. Diagnose before editing.  Separate import cost from elaboration cost: compile the header
   alone (the `import` lines plus `module`) and compare.  If the header dominates, splitting
   cannot help; trim imports (`tools/check_import_removal.py`) or split what it imports.  Use
   `-Dprofiler=true` (pass after `--`) to find heavy declarations.
3. Try fixes in this order (cheapest in score first):
   a. delete dead or duplicated code (`tools/dup_decls.py`, `tools/text_reach.py`,
      `tools/delete_dead.py`): shrinks the repo as well;
   b. replace the expensive step: `decide`/`simp`/`omega`/`norm_num` blow-ups, huge `by
      decide` computations, large literals, unneeded instances, `unfold`-heavy proofs,
      `maxRecDepth`/`maxHeartbeats` increases that hide a blow-up;
   c. a mathematically better route (shorter, or avoiding a big case analysis): the real
      priority-2 win, record the argument in the PR notes;
   d. move a heavy lemma group into its own module (a split) or break an import chain.
      Last resort: it adds lines.  Prefer splits that make the heavy part's importers lighter.
4. Verify every attempt with `tools/check_change.sh` (builds changed modules, classifies the
   interface change, builds `Comparator.Solution` downstream, runs `verify_final.sh`, prints
   the score diff).
5. Measure again as in step 1 (median of three).  Record the attempt, accepted or not, as a
   line in `.cache/membench/attempts.jsonl`: module, idea, before/after peak anon, before/after
   CPU, score delta (bytes, lines), check_change result.

### Acceptance (edit these numbers if you disagree)
* `check_change.sh` passes; axioms stay within `propext`, `Quot.sound`, `Classical.choice`; the
  statement check passes.  No `sorry`, `native_decide`, new axioms, or `set_option` that
  weakens checking.  Never skip or weaken a check to get green.
* **Blocker**: peak anonymous memory falls at least 25% or below the flag threshold, with
  the smallest score increase that achieves it.  Wall time may grow (up to ~2x CPU time).
* **Non-blocker**: accepted only if memory does not rise and the score does not rise.
* **Interface**: the default is public-interface-unchanged.  `--allow-interface` only for a
  split, in which case the full rebuild in a second checkout is required (PR template).
* A result that is within run-to-run noise (compare the three runs' spread) is not an
  improvement.

Output per accepted attempt: a PR following the template, with the memory before/after and
score diff.  Rejected attempts stay in attempts.jsonl so they are not retried.

## Handing the loop back to Agent A
After a batch of accepted changes, re-run `tools/mem_detect.sh` (full build): fixes can move
the peak to another module, and concurrency effects change.  Stop when a full build with the
guard shows no pressure episodes and no forced resumes.

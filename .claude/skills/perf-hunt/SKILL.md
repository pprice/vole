---
name: perf-hunt
description: Automated performance optimization loop. Generates large benchmark workloads with vole-stress, profiles with perf, identifies hotspots in our code, fixes them, verifies improvement, repeats.
---

# Perf Hunt

Automated performance optimization skill that generates large benchmark suites
with `vole-stress`, profiles them with `perf record`/`perf report` via
`vole test`, identifies hotspots in our crates, fixes them, and verifies
improvement — in an iterative loop.

## Invocation

Launch via ralph-loop with a completion promise:

```
/ralph-loop "/perf-hunt 10" --completion-promise PERF_HUNT_DONE
```

Or invoke directly (single iteration):

```
/perf-hunt 10    # max 10 iterations
/perf-hunt 5     # max 5 iterations
```

Parse `$ARGUMENTS`:
- First token: K (max iterations) — default 10

## How It Works

Each iteration targets ONE hotspot: profile the suite, pick the top un-investigated
function, fix it, verify the improvement. When no actionable hotspots remain or
K iterations are exhausted, stop.

All builds use the `release-local` cargo profile (optimized with debug symbols)
since we are measuring performance, not debugging correctness.

## State File: `.claude/perf-hunt-state.json`

```json
{
  "max_iterations": 10,
  "iteration": 1,
  "benchmark_suite": {
    "base_dir": "/tmp/vole-perf",
    "workloads": [
      { "name": "perf-full-1000", "seed": 1000, "profile": "full",
        "dir": "/tmp/vole-perf/perf-full-1000", "layers": 12, "modules_per_layer": 15 },
      { "name": "perf-many-modules-2000", "seed": 2000, "profile": "many-modules",
        "dir": "/tmp/vole-perf/perf-many-modules-2000", "layers": 12, "modules_per_layer": 25 },
      { "name": "perf-wide-types-3000", "seed": 3000, "profile": "wide-types",
        "dir": "/tmp/vole-perf/perf-wide-types-3000", "layers": 10, "modules_per_layer": 12 },
      { "name": "perf-generics-heavy-4000", "seed": 4000, "profile": "generics-heavy",
        "dir": "/tmp/vole-perf/perf-generics-heavy-4000", "layers": 10, "modules_per_layer": 12 },
      { "name": "perf-stdlib-heavy-5000", "seed": 5000, "profile": "stdlib-heavy",
        "dir": "/tmp/vole-perf/perf-stdlib-heavy-5000", "layers": 10, "modules_per_layer": 15 }
    ]
  },
  "baseline": {
    "timestamp": "...",
    "commit": "...",
    "timings": { "<workload>": 0.0 }
  },
  "candidates": [
    {
      "function": "vole_sema::example::hot_function",
      "max_self_pct": 8.31,
      "crate": "vole_sema",
      "by_workload": { "perf-many-modules-2000": 8.31, "perf-full-1000": 3.18 }
    }
  ],
  "investigated": [
    {
      "function": "...",
      "iteration": 1,
      "outcome": "fixed|reverted|deferred|marginal",
      "commit": null,
      "ticket_id": null,
      "samples_pct_before": 0.0,
      "samples_pct_after": null,
      "compile_time_change_pct": null,
      "notes": "..."
    }
  ],
  "current_hotspot": null,
  "suite_generation": 1,
  "history": []
}
```

Key fields:
- **`candidates`**: All actionable hotspots (>2% Self in any workload) from the
  last profiling round, ranked by `max_self_pct`. Rebuilt from fresh profile data
  every iteration. Persists across sessions so investigated functions are tracked.
- The profiling round (~2.5 min) always runs to ensure fresh baseline timings
  and accurate hotspot data after each fix.

## Journal: `.claude/perf-hunt-journal.md`

Persistent across sessions. Sections:
- **Findings**: general performance observations
- **Optimizations Applied**: what worked and why
- **Deferred**: hotspots that touch >15 files (ticket filed)
- **Patterns**: recurring optimization patterns in the codebase
- **Noise Functions**: functions that always show up but aren't actionable (always skip)

<IMPORTANT>
- **Read the journal** at the start of every perf-hunt session (step 1)
- **Append to the journal** whenever you discover something useful — optimization
  patterns, noise functions to skip, measurement quirks, crate-specific notes.
  Keep entries terse (one line each).
</IMPORTANT>

## Workflow Per Iteration

Read `.claude/perf-hunt-state.json`. Based on state, perform the **first
applicable step** from the list below, then update state and finish.

### Step 1 — Initialize (no state file)

- **Read `.claude/perf-hunt-journal.md`** to load lessons from previous runs
- **Preflight check**: run `just check` to verify the repo compiles
- Build release-local: `cargo build --profile release-local`
- Generate 5 large benchmark workloads using `gen-suite.py`:

```bash
python3 .claude/skills/perf-hunt/gen-suite.py /tmp/vole-perf \
  perf-full-1000:1000:full:12:15 \
  perf-many-modules-2000:2000:many-modules:12:25 \
  perf-wide-types-3000:3000:wide-types:10:12 \
  perf-generics-heavy-4000:4000:generics-heavy:10:12 \
  perf-stdlib-heavy-5000:5000:stdlib-heavy:10:15
```

  The goal is that each workload takes **at least several seconds** under
  `vole test` so `perf` collects enough samples (thousands) for statistically
  meaningful hotspot data. If workloads are too fast, increase layers/modules.

- Run `profile-round.py` to capture baseline timings + perf hotspots:

```bash
python3 .claude/skills/perf-hunt/profile-round.py /tmp/vole-perf \
  perf-full-1000 perf-many-modules-2000 perf-wide-types-3000 \
  perf-generics-heavy-4000 perf-stdlib-heavy-5000
```

- Parse the JSON output (see profile-round.py output format below)
- Build the **candidate list** from profile results (see Step 3 for filtering rules)
- Write initial state with baseline timings, candidates, and `fixes_since_last_profile: 0`

### Step 2 — Profile (state exists, no current_hotspot)

Always re-profile to get fresh baseline timings and accurate hotspot data:

- Rebuild release-local: `cargo build --profile release-local`
- Regenerate workloads if directories don't exist (e.g. after reboot/cleanup)
- Run `profile-round.py` on the benchmark suite
- Compare timings against previous baseline:
  - If total wall-clock time regressed >2% from a previous fix: revert and investigate
  - Otherwise: update baseline timings
- Rebuild candidate list from fresh profile data (Step 3 filtering rules)
- Proceed to Step 3

### Step 3 — Analyze (pick from candidate list)

Filter the `candidates` list:

**Include only our crate prefixes:**
- `vole_sema::`
- `vole_codegen::`
- `vole_runtime::`
- `vole_frontend::`
- `vole_identity::`

**Skip external functions:**
- `cranelift_*`, `regalloc2`
- `hashbrown`, `alloc::`, `core::`, `std::`
- libc: `malloc`, `cfree`, `free`, `mmap`, `__GI_*`
- Anything not matching our crate prefixes

**Skip already-investigated functions:**
- Check the `investigated` list in state; skip any function already there

**Threshold:** >2% Self in any workload = actionable

When building the candidate list from profile-round.py output, aggregate each
symbol's `self_pct` across all workloads. Store the per-workload breakdown in
`by_workload` and rank by `max_self_pct` (highest Self% in any single workload).

**Decision:**
- If no un-investigated candidate above threshold and `suite_generation == 1`:
  Evolve suite — regenerate workloads with larger `--layers`/`--modules-per-layer`,
  increment `suite_generation`, re-profile
- If no un-investigated candidate above threshold and `suite_generation > 1`:
  Output `<promise>PERF_HUNT_DONE</promise>` — no more actionable hotspots
- Otherwise: set `current_hotspot` to the top-ranked un-investigated candidate,
  proceed to Step 4

### Step 4 — Investigate + Fix (current_hotspot set)

<IMPORTANT>
15-minute time limit per hotspot. The ticket is your running log — if you hit
the limit, those notes are what makes the ticket useful for future investigation.
</IMPORTANT>

#### 4a. Create a ticket

Before investigating, create a `tk` ticket to track the work:

```bash
tk create "perf-hunt: <function_name> at X.X% samples" \
  -d "Hotspot: <full::path::to::function>
Samples: X.X% across workloads
Crate: <crate_name>
Iteration: N"
```

Record the ticket ID in the `investigated` entry and in `current_hotspot`.

#### 4b. Dispatch a sub-agent for investigation and fix

Dispatch a **sequential sub-agent** (using the Task tool) to investigate and
attempt the optimization. This keeps the investigation focused and protects
the main context window.

**The sub-agent's prompt must include:**
- The hot function's full path (e.g. `vole_sema::check::TypeChecker::resolve_type`)
- The sample percentage and which workloads it appears in
- The ticket ID for tracking notes
- The crate to investigate (e.g. `src/crates/vole-sema/`)
- Any relevant context from the perf report (callers, callees, call chain)
- Paths to perf.data files for `perf annotate` (if available from last profile)

**The sub-agent MUST follow this investigation process:**

1. **Reproduce and understand the hotspot**
   - Use `perf annotate` to see instruction-level hotness (if perf.data exists):
     ```bash
     perf annotate -i /tmp/vole-perf-data-<workload>.data --symbol=<symbol> --stdio
     ```
   - Read the hot function's source code
   - Identify callers with `rg "<function_name>" src/crates/<crate>/`
   - Identify callees — what does this function call in its hot path?
   - Inspect compiler IR at various levels to understand what's being generated:
     - `vole inspect ast <file>` — parsed AST (useful for frontend hotspots)
     - `vole inspect mir <file>` — mid-level IR after sema (useful for sema/runtime hotspots)
     - `vole inspect ir <file>` — Cranelift IR (useful for codegen hotspots)
     Use `--all` with `mir` to include prelude functions. These help you see
     whether the compiler is doing unnecessary work or generating bloated output.
   - Track findings: `tk add-note <id> "Callers: ..., Callees: ..., Hot path: ..."`

2. **Identify the optimization opportunity**

   Look for these patterns (in priority order):

   | Pattern | What to look for | Typical fix |
   |---------|-----------------|-------------|
   | **Redundant work** | Same lookup/computation repeated in a loop | Cache result before loop |
   | **Unnecessary clones** | `.clone()` on `String`, `Vec`, `Rc`, `HashMap` in hot path | Borrow instead, or `Rc::clone` only when needed |
   | **Hot allocations** | `Vec::new()`, `String::new()`, `format!()` inside inner loops | Pre-allocate outside loop, reuse buffers |
   | **O(n^2) patterns** | Nested iteration, `.contains()` on Vec in a loop | Use HashSet, index map, or sort+binary search |
   | **Excessive Rc traffic** | Many `Rc::clone`/drop in tight loop | Borrow the inner value, batch operations |
   | **Missing caching** | Pure function called repeatedly with same args | Memoize or compute once |
   | **Bad data structures** | Vec used for frequent lookups, linear scans | HashMap, BTreeMap, or indexed storage |
   | **Unnecessary format!/to_string** | String formatting in hot path that isn't needed | Use Display impl lazily, avoid intermediate strings |
   | **Excessive hashing** | HashMap with complex keys hashed repeatedly | Use NameId/interned keys, or cache hash |
   | **Branch misprediction** | Hot if/match with unpredictable pattern | Reorder arms by frequency, use likely/unlikely hints |

   Track what you find: `tk add-note <id> "Pattern: <what>, Location: <file:line>"`

3. **Assess scope**
   - If the fix would touch **>15 files**: this is an architectural issue
     ```bash
     tk add-note <id> "Deferred: fix requires changes across >15 files"
     ```
     Add to journal under Deferred, mark `deferred` in investigated, return
   - If the fix is localized (<15 files): proceed to implement

4. **Implement the optimization**
   - Make the change, keeping it minimal and focused
   - Add a comment explaining *why* the optimization matters if it's not obvious
     (e.g. `// Pre-allocate: this loop typically processes 50-200 items`)
   - Do NOT add unnecessary abstractions — a direct fix is better than a
     clever refactor
   - Track what you changed: `tk add-note <id> "Fix: <what was changed and why>"`

5. **Verify correctness**
   - Run `just pre-commit` — the optimization MUST NOT break anything
   - If pre-commit fails: fix the issue or revert and try a different approach
   - Track: `tk add-note <id> "pre-commit: pass"` or `tk add-note <id> "pre-commit: FAIL, reverting"`

6. **Commit**
   - Commit with: `perf: <what was optimized and why>`
   - Track: `tk add-note <id> "Committed: <hash>"`
   - Close the ticket: `tk close <id>`

7. **15-minute time limit**
   - If unable to fix within ~15 minutes, stop
   - Add a final note explaining what was tried, what the blocker is, and
     leads for future investigation:
     ```bash
     tk add-note <id> "Stopping after 15min. Tried: <approaches>. Blocker: <issue>. Leads: <suggestions>"
     ```
   - Leave the ticket open
   - Mark `deferred` in investigated, return

**After the sub-agent completes:**
- If fixed: record `fix_commit` hash in investigated entry, mark outcome `fixed`
- If marginal improvement but code is cleaner: mark `marginal`
- If deferred (>15 files or 15-min limit): mark `deferred`, ticket stays open
- Clear `current_hotspot`
- Update journal with any learnings (patterns found, noise functions, etc.)

### Step 5 — Check Termination

- If `iteration >= max_iterations`: output `<promise>PERF_HUNT_DONE</promise>`
- If no un-investigated candidates above threshold and `suite_generation > 1`:
  done, output `<promise>PERF_HUNT_DONE</promise>`
- Otherwise: increment `iteration`, go to Step 2

## Suite Generation Script

`gen-suite.py` generates benchmark workloads. Always use it instead of running
`vole-stress` manually.

**Usage:**

```bash
python3 .claude/skills/perf-hunt/gen-suite.py <output-dir> <spec> [spec ...]
```

Each spec is a colon-separated tuple: `name:seed:profile:layers:modules_per_layer`.

**Output** (stdout): JSON array of generated workloads:

```json
[
  { "name": "perf-full-1000", "dir": "/tmp/vole-perf/perf-full-1000" }
]
```

The script builds vole-stress once, then generates all workloads sequentially.
Progress goes to stderr.

## Profile Round Script

`profile-round.py` profiles workloads with `vole test`. For each workload it
runs a single `vole test` invocation under `perf record`, timed for wall-clock
comparison. Only one `vole test` run per workload (perf overhead is negligible).

`vole test` exercises all test blocks across all modules, producing plenty of
CPU samples for meaningful profiling. Always use this script instead of running
`perf` commands individually.

**Usage:**

```bash
python3 .claude/skills/perf-hunt/profile-round.py <base-dir> <workload1> [workload2 ...]
```

Where each workload name is a directory name under `<base-dir>`.

**Output** (stdout): JSON array, one entry per workload:

```json
[
  {
    "workload": "perf-full-1000",
    "time_s": 54.056,
    "perf_data": "/tmp/vole-perf-data-perf-full-1000.data",
    "hotspots": [
      { "symbol": "vole_sema::analyzer::Analyzer::analyze", "children_pct": 14.2, "self_pct": 0.05 },
      { "symbol": "vole_frontend::lexer::Lexer::next_token", "children_pct": 2.63, "self_pct": 2.24 }
    ]
  }
]
```

- `time_s`: wall-clock seconds for `vole test` under perf record
- `perf_data`: path to perf.data file (for `perf annotate` during investigation)
- `hotspots`: parsed from `perf report`, sorted by children_pct descending
  - `self_pct` is the key metric for identifying optimization targets

Progress goes to stderr. Perf.data files are kept in `/tmp/` so the sub-agent
can use `perf annotate` for instruction-level analysis during investigation.

## Key Differences from stress-hunt

| Aspect | stress-hunt | perf-hunt |
|--------|-------------|-----------|
| Goal | Find correctness bugs | Fix performance hotspots |
| Seeds | Random, new each round | Fixed set, reused for stable comparison |
| Build | Debug (default) | Always release-local |
| Primary tool | `vole test` exit code | `perf record` + `vole test` |
| Iteration unit | K seeds through full pipeline | One hotspot: profile, fix, verify |
| Revert policy | Never revert fixes | Revert if regression >2% |
| Suite evolution | Generator code evolution | Larger/different workloads |

## Important Rules

- NEVER simplify tests — you are hiding bugs
- NEVER assume "pre-existing failures" — you likely broke it
- NEVER skip work or decide it's "too complex"
- Always `just pre-commit` before any commit
- Track shortcuts in tickets with `tk` if any are taken
- Fix ONE hotspot per iteration to keep changes focused
- Always verify with the full benchmark suite, not just one workload
- If a fix regresses performance: revert immediately, don't try to salvage

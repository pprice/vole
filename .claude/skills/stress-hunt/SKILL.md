---
name: stress-hunt
description: Automated bug-hunting loop using vole-stress + vole-reduce. Generates random codebases, tests them, reduces failures, fixes bugs, verifies, and repeats.
---

# Stress Hunt

Automated bug-hunting skill that ties together `vole-stress` (synthetic codebase
generation) and `vole-reduce` (test case minimization) in an iterative loop.

## Invocation

Launch via ralph-loop with a completion promise:

```
/ralph-loop "/stress-hunt 5 20" --completion-promise STRESS_HUNT_DONE
/ralph-loop "/stress-hunt 10 10 full,many-modules" --completion-promise STRESS_HUNT_DONE
```

Or invoke directly (single iteration):

```
/stress-hunt 5 20                       # 5 seeds per round, 20 max rounds
/stress-hunt 10 10 full,many-modules    # 10 seeds, 10 rounds, specific profiles
```

Parse `$ARGUMENTS`:
- First token: K (seeds per round)
- Second token: Z (max rounds) — default 20
- Optional third token: comma-separated profile names

Default profiles if none specified:
`full`, `many-modules`, `deep-nesting`, `wide-types`, `generics-heavy`.

If new profiles are added during Generator Evolution, they are appended to
the `profiles` list in the state file and used in subsequent rounds.

## How It Works

Each iteration processes one round of K seeds through the workflow. When all K
seeds in a round pass or are verified, the round is **completed**: passing seed
directories are cleaned up, and K fresh seeds are generated for the next round.

The skill tracks iterations internally via `round` in the state file. When
`round > Z` (max rounds), output `<promise>STRESS_HUNT_DONE</promise>` to
signal the ralph loop to stop.

**Iteration cost**: a single bug takes at minimum 5 ralph-loop iterations to
fully process (generate → triage → reduce → fix → verify). Plan accordingly
when setting K and Z.

## State File: `.claude/stress-hunt-state.json`

```json
{
  "k": 10,
  "max_rounds": 20,
  "profiles": ["full", "many-modules", "deep-nesting", "wide-types", "generics-heavy"],
  "known_bugs": [
    {
      "fingerprint": "panicked at frontend.rs:509",
      "ticket_id": "vol-xxxx",
      "error_category": "codegen",
      "description": "Cranelift frontend panic on complex types"
    }
  ],
  "seeds": [
    {
      "seed": 12345,
      "profile": "full",
      "dir": "/tmp/vole-stress/clever-badger",
      "status": "pending",
      "error_category": null,
      "error_summary": null,
      "error_fingerprint": null,
      "reduced_dir": null,
      "fix_commit": null,
      "ticket_id": null,
      "dupe_of": null
    }
  ],
  "round": 1,
  "consecutive_clean": 0,
  "base_k": 10,
  "history": [
    { "round": 1, "passed": 3, "failed": 2, "bugs_fixed": 2, "skipped": 0, "dupes": 0 }
  ]
}
```

Seed statuses: `pending` -> `pass` | `fail` -> `reducing` -> `reduced` -> `fixing` -> `verified`
                                                                                  `-> skipped`
                                                            `-> dupe` (matched known bug)

## Journal: `.claude/stress-hunt-journal.md`

A persistent log of facts learned across runs — reserved words, syntax
gotchas, generator pitfalls, process lessons. This file is gitignored and
survives across sessions.

<IMPORTANT>
- **Read the journal** at the start of every stress-hunt session (step 1)
- **Append to the journal** whenever you discover something that would save
  a future run from wasting time — wrong syntax assumptions, reserved words,
  codegen quirks, process mistakes. Keep entries terse (one line each).
</IMPORTANT>

## Workflow Per Iteration

Read `.claude/stress-hunt-state.json`. Based on seed statuses, perform the
**first applicable action** from the list below, then update state and finish.

### 1. Initialize (no state file, or stale state from a previous run)

- **Read `.claude/stress-hunt-journal.md`** to load lessons from previous runs
- If `.claude/stress-hunt-state.json` exists from a previous session (i.e. we
  did NOT create it this session), delete it and start fresh
- **Preflight check**: run `just check` to verify the repo compiles. If it
  fails, stop and report — do not generate seeds against a broken repo.
- Pick K random seeds (use `shuf -i 0-4294967295 -n K` for full u32 range)
- Distribute across profiles round-robin (seed 0 gets profile 0, seed 1 gets
  profile 1, etc., wrapping around)
- Write initial state with all seeds as `pending`, `known_bugs` as `[]`
- Set `round` to 1, `max_rounds` to Z, `history` to `[]`

### 2. Generate + Test (`pending` seeds exist)

<IMPORTANT>
ALWAYS use the `run-round.sh` shell script for generation and testing. NEVER
run `cargo run -p vole-stress` or `cargo run -- test` individually per seed.
The script builds once and runs all seeds in a single invocation — it is
faster, handles timeouts, and produces structured JSONL output.
</IMPORTANT>

**Step-by-step:**

1. Collect all `pending` seeds from the state file into `seed:profile` pairs
2. Run them all in one batch via the script:

```bash
bash .claude/skills/stress-hunt/run-round.sh [flags] /tmp/vole-stress \
  <seed1>:<profile1> <seed2>:<profile2> ...
```

For example, if the state has seeds 12345 (profile=full), 67890
(profile=many-modules), and 11111 (profile=deep-nesting):

```bash
bash .claude/skills/stress-hunt/run-round.sh /tmp/vole-stress \
  12345:full 67890:many-modules 11111:deep-nesting
```

3. Capture stdout (JSONL results) and parse it to update seed statuses

**Flags:**

- `--release` — Build and run with the `release-local` cargo profile
  (optimized with debug symbols). Use when recent rounds have had no failures
  — it iterates much faster. Omit for debug builds (better error messages,
  faster compilation).
- `--diff` — Differential testing: builds both debug and release-local, runs
  each seed under both, and reports mismatches (different exit codes or stdout
  output). Catches optimization-related bugs. Output includes a `diff_mismatch`
  field. Use this periodically (e.g. every 3-5 rounds) to catch bugs that only
  manifest under optimization.
- `--asan` — Build vole with AddressSanitizer (nightly toolchain, into
  `target-asan/`). Catches heap corruption, double-free, and use-after-free
  in the compiler runtime. Mutually exclusive with `--release` and `--diff`.
  Use every 5-10 rounds with moderate K (10-20) — ASan adds ~2-3x overhead.
  ASan errors appear in `error_summary` with `AddressSanitizer:` prefixed
  messages and should be categorized as codegen errors during triage.

**Scaling K:** When using `--release` and recent rounds have zero failures,
increase K to 50-100 seeds per round. The expanded name pool (94k unique
names) supports this without collisions, and release-local builds execute
significantly faster than debug.

**Script output format:** The script builds once, then for each seed:profile
pair it generates, tests (60s timeout), and runs main.vole (30s timeout). It
outputs **JSONL to stdout** — one JSON object per line, one per seed:

```json
{"seed":12345,"profile":"full","dir_name":"soaring-swift-penguin","dir":"/tmp/vole-stress/soaring-swift-penguin","test_status":"pass","run_status":"pass","error_summary":""}
```

In `--diff` mode, an additional `diff_mismatch` field is included (empty string
if both builds agree, otherwise describes the difference).

Status values: `pass`, `fail`, `timeout`, `skip`. Progress goes to stderr.

**Parsing the JSONL output:** For each line, update the corresponding seed in
the state file:
- `test_status` and `run_status` both `pass` → mark seed `pass`
- Any `fail` or `timeout` → mark seed `fail`, record `error_summary`
- `diff_mismatch` non-empty → mark seed `fail` even if both builds "pass"
  (the mismatch itself is the bug)
- Update the seed's `dir` and `dir_name` fields from the JSONL output

Process all pending seeds in one iteration before moving on.

### 3. Triage (`fail` seeds without `error_category`)

For each `fail` seed:

#### 3a. Fingerprint the error

Extract a fingerprint from the error: the panic location (e.g.
`panicked at frontend.rs:509`), the error code + message (e.g.
`[E2023]: unknown method 'foo'`), the signal (e.g. `signal 11`), or the
ASan error type and location (e.g.
`AddressSanitizer: heap-use-after-free on address 0x... at pc 0x...`).
Store in `error_fingerprint`.

#### 3b. Check for duplicates

Compare the fingerprint against `known_bugs` in the state file. If it
matches an existing known bug:
- Set `dupe_of` to the matching ticket ID
- Mark seed as `dupe`
- Add a note to the existing ticket: `tk add-note <id> "Also hit by seed <S> (round N)"`
- **Do not reduce or fix** — the original ticket tracks this bug

If multiple seeds in the same round hit the same *new* error (same
fingerprint, no matching known bug), pick ONE as the primary and mark
the rest as `dupe` of that seed's (future) ticket. Only reduce/fix the
primary.

#### 3c. Categorize (non-duplicate seeds only)

**Generator error** (vole-stress bug):
- `[E0xxx]` lexer errors, `[E1xxx]` parser errors
- `[E2xxx]` sema errors where generated code is clearly structurally wrong
  (impossible types, undefined names that should have been declared)
- Runtime panics caused by invalid generated code (e.g. array index OOB
  on empty arrays from `filter().collect()`)
- Set `error_category: "generator"`
- **Generator bugs MUST be fixed** — do not dismiss them as "pre-existing"
  or move on. If the same generator bug keeps appearing, fix the root cause
  in `src/tools/vole-stress/` before proceeding to the next round.

**Sema error** (type checker bug):
- `[E2xxx]` errors where generated code looks valid but type checker rejects it
- Read the generated code to verify it should be valid Vole
- Set `error_category: "sema"`

**Codegen error** (code generation / runtime bug):
- No E-code errors, timeouts, signal 11 (segfault), panics, wrong results
- AddressSanitizer errors (heap-use-after-free, double-free, heap-buffer-overflow,
  stack-buffer-overflow) — these are always codegen bugs indicating memory
  safety issues in the compiler runtime or generated code
- Set `error_category: "codegen"`

### 4. Reduce (`fail` seeds with `error_category` set)

For each non-dupe `fail` seed, run `vole-reduce` with oracle flags based on
error type:

| Error Pattern | Oracle Flags |
|---------------|-------------|
| Parse/lex error | `--stderr "E0\|E1" --exit-code 1` |
| Sema error | `--stderr "E2" --exit-code 1` |
| Segfault | `--signal 11` |
| Timeout | `--timeout 60` |
| Assertion failure | `--stderr "assertion failed" --exit-code 1` |
| ASan error | `--stderr "AddressSanitizer" --exit-code 1` |
| Generic crash | `--exit-code 1 --stderr "<specific error text>"` |

Always use `--command` with `--manifest-path` since vole-reduce runs from the
result/ directory:

```bash
cargo run -p vole-reduce -- <dir>/ \
  --command 'timeout 90 cargo run --manifest-path /home/phil/code/personal/vole/Cargo.toml -- test {file}' \
  --timeout 60 \
  <oracle-flags>
```

For ASan-detected bugs, use the ASan binary in the oracle command instead:

```bash
cargo run -p vole-reduce -- <dir>/ \
  --command 'timeout 90 env ASAN_OPTIONS=detect_leaks=0 /home/phil/code/personal/vole/target-asan/x86_64-unknown-linux-gnu/debug/vole test {file}' \
  --timeout 60 \
  --stderr "AddressSanitizer" --exit-code 1
```

After reduction completes:

1. **Copy the reduced directory** to a persistent location:
   ```bash
   cp -r <reduced_dir> .claude/stress-hunt-repros/<seed-name>/
   ```
   This is the canonical repro — survives `/tmp` cleanup and generator
   evolution. The reducer may leave multiple files if the bug requires
   cross-module interaction.
2. Update `reduced_dir` and mark `reducing` -> `reduced`.

### 5. Fix (`reduced` seeds exist)

For each `reduced` seed, **actually attempt to fix the bug**. The goal is to
fix it, not just file it. The ticket exists to track your investigation data
— a running log of what you tried, what you found, and what's left.

Fix ONE seed per iteration to keep changes focused and reviewable.

#### Generator bugs (`error_category: "generator"`)

Generator bugs are straightforward vole-stress fixes and do NOT get tickets.
Read the reduced test case, fix the generator code in `src/tools/vole-stress/`,
run `just pre-commit`, commit, and mark `fixing`.

<IMPORTANT>
Generator bugs MUST be fixed immediately — there is no such thing as a
"pre-existing" generator bug. If the generator produces code that panics at
runtime (e.g. array index OOB on empty arrays), that is a bug in the generator
that must be root-caused and fixed, not noted and skipped. Fix the generator
so it never produces that invalid pattern again.
</IMPORTANT>

#### Sema/codegen bugs — dispatch a sub-agent

For sema and codegen bugs, dispatch a **sequential sub-agent** (using the Task
tool) to investigate and attempt the fix.

**Before dispatching the sub-agent:**

1. Read the minimized test case in `reduced_dir`
2. Create a `tk` ticket for the bug (see Ticket Tracking below)
3. Record the ticket ID in the seed's state as `ticket_id`
4. Add the bug to `known_bugs` in the state file with its fingerprint
   and ticket ID, so future duplicates are detected

**The sub-agent's task:**

Give the sub-agent a detailed prompt including:
- The reduced test case code (paste it in the prompt)
- The path to the persistent repro directory (`.claude/stress-hunt-repros/<name>/`)
- The error category and error summary
- The ticket ID for tracking notes
- Which crate to investigate:
  - `sema`: `src/crates/vole-sema/`
  - `codegen`: `src/crates/vole-codegen/` or `src/crates/vole-runtime/`

The sub-agent MUST:
1. Reproduce the bug by running the test case
2. Investigate the root cause — read relevant compiler code, use debuggers
3. Track findings with `tk add-note <id> "..."` as it goes
4. Attempt to fix the bug
5. Add a regression test to `test/unit/` covering the pattern
6. Run `just pre-commit` to verify
7. If fixed: commit, record the commit hash, `tk close <id>`
8. **15-minute time limit**: if unable to fix within ~15 minutes, stop.
   Add a final note to the ticket explaining what was tried, what the
   blocker is, and any leads for future investigation. Leave the ticket
   open as a backlog item.

**After the sub-agent completes:**

- If fixed: update seed with `fix_commit` hash, mark `fixing`
- If not fixed (15-min limit hit): mark seed `skipped`, move on
  - The ticket remains open with investigation notes for future reference

### 6. Verify (`fixing` seeds exist)

For each `fixing` seed:

- **Generator fixes**: must regenerate the seed (generated code changes):
  ```bash
  cargo run -p vole-stress -- --seed <S> --profile <P> --output /tmp/vole-stress --name <same-name>
  ```
  Then re-test.

- **Sema/codegen fixes**: re-test the same files (no regeneration needed):
  ```bash
  timeout 60 cargo run -- test <dir>/
  ```

If passes: mark `verified`.
If new failure: mark `fail` again with new error, clear `error_category`.

### 7. Round Complete (all seeds `pass`, `verified`, `skipped`, or `dupe`)

**A round is NOT complete if any generator bugs were observed but not fixed.**
Generator bugs must be fixed before moving to the next round. Only sema/codegen
bugs that hit the 15-minute time limit may be `skipped`.

When all K seeds in the current round are terminal (`pass`, `verified`,
`skipped`, or `dupe`):

1. Record round summary in `history`:
   ```json
   { "round": N, "passed": X, "failed": Y, "bugs_fixed": Z, "skipped": S, "dupes": D }
   ```
2. Clean up: `rm -rf` the `/tmp/vole-stress/` directories for all terminal
   seeds in this round
3. Print a summary: `Round N complete: X/K passed, Y bugs fixed, S skipped, D dupes`
4. If `round >= max_rounds`: output `<promise>STRESS_HUNT_DONE</promise>` and stop
5. **If any non-dupe failures occurred**: reset `consecutive_clean` to 0
6. **If zero non-dupe failures** (clean round):
   - Increment `consecutive_clean`
   - If `consecutive_clean == 1`: double K for next round (capped at 100),
     do NOT evolve the generator — just run more seeds at current complexity
   - If `consecutive_clean >= 2`: run Generator Evolution (see below),
     then reset K back to `base_k` for the next round
7. Pick K fresh random seeds, distribute across profiles round-robin,
   replace `seeds` array, increment `round`

## Timeout Handling

All commands use the `timeout` utility:
- `timeout 60` for `vole test` (test suites can be slow)
- `timeout 30` for `vole run` (single main function)
- `timeout 90` in vole-reduce oracle command (extra headroom for reduction)
- `--timeout 60` as vole-reduce oracle flag (for hang detection)

Timeout = potential infinite loop. Check the reduced code to determine:
- Generator error: bad loop generation -> fix vole-stress
- Codegen error: bad loop compilation -> fix vole-codegen

## Ticket Tracking (sema/codegen bugs only)

Tickets exist to **track your investigation data as you work**, not just to
file and forget. When a sema or codegen bug is found (after reduction), create
a `tk` ticket immediately, then use it as a running log of your investigation.
Generator bugs are simple vole-stress fixes and don't need tickets.

### Creating the ticket

```bash
tk create "stress-hunt: <short description of bug>" -d "<detailed description>"
```

The description should include:
- Seed number and profile
- Error category (sema or codegen)
- Error message or symptom (segfault, timeout, wrong result, etc.)
- Path to the persistent repro directory (`.claude/stress-hunt-repros/<name>/`)
- The reduced code itself (paste it in)

Record the ticket ID in the seed's `ticket_id` field in state.

### Updating during investigation

As you investigate, add notes with findings. The ticket is your running log —
if you hit the 15-minute limit, these notes are what makes the ticket useful
for future investigation:

```bash
tk add-note <id> "Root cause: <explanation>"
tk add-note <id> "Attempted fix: <what you tried>"
tk add-note <id> "Blocker: <why this is hard>"
tk add-note <id> "Relevant code: <file:line — what it does>"
```

### On fix

```bash
tk add-note <id> "Fixed in commit <hash>: <what was changed>"
tk close <id>
```

### On skip (15-minute limit exceeded)

```bash
tk add-note <id> "Skipping after 15min. Tried: <approaches>. Blocker: <issue>. Leads: <suggestions>"
```

Leave the ticket open with all investigation notes — it becomes a backlog
item with enough context for someone to pick up where you left off.

## Generator Evolution (clean rounds)

When a round completes with **zero non-dupe failures**, decide whether to
evolve or just run more seeds:

- **First clean round in a row**: double K for the next round (up to 100),
  do NOT evolve. More seeds at current complexity is cheaper than evolving.
- **Second+ consecutive clean round**: evolve the generator, then reset K
  back to the original value for the next round.

The goal is to generate increasingly exotic but **valid** Vole code — with
a bias toward *feature interactions* and *edge cases* over breadth.

This runs **before** the next round starts, not in parallel.

### Process

1. **Re-read `.claude/stress-hunt-journal.md`** before picking a feature —
   check for reserved words, syntax gotchas, and known pitfalls
2. Pick ONE small enhancement from the priority areas below
3. **Verify syntax first**: before writing any generator code, write a small
   hand-crafted `.vole` file in `/tmp/` that uses the feature you plan to
   generate. Run it with `cargo run -- test /tmp/test_feature.vole` (or
   `cargo run -- run /tmp/test_feature.vole`). This catches wrong assumptions
   about syntax early (e.g. tuple indexing is `tuple[0]` not `tuple.0`).
   If the syntax doesn't work as expected, adjust your plan or pick a
   different feature. **If you learn something new (reserved words, syntax
   quirks), append it to the journal.**
4. Launch a sub-agent to implement it. The sub-agent MUST:
   - Read existing `test/**/*.vole` files to understand valid syntax/structure
   - Make the change to `src/tools/vole-stress/`
   - Run `just pre-commit` to verify the change compiles
   - If pre-commit fails, fix or revert
5. **Wait for the sub-agent to complete** before continuing
6. **Validate** with multiple seeds across profiles:
   ```bash
   for seed in 999999 888888 777777 666666 555555; do
     cargo run -p vole-stress -- --seed $seed --profile full --output /tmp/vole-stress-validate
     timeout 60 cargo run -- test /tmp/vole-stress-validate/<dir>/
     rm -rf /tmp/vole-stress-validate/<dir>
   done
   ```
   Also validate any new profile specifically with 3+ seeds.
7. **Classify validation failures** (see below)
8. If validation passes: **commit** the change, then proceed to the next round
9. **If a new profile was added**: append its name to the `profiles` array in
   the state file so it gets used in round-robin seed distribution going forward.
10. The next round's stress tests will exercise the new feature across K seeds

### Classifying validation failures

When a generator evolution causes test failures, determine the failure type:

**Generator bug** (invalid code generated):
- Bad syntax, undefined names, structurally wrong types
- Infinite loops on the Vole side (not compiler-side)
- Code that is clearly not valid Vole

**Action**: fix the generator. If you can't fix it, **revert entirely**
(`git checkout -- src/tools/vole-stress/`).

**Compiler bug** (valid code that exposes a compiler/runtime issue):
- Segfaults, panics, wrong results, codegen crashes
- The generated code is valid Vole — the compiler should handle it

**Action — two parts, BOTH required:**

**Part 1**: commit the generator change — it found a real bug, that's good.

**Part 2 (mandatory — do NOT skip)**: attempt to fix each failing seed's
compiler bug before proceeding to the next round. For each distinct failure:
1. Reduce the failing test case with `vole-reduce`
2. Save the repro to `.claude/stress-hunt-repros/`
3. Create a `tk` ticket for the compiler bug
4. Dispatch a sub-agent to attempt the fix (same as step 5 workflow)
5. If fixed: commit the compiler fix too
6. If not fixed (15-min limit): leave the ticket open

After all failures are attempted (fixed or skipped), check whether the
generator change causes widespread failures:
- If only 1-2 of 5 validation seeds fail: **keep the generator change**.
  The next round will hit the bug, and the dedup logic will handle it.
- If most/all seeds fail: **revert the generator change** to avoid
  poisoning every round. Create a follow-up ticket to re-add the
  generator feature once the compiler bug is fixed:
  ```bash
  tk create "stress-hunt: re-add <feature> after <compiler-bug-id> is fixed" \
    -d "Generator evolution for <feature> was reverted because it triggers <bug>. Re-add once the compiler bug is resolved."
  tk dep <re-add-id> <compiler-bug-id>
  ```

Only proceed to the next round after Part 2 is complete.

### Choosing What to Evolve

Roll a dice (`shuf -i 1-10 -n 1`) to select the evolution category:

| Roll | Category | Why |
|------|----------|-----|
| 1-4  | **Feature interactions** | Cross-cutting combos are where real bugs hide |
| 5-7  | **Edge cases & boundaries** | Boundary conditions stress codegen/RC/sema |
| 8-9  | **Language features** | New syntax coverage, structural patterns |
| 10   | **Breadth** | Stdlib methods, API surface |

Record the roll and chosen category in the commit message (e.g.
`vole-stress: [roll=3/interactions] generate closures capturing union fields`).

### Category Details

Reference `test/**/*.vole` files for valid syntax patterns before implementing.

**Feature interactions** (rolls 1-4) — combine 2+ features that stress
different compiler subsystems together. These find the most bugs because
they exercise codegen paths that individual features don't reach alone.

Pick combinations, not individual features. Examples:
- Generics + interface dispatch (generic fn calling interface method)
- Closures + RC types (closure capturing a class instance or string)
- Unions + pattern matching + RC (match on union variant containing RC type)
- Generics + closures (generic fn taking closure parameter)
- Interface upcasting + method calls in generic context
- Optional chaining on results of generic function calls
- Fallible functions + closures (`try` block inside closure)
- Iterators + closures capturing outer mutable state
- Cross-module generics (generic type defined in one module, used in another)
- Nested containers (array of optional of class implementing interface)
- Match/when inside closures that capture variables
- String interpolation with method calls on generic types
- Destructuring + union types + optional fields
- Multiple interface implementations + generic constraints
- Recursive functions with generic parameters and interface bounds

**Edge cases & boundaries** (rolls 5-7) — boundary conditions, unusual but
valid inputs, and patterns that stress reference counting, memory layout,
or type resolution.

Examples:
- Empty arrays/strings passed to iterator chains
- Deeply nested optional unwrapping (`x??.field??.method()`)
- Zero-variant and single-variant unions
- Functions with many parameters (8+, 16+) — stresses calling conventions
- Large tuple types (5+, 8+ elements)
- Deeply nested function calls (f(g(h(x)))) with type coercions at each level
- Match/when with many arms (20+, 50+)
- Strings containing special characters, empty strings, very long strings
- Numeric boundary values (i32::MAX, i64::MIN, etc.) in expressions
- Classes with many fields (10+, 20+), some optional, some RC
- Arrays with mixed operations (push then pop then iterate then map)
- Chained method calls (5+ deep) on iterators or strings
- Diamond interface inheritance with method name conflicts
- Default parameter values that are complex expressions
- Break/continue in nested loops with closures in between

**Language features** (rolls 8-9) — new syntax or structural patterns
the generator doesn't use yet. Focus on features that are likely to interact
with existing generation in complex ways.

Examples:
- Type aliases (especially aliasing generic types)
- Nested generic types (`Array<Optional<MyClass<T>>>`)
- Multi-line string literals
- `unreachable` keyword in exhaustive branches
- Modules re-exporting imported symbols
- Multiple implement blocks for the same class
- Test blocks that exercise error paths
- Complex control flow (break/continue in nested loops with early returns)
- Recursive data patterns (where valid)
- Functions returning functions (closures)

**Breadth** (roll 10) — adding individual stdlib methods, API surface
coverage. Still useful but unlikely to find new bug categories.

Examples:
- String methods not yet generated
- Array/iterator methods not yet generated
- Math operations: bitwise, shifts
- Type conversions between numeric types

### Rules for generator changes

- Each change should be SMALL and focused (one feature per round)
- Always verify generated code compiles AND passes tests
- If a change generates **invalid code**: fix the generator or revert
- If a change generates **valid code** that crashes the compiler: keep the
  generator change, fix the compiler (see Classifying validation failures)
- Reference `test/` files for syntax, but don't copy tests wholesale

## Regression Tests

When fixing **sema** or **codegen** bugs, always add a regression test to
`test/unit/`. The test should:

- Be in an appropriate subdirectory (e.g. `test/unit/language/interfaces/`)
- Cover the specific pattern that triggered the bug
- Include a descriptive test name
- Test both the failing case and related edge cases

## Important Rules

- NEVER simplify tests — you are hiding bugs
- NEVER assume "pre-existing failures" — you likely broke it
- NEVER skip work or decide it's "too complex"
- **ALL generator bugs must be fixed immediately** — do not label them
  "pre-existing" and move on. If a generator pattern produces invalid code
  (e.g. indexing empty arrays from `filter().collect()`), find and fix the
  root cause in `src/tools/vole-stress/`. A recurring generator bug that is
  never fixed is wasted signal in every future round.
- Always `just pre-commit` before any commit
- Track shortcuts in tickets with `tk` if any are taken
- Fix ONE bug per iteration to keep commits focused
- Always add regression tests to `test/unit/` for sema/codegen fixes

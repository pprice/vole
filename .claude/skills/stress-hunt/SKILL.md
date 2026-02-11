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
  "history": [
    { "round": 1, "passed": 3, "failed": 2, "bugs_fixed": 2, "skipped": 0, "dupes": 0 }
  ]
}
```

Seed statuses: `pending` -> `pass` | `fail` -> `reducing` -> `reduced` -> `fixing` -> `verified`
                                                                                  `-> skipped`
                                                            `-> dupe` (matched known bug)

## Workflow Per Iteration

Read `.claude/stress-hunt-state.json`. Based on seed statuses, perform the
**first applicable action** from the list below, then update state and finish.

### 1. Initialize (no state file, or stale state from a previous run)

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

For each `pending` seed:

```bash
cargo run -p vole-stress -- --seed <S> --profile <P> --output /tmp/vole-stress
```

Capture the output directory name from stdout. Then test:

```bash
timeout 60 cargo run -- test <dir>/
```

And if a `main.vole` exists:

```bash
timeout 30 cargo run -- run <dir>/main.vole
```

- If both pass: mark `pass`
- If either fails or times out: mark `fail`, record error in `error_summary`
  (**truncate to first 20 lines** — keep the key error, not full backtraces)

Process all pending seeds in one iteration before moving on.

### 3. Triage (`fail` seeds without `error_category`)

For each `fail` seed:

#### 3a. Fingerprint the error

Extract a fingerprint from the error: the panic location (e.g.
`panicked at frontend.rs:509`), the error code + message (e.g.
`[E2023]: unknown method 'foo'`), or the signal (e.g. `signal 11`).
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
- Set `error_category: "generator"`

**Sema error** (type checker bug):
- `[E2xxx]` errors where generated code looks valid but type checker rejects it
- Read the generated code to verify it should be valid Vole
- Set `error_category: "sema"`

**Codegen error** (code generation / runtime bug):
- No E-code errors, timeouts, signal 11 (segfault), panics, wrong results
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
| Generic crash | `--exit-code 1 --stderr "<specific error text>"` |

Always use `--command` with `--manifest-path` since vole-reduce runs from the
result/ directory:

```bash
cargo run -p vole-reduce -- <dir>/ \
  --command 'timeout 90 cargo run --manifest-path /home/phil/code/personal/vole/Cargo.toml -- test {file}' \
  --timeout 60 \
  <oracle-flags>
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
5. **If zero non-dupe failures**: run Generator Evolution (see below) before
   continuing
6. Pick K fresh random seeds, distribute across profiles round-robin,
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

When a round completes with **zero non-dupe failures**, add a small feature to
`vole-stress` that increases language coverage. The goal is to generate
increasingly exotic but **valid** Vole code.

This runs **before** the next round starts, not in parallel.

### Process

1. Pick ONE small enhancement from the priority areas below
2. **Verify syntax first**: before writing any generator code, write a small
   hand-crafted `.vole` file in `/tmp/` that uses the feature you plan to
   generate. Run it with `cargo run -- test /tmp/test_feature.vole` (or
   `cargo run -- run /tmp/test_feature.vole`). This catches wrong assumptions
   about syntax early (e.g. tuple indexing is `tuple[0]` not `tuple.0`).
   If the syntax doesn't work as expected, adjust your plan or pick a
   different feature.
3. Launch a sub-agent to implement it. The sub-agent MUST:
   - Read existing `test/**/*.vole` files to understand valid syntax/structure
   - Make the change to `src/tools/vole-stress/`
   - Run `just pre-commit` to verify the change compiles
   - If pre-commit fails, fix or revert
4. **Wait for the sub-agent to complete** before continuing
5. **Validate** with multiple seeds across profiles:
   ```bash
   for seed in 999999 888888 777777 666666 555555; do
     cargo run -p vole-stress -- --seed $seed --profile full --output /tmp/vole-stress-validate
     timeout 60 cargo run -- test /tmp/vole-stress-validate/<dir>/
     rm -rf /tmp/vole-stress-validate/<dir>
   done
   ```
   Also validate any new profile specifically with 3+ seeds.
6. **Classify validation failures** (see below)
7. If validation passes: **commit** the change, then proceed to the next round
8. **If a new profile was added**: append its name to the `profiles` array in
   the state file so it gets used in round-robin seed distribution going forward.
9. The next round's stress tests will exercise the new feature across K seeds

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

### Priority Areas

Pick enhancements in rough priority order. Reference `test/**/*.vole` files
for valid syntax patterns before implementing.

**a) Language coverage gaps** — features the generator doesn't use yet:
- `match` with guards (`_ if condition => ...`)
- Nested `when`/`match` in more positions (arguments, field values)
- String interpolation with expressions (`"result: {x + y}"`)
- Tuple indexing (`tuple.0`, `tuple.1`)
- Multi-line string literals
- `unreachable` keyword in exhaustive branches
- Range expressions in more contexts (`for i in 0..n`)
- Chained comparisons and boolean logic patterns
- Type aliases
- Nested generic types

**b) Exotic but valid patterns:**
- Deeply nested type expressions (optional of array of tuple)
- Union types with 3+ variants
- Functions returning functions (closures)
- Closures capturing outer variables
- Diamond interface implementations
- Method calls in string interpolation
- Chained optional unwrap (`value ?? default ?? fallback`)
- Nested destructuring
- Passing class instances as interface-typed parameters
- Recursive data patterns (where valid)

**c) Standard library usage (excluding IO):**
- String methods: `.contains()`, `.length()`, `.split()`, `.trim()`,
  `.starts_with()`, `.ends_with()`, `.to_upper()`, `.to_lower()`
- Array methods: `.length()`, `.map()`, `.filter()`, `.push()`, `.pop()`
- Math operations: bitwise, shifts, overflow behavior
- Type conversions between numeric types
- Optional chaining and coalescing patterns

**d) Structural patterns:**
- Multiple implement blocks for the same class
- Fallible functions with `try`/`raise`
- Generic functions with interface constraints
- Modules re-exporting imported symbols
- Test blocks that exercise error paths
- Complex control flow (break/continue in nested loops)
- Large switch/match with many arms

**e) New profiles** (add to `profile.rs` alongside existing ones):
- Profiles that focus generation on specific feature combinations
- E.g. `closures-heavy`, `unions-heavy`, `fallible-heavy`, `stdlib-heavy`
- Each profile should tune the config knobs to emphasize its focus area
- When adding a new profile, update the state file's `profiles` array

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
- Always `just pre-commit` before any commit
- Track shortcuts in tickets with `tk` if any are taken
- Fix ONE bug per iteration to keep commits focused
- Always add regression tests to `test/unit/` for sema/codegen fixes

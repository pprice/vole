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

## How It Works

Each iteration processes one round of K seeds through the workflow. When all K
seeds in a round pass or are verified, the round is **completed**: passing seed
directories are cleaned up, and K fresh seeds are generated for the next round.

The skill tracks iterations internally via `round` in the state file. When
`round > Z` (max rounds), output `<promise>STRESS_HUNT_DONE</promise>` to
signal the ralph loop to stop.

## State File: `.claude/stress-hunt-state.json`

```json
{
  "k": 10,
  "max_rounds": 20,
  "profiles": ["full", "many-modules", "deep-nesting", "wide-types", "generics-heavy"],
  "seeds": [
    {
      "seed": 12345,
      "profile": "full",
      "dir": "/tmp/vole-stress/clever-badger",
      "status": "pending",
      "error_category": null,
      "error_summary": null,
      "reduced_dir": null,
      "fix_commit": null,
      "ticket_id": null
    }
  ],
  "round": 1,
  "history": [
    { "round": 1, "passed": 3, "failed": 2, "bugs_fixed": 2, "skipped": 0 }
  ]
}
```

Seed statuses: `pending` -> `pass` | `fail` -> `reducing` -> `reduced` -> `fixing` -> `verified`
                                                                                  `-> skipped`

## Workflow Per Iteration

Read `.claude/stress-hunt-state.json`. Based on seed statuses, perform the
**first applicable action** from the list below, then update state and finish.

### 1. Initialize (no state file, or stale state from a previous run)

- If `.claude/stress-hunt-state.json` exists from a previous session (i.e. we
  did NOT create it this session), delete it and start fresh
- Pick K random seeds (use `shuf -i 0-4294967295 -n K` for full u32 range)
- Distribute across profiles round-robin (seed 0 gets profile 0, seed 1 gets
  profile 1, etc., wrapping around)
- Write initial state with all seeds as `pending`
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
- If either fails or times out: mark `fail`, record error output in `error_summary`

Process all pending seeds in one iteration before moving on.

### 3. Triage (`fail` seeds without `error_category`)

For each `fail` seed, categorize the error. Check in priority order:

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

For each `fail` seed, run `vole-reduce` with oracle flags based on error type:

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

After reduction completes, update `reduced_dir` and mark `reducing` -> `reduced`.

### 5. Fix (`reduced` seeds exist)

For each `reduced` seed:

1. Read the minimized test case in `reduced_dir`
2. Create a `tk` ticket for the bug (see Ticket Tracking below)
3. Investigate the root cause based on `error_category`:
   - `generator`: fix in `src/tools/vole-stress/`
   - `sema`: fix in `src/crates/vole-sema/`
   - `codegen`: fix in `src/crates/vole-codegen/` or `src/crates/vole-runtime/`
4. Add investigation notes to the ticket as you go with `tk add-note`
5. **15-minute time limit**: if unable to fix within ~15 minutes, stop
   attempting. Add a note to the ticket explaining what was tried, what
   the blocker is, and any leads. Leave the ticket open. Mark the seed
   `skipped` in state and move on.
6. If fixed: run `just pre-commit`, commit, record `fix_commit` hash,
   mark seed `fixing`, close the ticket with `tk close`
7. Record the ticket ID in the seed's state as `ticket_id`

Fix ONE seed per iteration to keep changes focused and reviewable.

Generator bugs do NOT get tickets — they are straightforward vole-stress
fixes. Only sema and codegen bugs get tracked in `tk`.

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

### 7. Round Complete (all seeds `pass`, `verified`, or `skipped`)

When all K seeds in the current round are `pass`, `verified`, or `skipped`:

1. Record round summary in `history`:
   ```json
   { "round": N, "passed": X, "failed": Y, "bugs_fixed": Z, "skipped": S }
   ```
2. Clean up: `rm -rf` the `/tmp/vole-stress/` directories for all `pass`,
   `verified`, and `skipped` seeds in this round
3. Print a summary: `Round N complete: X/K passed, Y bugs fixed, S skipped`
4. If `round >= max_rounds`: output `<promise>STRESS_HUNT_DONE</promise>` and stop
5. Otherwise: pick K fresh random seeds, distribute across profiles round-robin,
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

When a sema or codegen bug is found (after reduction), create a `tk` ticket
to track it. Generator bugs are simple vole-stress fixes and don't need tickets.

### Creating the ticket

```bash
tk create "stress-hunt: <short description of bug>" -d "<detailed description>"
```

The description should include:
- Seed number and profile
- Error category (sema or codegen)
- Error message or symptom (segfault, timeout, wrong result, etc.)
- Path to the reduced test case
- The reduced code itself (paste it in)

Record the ticket ID in the seed's `ticket_id` field in state.

### Updating during investigation

As you investigate, add notes with findings:

```bash
tk add-note <id> "Root cause: <explanation>"
tk add-note <id> "Attempted fix: <what you tried>"
tk add-note <id> "Blocker: <why this is hard>"
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

Leave the ticket open — it becomes a backlog item for manual investigation.

## Important Rules

- NEVER simplify tests — you are hiding bugs
- NEVER assume "pre-existing failures" — you likely broke it
- NEVER skip work or decide it's "too complex"
- Always `just pre-commit` before any commit
- Track shortcuts in tickets with `tk` if any are taken
- Fix ONE bug per iteration to keep commits focused

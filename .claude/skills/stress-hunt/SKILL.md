---
name: stress-hunt
description: Automated bug-hunting loop using vole-stress + vole-reduce. Generates random codebases, tests them, reduces failures, fixes bugs, verifies, and repeats.
---

# Stress Hunt

Automated bug-hunting skill that ties together `vole-stress` (synthetic codebase
generation) and `vole-reduce` (test case minimization) in an iterative loop.

## Invocation

```
/stress-hunt 10                     # 10 seeds, round-robin across all profiles
/stress-hunt 5 full,many-modules    # 5 seeds, specific profiles only
```

Parse `$ARGUMENTS`: first token is K (number of seeds), optional second token is
comma-separated profile names. Default profiles if none specified:
`full`, `many-modules`, `deep-nesting`, `wide-types`, `generics-heavy`.

## Ralph Loop Setup

On first invocation (no `.claude/stress-hunt-state.json` exists), write
`.claude/.ralph-loop.local.md` with:

```markdown
prompt: /stress-hunt <K> [profiles]
completion-promise: ALL_SEEDS_PASS
```

If `.claude/.ralph-loop.local.md` already exists, skip — we are already looping.

Each iteration: read state, perform next action, update state, finish the turn.
The stop hook feeds the same `/stress-hunt` prompt back for the next iteration.

## State File: `.claude/stress-hunt-state.json`

```json
{
  "k": 10,
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
      "fix_commit": null
    }
  ],
  "round": 1
}
```

Seed statuses: `pending` -> `pass` | `fail` -> `reducing` -> `reduced` -> `fixing` -> `verified`

## Workflow Per Iteration

Read `.claude/stress-hunt-state.json`. Based on seed statuses, perform the
**first applicable action** from the list below, then update state and finish.

### 1. Initialize (no state file)

- Pick K random seeds (use `$RANDOM` or similar)
- Distribute across profiles round-robin (seed 0 gets profile 0, seed 1 gets
  profile 1, etc., wrapping around)
- Write initial state with all seeds as `pending`
- Set round to 1

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
2. Investigate the root cause based on `error_category`:
   - `generator`: fix in `src/tools/vole-stress/`
   - `sema`: fix in `src/crates/vole-sema/`
   - `codegen`: fix in `src/crates/vole-codegen/` or `src/crates/vole-runtime/`
3. Run `just pre-commit` before committing
4. Commit the fix
5. Record `fix_commit` hash, mark `fixing`

Fix ONE seed per iteration to keep changes focused and reviewable.

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

### 7. Check Completion

If ALL seeds are `pass` or `verified`:
1. Run `just pre-commit` one final time
2. If it passes, output: `<promise>ALL_SEEDS_PASS</promise>`

If some seeds still need work, increment `round` in state and continue.

## Timeout Handling

All commands use the `timeout` utility:
- `timeout 60` for `vole test` (test suites can be slow)
- `timeout 30` for `vole run` (single main function)
- `timeout 90` in vole-reduce oracle command (extra headroom for reduction)
- `--timeout 60` as vole-reduce oracle flag (for hang detection)

Timeout = potential infinite loop. Check the reduced code to determine:
- Generator error: bad loop generation -> fix vole-stress
- Codegen error: bad loop compilation -> fix vole-codegen

## Important Rules

- NEVER simplify tests — you are hiding bugs
- NEVER assume "pre-existing failures" — you likely broke it
- NEVER skip work or decide it's "too complex"
- Always `just pre-commit` before any commit
- Always `just pre-commit` before outputting the completion promise
- Track shortcuts in tickets with `tk` if any are taken
- Fix ONE bug per iteration to keep commits focused

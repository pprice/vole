# AGENTS.md

This file summarizes local agent instructions for this repo.

## Required Reads

- Always read `CLAUDE.md` for repo guidance.
- Always check `CLAUDE.local.md` for private instructions.
- If in a git worktree, read `CLAUDE.local.md` from the main worktree (first entry in `git worktree list`).

## Project Context

- Vole is a compiled programming language with JIT compilation via Cranelift.
- Original source of truth is the Zig project at `~/code/personal/void`; refer to it (including docs/tests) when adding features.

## Working Style

- Bias toward action; use tools to investigate.
- Be concise; check before asking.
- Use haiku agents for simple tasks (single-file edits, docs, mechanical changes, simple commits).

## Build and Test

Prefer `just` commands:

- `just build` for debug build
- `just ci` for full checks
- `just unit` for unit tests
- `just snap` for snapshot tests

## Files and Modules

- Keep files ~1000 lines; prefer new files over growing large ones.
- When splitting, use logical submodules and split `impl` blocks.

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed) - Tests, linters, builds
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds

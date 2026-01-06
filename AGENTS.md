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

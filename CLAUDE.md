# CLAUDE.md

## Loading Private Instructions

Check for `CLAUDE.local.md` (private, not in git). In git worktrees, find it via `git worktree list`.

## Working Style

- **Bias toward action** - use tools to investigate instead of speculating
- **Be concise** - don't over-explain, just do it
- **Check before asking** - answer questions with tools first
- **Use haiku for simple tasks** - single-file edits, docs, mechanical changes

## Project Overview

Vole is a compiled language with JIT via Cranelift.

**Pipeline:** frontend (lexer/parser/AST) → sema (type checking) → codegen (Cranelift IR) → runtime

Key directories:
- `frontend/` - lexer.rs, token.rs, parser/, ast.rs, intern.rs
- `sema/` - analyzer/ (expr.rs, stmt.rs, patterns.rs), types.rs, scope.rs
- `codegen/` - compiler/ (patterns.rs, calls.rs, ops.rs, methods.rs), jit.rs
- `errors/` - sema.rs (E2xxx), parser.rs (E1xxx), lexer.rs (E0xxx)

## Commands

```bash
just check          # Fast type check (run after ANY change)
just ci             # All checks (format, clippy, test, snap)
just unit           # Run vole unit tests
just snap           # Run snapshot tests
cargo run -- run file.vole    # Execute
cargo run -- test dir/        # Run test blocks
```

Dev tools: `just dev-next-error sema`, `just dev-trace-keyword raise`, `just dev-test-for lambda`

## Where to Edit

| Task | Files |
|------|-------|
| New keyword/token | `frontend/lexer.rs`, `frontend/token.rs` |
| New expression | `frontend/parser/parse_expr.rs`, `frontend/ast.rs` |
| New statement | `frontend/parser/parse_stmt.rs`, `frontend/ast.rs` |
| New operator | lexer → parser → `sema/analyzer/expr.rs` → `codegen/compiler/ops.rs` |
| Type checking | `sema/analyzer/expr.rs`, `stmt.rs`, `patterns.rs` |
| New error code | `errors/sema.rs` or `errors/parser.rs` |
| Codegen | `codegen/compiler/patterns.rs`, `calls.rs`, `methods.rs` |
| Builtins | `runtime/builtins.rs`, register in `codegen/compiler/calls.rs` |

## Testing

| Type | Location | Use For |
|------|----------|---------|
| Unit tests | `test/unit/` | Preferred. Code that runs. |
| Snapshot/check | `test/snapshot/check/` | Error messages |
| Snapshot/run | `test/snapshot/run/` | Smoke tests |

Format: `tests { test "name" { assert(...) } }`
Bless: `cargo run --bin vole-snap -- bless path/`

### Skipped Tests

Files/directories starting with `_` are skipped by default (WIP tests for unimplemented features).

```bash
# Run all tests including skipped
cargo run -- test test/unit/ --include-skipped
vole-snap test test/snapshot/ --include-skipped

# Run a specific skipped file directly (bypasses skip)
cargo run -- test test/unit/language/_raw_strings.vole
```

WIP test files live in `test/unit/language/_*.vole`.

## Verification

**ALWAYS run `just check` after ANY code change.**

Never claim success when:
- `cargo check` shows errors
- Tests are failing
- Subagents must verify `cargo check` exits 0

## Language Syntax

Types: `i32`, `i64`, `f64`, `bool`, `string`, `nil`, `T?` (optional)
See `docs/language/cheatsheet.md` for full reference.

## Name Identity System

- **Symbol** (frontend/intern.rs): u32 into Interner. AST layer only, NOT stable across interners.
- **NameId** (identity.rs): u32 into NameTable. Cross-module safe, sema/codegen layer.

Type structs use `name_id: NameId`, not Symbol. NameTable stores definition locations for diagnostics.

## Common Pitfalls

- **AST changes cascade**: ast.rs changes require updates in parser, sema, codegen, printer, transforms
- **Type vs TypeExpr**: Type = resolved (sema), TypeExpr = syntax (AST)
- **Interface boxing**: returning record as interface requires boxing (`box_interface_value`)
- **Generator transform**: builds AST directly, bypasses parser

## File Size

Target ~1000 lines, max 2000. Prefer creating new files over extending existing ones.

## Debugging

```bash
vole inspect ast file.vole       # Show AST
vole inspect ir file.vole        # Show Cranelift IR
just dev-backtrace-test file.vole  # Debug segfaults
just trace file.vole             # Tracing with VOLE_LOG
```

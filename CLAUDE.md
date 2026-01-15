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
- `sema/` - analyzer/, types/, entity_registry/, generic.rs, resolve.rs
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

## Refactoring with ast-grep

Use `ast-grep` (command: `ast-grep`) for structural search/replace. It understands Rust syntax.

```bash
# Find pattern (dry-run)
ast-grep run --pattern 'Type::$VARIANT' --lang rust src/

# Find and replace (shows diff)
ast-grep run --pattern 'OldName::$V' --rewrite 'NewName::$V' --lang rust src/

# Apply changes
ast-grep run --pattern 'OldName::$V' --rewrite 'NewName::$V' --lang rust src/ --update-all
```

**Pattern syntax:**
- `$VAR` - single AST node
- `$$$VAR` - multiple nodes (variadic)
- Literal code matches literally

**Common patterns:**
```bash
# Rename enum variants
ast-grep run -p 'Type::$V($$$A)' -r 'LegacyType::$V($$$A)' -l rust src/

# Rename type annotations
ast-grep run -p ': Type' -r ': LegacyType' -l rust src/

# Find impl blocks
ast-grep run -p 'impl Type { $$$BODY }' -l rust src/
```

Always test without `--update-all` first, then run `just check` after applying.

## Where to Edit

| Task | Files |
|------|-------|
| New keyword/token | `frontend/lexer.rs`, `frontend/token.rs` |
| New expression | `frontend/parser/parse_expr.rs`, `frontend/ast.rs` |
| New statement | `frontend/parser/parse_stmt.rs`, `frontend/ast.rs` |
| New operator | lexer → parser → `sema/analyzer/expr.rs` → `codegen/compiler/ops.rs` |
| Type checking | `sema/analyzer/expr.rs`, `stmt.rs`, `patterns.rs` |
| Generics/type params | `sema/generic.rs`, `sema/analyzer/inference.rs` |
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

NEVER "simplify" tests, even if you just created them.

### When Tests Reveal Unimplemented Features

If tests fail due to missing language features (not bugs), follow this workflow:

1. **Create a WIP test file** with `_` prefix (e.g., `_feature_name.vole`)
2. **Move the failing tests** to the WIP file, keeping the original test file working
3. **Create a bead** to track the feature: `bd create --title="Feature description" --type=feature`
4. **Reference the bead** in the WIP test file header comment
5. **Never simplify or remove tests** - they prove correctness once the feature is implemented

Example WIP test file header:
```vole
// Test: Feature description
// WIP: Requires implementation of X
// Tracked by bead: vole-xxxx
```

### Skipped Tests

Files/directories starting with `_` are skipped by default (WIP tests for unimplemented features).

```bash
# Run all tests including skipped
cargo run -- test test/unit/ --include-skipped
vole-snap test test/snapshot/ --include-skipped

# Run a specific skipped file directly (bypasses skip)
cargo run -- test test/unit/language/_raw_strings.vole
```

WIP test files live in `test/unit/language/_*.vole` or `test/unit/language/generics/_*.vole`.

## Verification

**ALWAYS run `just check` after ANY code change.**

Never claim success when:
- `cargo check` shows errors
- Tests are failing
- Subagents must verify `cargo check` exits 0
- You have "simplified" tests

## Partial Fixes Policy

**Never leave partial fixes without tracking.**

If you cannot fully complete a fix:
1. DO NOT claim the task is done
2. Create a follow-up bead with `bd create` describing remaining work
3. Link it as blocking if appropriate
4. Mention the follow-up bead in your response

Examples of partial fixes that need follow-up beads:
- Fixed 3 of 5 occurrences of a pattern
- Added feature but didn't add tests
- Fixed the bug but didn't handle edge case
- Refactored one file but similar changes needed elsewhere

Bad: "Fixed most of the issues, some edge cases remain"
Good: "Fixed X, created vole-abc for remaining Y"

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

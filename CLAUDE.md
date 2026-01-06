# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Loading Private Instructions

Always check for `CLAUDE.local.md` which contains private instructions not checked into git.

**If in a git worktree**, find and load `CLAUDE.local.md` from the main repo:
```bash
git worktree list  # First entry is the main worktree
```

## Working Style

- **Bias toward action** - use tools to investigate instead of speculating
- **Be concise** - don't over-explain what you're about to do, just do it
- **Check before asking** - if you can answer a question with a tool, do that first
- **Use haiku for simple tasks** - spawn haiku agents for single-file edits, docs, mechanical changes, and simple commits

## Project Overview

Vole is a compiled programming language with JIT compilation via Cranelift.

### Pipeline

1. **frontend/** - Lexing and parsing
   - `lexer.rs`, `token.rs` → tokenization
   - `parser/` → AST (`parse_expr.rs`, `parse_stmt.rs`, `parse_decl.rs`)
   - `ast.rs` → node definitions, `intern.rs` → symbol interning

2. **sema/** - Semantic analysis
   - `analyzer/` → type checking (`expr.rs`, `stmt.rs`, `patterns.rs`, `methods.rs`)
   - `types.rs` → type representation, `scope.rs` → lexical scoping

3. **codegen/** - Code generation
   - `compiler/` → Cranelift IR (`patterns.rs`, `calls.rs`, `ops.rs`, `methods.rs`, `fields.rs`)
   - `jit.rs` → JIT context

4. **runtime/** - `builtins.rs`, `string.rs` (RcString)

5. **errors/** - `sema.rs` (E2xxx), `parser.rs` (E1xxx), `lexer.rs` (E0xxx)

## Build Commands

```bash
just build       # Debug build
just ci          # Run all checks (format, clippy, test, snap)
just pre-commit  # Quick checks and fixes before committing
just unit        # Run vole unit tests
just snap        # Run snapshot tests
```

Dev tools:
```bash
just dev-next-error sema       # Next available error code
just dev-trace-keyword raise   # Trace keyword through pipeline
just dev-list-errors sema      # List all error codes
just dev-test-for lambda       # Find tests for a feature
just dev-void-ref <file>       # Show equivalent Void (Zig) reference
just dev-tokens                # List all token types
just dev-todos                 # List TODOs and FIXMEs
```

Run vole programs:
```bash
cargo run -- run file.vole     # Execute
cargo run -- check file.vole   # Type-check only
cargo run -- test dir/         # Run test blocks
```

## Where to Edit

| Task | Files |
|------|-------|
| **New keyword/token** | `frontend/lexer.rs`, `frontend/token.rs` |
| **New expression** | `frontend/parser/parse_expr.rs`, `frontend/ast.rs` |
| **New statement** | `frontend/parser/parse_stmt.rs`, `frontend/ast.rs` |
| **New operator** | lexer → parser → `sema/analyzer/expr.rs` → `codegen/compiler/ops.rs` |
| **Type checking** | `sema/analyzer/expr.rs`, `stmt.rs`, `patterns.rs` |
| **New error code** | `errors/sema.rs` or `errors/parser.rs` |
| **Expression codegen** | `codegen/compiler/patterns.rs` |
| **Function calls** | `codegen/compiler/calls.rs` |
| **Methods** | `codegen/compiler/methods.rs` |
| **Builtins** | `runtime/builtins.rs`, register in `codegen/compiler/calls.rs` |

## Testing

| Type | Location | Use For |
|------|----------|---------|
| **Unit tests** | `test/unit/` | Preferred. Code that compiles and runs. |
| **Snapshot/check** | `test/snapshot/check/` | Error messages (parse/type errors) |
| **Snapshot/run** | `test/snapshot/run/` | Simple smoke tests |

Unit test format: `tests { test "name" { assert(...) } }`

Bless snapshots: `cargo run --bin vole-snap -- bless path/`

## File Size

Target ~1000 lines, max 2000. **Prefer creating new files** over extending existing ones.

When splitting:
- Extract logical groupings into submodules (e.g., `analyzer/expr.rs`, `compiler/calls.rs`)
- Move tests to separate `tests.rs` files
- Use Rust's split `impl` pattern: same struct, methods in different files

Create new files when existing modules are too large or when functionality is logically separate.

## Language Syntax

```vole
func add(a: i64, b: i64) -> i64 {
    return a + b
}

tests {
    test "addition" {
        assert(add(2, 3) == 5)
    }
}
```

Types: `i32`, `i64`, `f64`, `bool`, `string`, `nil`, `T?` (optional)

See `docs/language/cheatsheet.md` for full reference. Update docs when changing language features.

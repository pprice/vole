# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Vole is a compiled programming language with JIT compilation via Cranelift. It features a complete compiler pipeline: lexer, parser, semantic analyzer (type checking), and code generator.

## Build Commands

The project uses `just` as a command runner. Key commands:

```bash
just build          # Debug build
just test           # Run Rust unit tests
just snap           # Run snapshot tests
just clippy         # Run lints
just fmt            # Format code
just ci             # Run all checks (mirrors CI)
```

Dev tools (for Claude Code):
```bash
just dev-next-error sema       # Next available error code (E2061, E1012, E0006)
just dev-trace-keyword raise   # Trace keyword through lexer→parser→sema→codegen
just dev-list-errors sema      # List all error codes with messages
just dev-test-for lambda       # Find test files related to a feature
just dev-void-ref src/sema/analyzer.rs  # Show equivalent Void (Zig) reference
just dev-todos                         # List TODOs and FIXMEs in codebase
just dev-tokens                        # List all token types
```

Run a single Rust test:
```bash
cargo test test_name
```

Run vole programs:
```bash
cargo run -- run path/to/file.vole    # Execute a vole program
cargo run -- check path/to/file.vole  # Type-check without running
cargo run -- test path/to/tests/      # Run vole test blocks
```

## Architecture

### Compiler Pipeline

Source code flows through these stages in order:

1. **frontend/** - Lexing and parsing
   - `lexer.rs` → tokenizes source into `Token`s with `Span`s
   - `parser.rs` → builds AST (`Program` containing `Decl`s)
   - `intern.rs` → string interning for identifiers (`Symbol`)
   - `ast.rs` → AST node definitions

2. **sema/** - Semantic analysis
   - `analyzer.rs` → type checking, scope resolution, produces `TypeError`s with structured diagnostics
   - `scope.rs` → lexical scoping for variables
   - `types.rs` → internal type representation (`Type`, `FunctionType`)

3. **codegen/** - Code generation
   - `compiler.rs` → translates typed AST to Cranelift IR
   - `jit.rs` → Cranelift JIT context management

4. **runtime/** - Runtime support
   - `assert.rs` → test assertion handling with setjmp/longjmp
   - `builtins.rs` → built-in functions (`print`, `println`, `assert`)
   - `string.rs` → reference-counted string type (`RcString`)

5. **errors/** - Diagnostic system
   - `codes.rs` → error codes (E0xxx lexer, E1xxx parser, E2xxx semantic)
   - `diagnostic.rs` → structured diagnostic building
   - `render.rs` → terminal output with colors

### Where to Edit

Common tasks mapped to files:

| Task | Files to Edit |
|------|---------------|
| **New keyword/token** | `frontend/lexer.rs` (add token), `frontend/token.rs` (Token enum) |
| **New syntax/expression** | `frontend/parser.rs` or `parse_expr.rs`, `frontend/ast.rs` (AST node) |
| **New statement** | `frontend/parse_stmt.rs`, `frontend/ast.rs` |
| **New declaration** | `frontend/parse_decl.rs`, `frontend/ast.rs` |
| **New type syntax** | `frontend/parse_type.rs` |
| **New operator** | `frontend/lexer.rs` → `frontend/parser.rs` → `sema/analyzer.rs` → `codegen/ops.rs` |
| **Type checking** | `sema/analyzer.rs` (main), `sema/types.rs` (type definitions) |
| **New semantic error** | `errors/sema.rs` (add variant), `sema/analyzer.rs` (emit it) |
| **New parser error** | `errors/parser.rs` |
| **Code generation** | `codegen/compiler.rs` (main), `codegen/expr.rs`, `codegen/stmt.rs` |
| **New builtin function** | `runtime/builtins.rs`, register in `codegen/compiler.rs` |
| **Classes/records codegen** | `codegen/structs.rs` |
| **Lambda codegen** | `codegen/lambda.rs` |

Test locations:

| Test Type | Location |
|-----------|----------|
| Language feature tests | `test/unit/language/<feature>.vole` |
| Type system tests | `test/unit/types/` |
| Error message snapshots | `test/snapshot/check/` |
| Smoke tests | `test/snapshot/run/` |

### Testing Infrastructure

Two testing systems:

1. **Unit tests** (`just unit`) - Vole files in `test/unit/` with `tests { }` blocks containing `test "name" { }` cases. Uses setjmp/longjmp for assertion failure recovery.

2. **Snapshot tests** (`just snap`) - Compares program output against `.snap` files. Located in `test/snapshot/`. Files prefixed with `_` are skipped by default.

**When to use which:**
- **Unit tests (`test/unit/`)**: Preferred for testing language features that compile and run correctly. Use assertions to verify behavior. Tests are organized by feature (e.g., `language/lambdas.vole`, `types/numeric_types.vole`).
- **Snapshot tests (`test/snapshot/`)**: Use for testing error messages (parse errors, type errors) in `check/` subdirectory, or for simple smoke tests in `run/`. Prefer unit tests over snapshot/run tests when the code compiles successfully.

Snapshot format:
```
[stdout]
expected stdout here

[stderr]
expected stderr here
```

Bless new/changed snapshots:
```bash
cargo run --bin vole-snap -- bless test/snapshot/
```

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

Lambdas: `(x: i64) => x * 2`, `() => { return 42 }` (with type inference from context)

Function types: `(i64) -> i64`, `(i64, i64) -> bool`, `() -> nil`

Supported: functions, let/let mut bindings, if/else, while, break, string interpolation (`"x is {x}"`), comparison and arithmetic operators, `&&` and `||`.

## Documentation

Language documentation lives in `docs/language/`. When adding or modifying language features:

1. **Update the relevant doc** - Each feature area has its own file (e.g., `types.md`, `functions.md`, `control-flow.md`)
2. **Update the cheatsheet** - `cheatsheet.md` is a single-page syntax reference
3. **Update the README** - `docs/language/README.md` has a feature status table showing what's implemented vs WIP

Key docs:
- `docs/language/README.md` - Index with feature status table
- `docs/language/cheatsheet.md` - Quick syntax reference
- `docs/language/*.md` - Detailed docs for each feature area

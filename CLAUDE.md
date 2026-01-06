# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Loading Private Instructions

Always check for `CLAUDE.local.md` which contains private instructions not checked into git.

**If in a git worktree**, find and load `CLAUDE.local.md` from the main repo:
```bash
git worktree list  # First entry is the main worktree
```
Then read `CLAUDE.local.md` from that path.

## Working Style

- **Bias toward action** - use tools to investigate instead of speculating
- **Be concise** - don't over-explain what you're about to do, just do it
- **Check before asking** - if you can answer a question with a tool, do that first
- **Use haiku for simple tasks** - spawn haiku agents for single-file edits, docs, mechanical changes, and simple commits

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
   - `parser/` → builds AST (`Program` containing `Decl`s)
   - `intern.rs` → string interning for identifiers (`Symbol`)
   - `ast.rs` → AST node definitions

2. **sema/** - Semantic analysis
   - `analyzer/` → type checking, scope resolution (split into modules)
     - `mod.rs` → main analyzer, declarations
     - `expr.rs` → expression type checking
     - `stmt.rs` → statement checking
     - `patterns.rs` → pattern matching
     - `lambda.rs` → lambda analysis
     - `methods.rs` → method/interface resolution
   - `scope.rs` → lexical scoping for variables
   - `types.rs` → internal type representation (`Type`, `FunctionType`)

3. **codegen/** - Code generation
   - `compiler/` → translates typed AST to Cranelift IR (split into modules)
     - `mod.rs` → main compiler, declarations
     - `patterns.rs` → pattern matching, `compile_expr`
     - `calls.rs` → function calls, builtins
     - `ops.rs` → binary/compound operations
     - `methods.rs` → method calls, try propagation
     - `fields.rs` → struct literals, field access
     - `strings.rs` → string interpolation
   - `expr.rs`, `stmt.rs` → Cg context methods
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
| **New syntax/expression** | `frontend/parser/parse_expr.rs`, `frontend/ast.rs` (AST node) |
| **New statement** | `frontend/parser/parse_stmt.rs`, `frontend/ast.rs` |
| **New declaration** | `frontend/parser/parse_decl.rs`, `frontend/ast.rs` |
| **New type syntax** | `frontend/parser/parse_type.rs` |
| **New operator** | `frontend/lexer.rs` → `frontend/parser/` → `sema/analyzer/` → `codegen/compiler/ops.rs` |
| **Type checking expressions** | `sema/analyzer/expr.rs` |
| **Type checking statements** | `sema/analyzer/stmt.rs` |
| **Type checking patterns** | `sema/analyzer/patterns.rs` |
| **New semantic error** | `errors/sema.rs` (add variant), `sema/analyzer/` (emit it) |
| **New parser error** | `errors/parser.rs` |
| **Expression codegen** | `codegen/compiler/patterns.rs` (compile_expr) |
| **Function call codegen** | `codegen/compiler/calls.rs` |
| **Binary/compound ops codegen** | `codegen/compiler/ops.rs` |
| **Method call codegen** | `codegen/compiler/methods.rs` |
| **Field/struct codegen** | `codegen/compiler/fields.rs` |
| **New builtin function** | `runtime/builtins.rs`, register in `codegen/compiler/calls.rs` |
| **Classes/records codegen** | `codegen/structs.rs` |
| **Lambda codegen** | `codegen/lambda.rs` |

Test locations:

| Test Type | Location |
|-----------|----------|
| Language feature tests | `test/unit/language/<feature>.vole` |
| Type system tests | `test/unit/types/` |
| Error message snapshots | `test/snapshot/check/` |
| Smoke tests | `test/snapshot/run/` |

### File Size Guidelines

Keep files manageable to maintain readability and ease of navigation:

- **Target:** ~1000 lines per file
- **Hard limit:** Never exceed 2000 lines
- **When to split:** If a file approaches 1500 lines, consider splitting by logical grouping

**Splitting strategy:**
- Extract tests into a separate `tests.rs` file using `#[cfg(test)] mod tests;`
- Group related functions into submodules (e.g., `analyzer/expr.rs`, `compiler/calls.rs`)
- Use Rust's split `impl` blocks pattern: same struct, methods in different files

**Creating new files is encouraged** when:
- Adding new functionality that doesn't fit existing modules
- A logical grouping of functions exceeds ~500 lines
- Tests for a module exceed ~300 lines

Example module structure:
```
sema/analyzer/
├── mod.rs      # Main struct, public API, declarations
├── expr.rs     # Expression checking methods
├── stmt.rs     # Statement checking methods
└── tests.rs    # All tests for the module
```

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

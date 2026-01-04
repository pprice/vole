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

### Testing Infrastructure

Two testing systems:

1. **Unit tests** (`vole test`) - Vole files with `tests { }` blocks containing `test "name" { }` cases. Uses setjmp/longjmp for assertion failure recovery.

2. **Snapshot tests** (`vole-snap`) - Compares program output against `.snap` files. Located in `test/snapshot/`. Files prefixed with `_` are skipped by default.

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

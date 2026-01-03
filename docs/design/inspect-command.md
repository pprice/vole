# Inspect Command Design

Date: 2026-01-02

## Overview

Add an `inspect` command to vole that dumps compilation artifacts for debugging and understanding. This mirrors void's `inspect` command.

## Command Interface

```
vole inspect <type> <file|glob>... [flags]

Types:
  ast    Show parsed AST
  ir     Show Cranelift CLIF IR

Options:
  -h, --help           Show help
      --no-tests       Exclude test blocks
      --imports <str>  Include imports: "project" or "all" (stub for now)

Examples:
  vole inspect ast hello.vole
  vole inspect ir src/*.vole
  vole inspect ast main.vole --no-tests
```

## Behavior

- Multiple files/globs supported
- Glob expansion (e.g., `src/*.vole`)
- `// path/to/file.vole` header printed to stderr for each file
- Files are deduplicated (same file not processed twice)
- Processing continues even if one file fails
- `--no-tests` excludes test blocks from output
- `--imports` follows imports and adds them to the queue (stub for now since vole doesn't have imports yet)

## AST Output

Custom display format with resolved symbols via `AstPrinter`:

```
// example.vole
Program
  FunctionDecl "add"
    params: [(a: i64), (b: i64)]
    return_type: i64
    body:
      Return
        BinaryOp Add
          Ident "a"
          Ident "b"
```

Features:
- Resolved symbol names in quotes (uses Interner)
- Clean indented tree structure
- `--no-tests` filtering built in

## IR Output

Cranelift CLIF IR via new `compile_to_ir` method:

```
// example.vole
// func add
function u0:0(i64, i64) -> i64 system_v {
block0(v0: i64, v1: i64):
    v2 = iadd v0, v1
    return v2
}

// func main
function u0:1() -> i64 system_v {
block0:
    v0 = call fn0(10, 32)
    return v0
}
```

The `compile_to_ir` method:
- Builds IR without finalizing for execution
- Takes a `Write` impl for output destination
- Respects `include_tests` parameter

## File Changes

| File | Changes |
|------|---------|
| `src/cli/args.rs` | Add `Inspect` variant with `inspect_type`, `files`, `no_tests`, `imports` |
| `src/commands/mod.rs` | Add `pub mod inspect;` |
| `src/commands/inspect.rs` | **New** - `inspect_files()` main entry point |
| `src/frontend/ast_display.rs` | **New** - `AstPrinter` with interner-aware formatting |
| `src/frontend/mod.rs` | Add `pub mod ast_display;` |
| `src/codegen/compiler.rs` | Add `compile_to_ir<W: Write>()` method |
| `src/bin/vole.rs` | Add match arm for `Commands::Inspect` |

## Dependencies

No new dependencies - `glob` crate already in Cargo.toml.

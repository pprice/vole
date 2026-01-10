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
just check       # Fast type checking (use after ANY code change)
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

## Verification Requirements

**ALWAYS run `just check` after ANY code change before claiming success.**

### Before Claiming Done
```bash
just check              # After any code change
just ci                 # After feature work
cargo run --bin vole -- test <path>  # After test changes
```

### Never Claim Success When
- `cargo check` shows errors
- Tests are failing
- Build warnings about unused/unresolved items

### Subagent Requirements
When dispatching subagents, they MUST run `cargo check` and verify exit code 0 before reporting success.

## Name Identity System

The compiler has two identifier systems:

| Type | Scope | Use |
|------|-------|-----|
| **Symbol** | AST layer only | Parser output, local variables |
| **NameId** | sema/codegen | Module-qualified canonical identity |

### Key Architecture

- **Symbol** (`frontend/intern.rs`): u32 index into a specific Interner. NOT stable across interners.
- **NameId** (`identity.rs`): u32 index into NameTable. Stores strings directly, self-contained.
- **NameTable**: Central registry for all named items (types, functions, methods). Stores strings internally.

### Type Structs Use NameId Only

```rust
// Type structs have name_id, NOT Symbol
pub struct RecordType {
    pub name_id: NameId,  // Canonical identifier
    pub fields: Vec<StructField>,
}
```

### Safe Patterns

```rust
// Display without needing interner
let display = name_table.display(some_type.name_id);

// Lookup using NameId (cross-module safe)
let method = methods.get(&(type_name_id, method_name_id));

// Record definition location for diagnostics
name_table.set_location(name_id, file, span);
```

### When Symbol Is Still Used

- **Parser output**: AST nodes use Symbol for names
- **Local variables**: Function-scoped names stay as Symbol
- **Within single interner**: Symbol comparisons are safe within same interner

### Diagnostic Locations

NameTable stores `DefLocation` for "defined here" error notes:
```rust
// Set when defining a name
name_table.set_location(name_id, &file, span);

// Retrieve for error messages
if let Some(loc) = name_table.location(name_id) {
    // Add "defined here" secondary label
}
```

## Common Pitfalls

### AST Changes Cascade
Changing AST types (`ast.rs`) requires updates in:
- Parser (`parse_*.rs`)
- Sema analyzer (`analyzer/*.rs`)
- Codegen (`codegen/*.rs`)
- Printer (`fmt/printer.rs`)
- Transforms (`transforms/*.rs`)

**Search ALL locations before making AST changes.**

### Type vs TypeExpr
- `Type` = sema layer resolved types
- `TypeExpr` = AST layer syntax types

Don't confuse them - they're in different compiler phases.

### Interface Boxing
Returning a record as an interface type requires boxing. Check:
- `box_interface_value` in codegen
- Vtable dispatch for method calls

### Generator Transform
Generators build AST directly, bypassing parser. Changes to parser syntax may not affect generators.
Location: `src/transforms/generator.rs`

## Refactoring Checklist

Before renaming a field, type, or function:

1. **Find all usages FIRST**
   ```bash
   grep -rn 'old_name' src/ --include='*.rs'
   ```

2. **Count usages** - know how many changes needed

3. **Fix ALL usages in one pass** - don't build until all are done

4. **Run `just check`** - verify before claiming success

### Common Refactors

| Change | Search Pattern |
|--------|---------------|
| Struct field | `grep -rn 'field_name' src/` |
| Enum variant | `grep -rn 'EnumName::Variant' src/` |
| Function | `grep -rn 'fn func_name\|func_name(' src/` |
| Type | `grep -rn 'TypeName' src/` |

## Debugging with vole inspect

Use `vole inspect` to see intermediate representations:

```bash
vole inspect ast file.vole       # Show parsed AST
vole inspect ir file.vole        # Show Cranelift IR
```

### When to Use
- **AST**: Parser bugs, transform issues, syntax questions
- **IR**: Codegen bugs, wrong output, type layout issues

## Debugging Segfaults

For crashes in JIT-compiled code:

```bash
just dev-debug-test file.vole    # Run test under lldb (interactive)
just dev-debug-run file.vole     # Run program under lldb (interactive)
just dev-backtrace-test file.vole  # Get backtrace non-interactively
just dev-disasm 0x12345          # Disassemble around crash address
```

### Signal Handler Context
The runtime installs a signal handler that prints context on SIGSEGV/SIGBUS:
```
SEGFAULT in test/unit/foo.vole :: test name here
```

This shows which file and test was running when the crash occurred.

### Debugging Workflow
1. Run failing test with `just dev-backtrace-test` to get crash location
2. Use `vole inspect ir` to see generated code
3. Use `just dev-disasm <addr>` to examine crash site
4. Check union tag/payload layout if crash is in type checks

## Tracing

Use `VOLE_LOG` to observe compiler behavior with structured tracing.

### Quick Start
```bash
just trace file.vole              # Pipeline phases with timing (compact)
just trace-verbose file.vole      # Detailed spans (sema, codegen calls)
just trace-full file.vole         # With ISO timestamps (human debugging)
just trace-module codegen file.vole  # Focus on specific module
just trace-test test/unit/        # Trace test execution
```

### Environment Variables
- `VOLE_LOG` - Filter (e.g., `vole=info`, `vole::codegen=debug`)
- `VOLE_LOG_STYLE=full` - ISO timestamps (default: compact, no timestamps)

### What You'll See
Pipeline phase spans with timing (compact format):
```
INFO parse{file=test.vole}: vole::commands::common: close time.busy=105µs time.idle=52µs
INFO transform: vole::commands::common: close time.busy=21µs time.idle=5µs
INFO sema: vole::commands::common: close time.busy=15.0ms time.idle=5µs
INFO codegen: vole::commands::run: close time.busy=2.05ms time.idle=15µs
INFO execute: vole::commands::run: close time.busy=11.9µs time.idle=9µs
```

### Filter Syntax
- `vole=info` - All vole spans at info level
- `vole::codegen=debug` - Codegen module only
- `vole::sema=trace` - Sema with maximum detail
- `vole=info,vole::codegen::calls=debug` - Combined filters

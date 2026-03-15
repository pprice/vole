# CLAUDE.md
Vole is a fast little scripting language, with fancy types

This project uses a CLI ticket system for task management. Run `tk help` when you need to use it.

## General Rules

<IMPORTANT>
  - Use tools to investigate (run tests, use debuggers, delta, fd, fzf, etc)
  - Use tools to modify where needed (e.g. ast-grep)
  - When planning work, do not write markdown files, use tickets with `tk`
  - NEVER "simplfy" tests in `vole/test`; you are hiding  bugs doing so
  - NEVER assume failures are "pre-existing", they are not.
  - NEVER opt out of work, simplify, for think tasks are too complex, _especially_ from tickets
  - NEVER add new `just` file commands unless the user asks you to
  - NEVER downgrade or close tickets unless the work is complete.
  - If you take shortcuts, track them in tickets with `tk`
</IMPORTANT>

## Project Rules

<IMPORTANT>
  - Parser: Syntax only.
  - Sema: All type-driven decisions. Annotates and normalizes.
  - VIR: Vole Intermedia Representation, lowering of sema before code gen.
  - Codegen: Instruction selection and memory layout only. Reads VIR, never re-detects types or
    inspects interface names.
  - Desugar early. when codegen needs type-specific behavior, add annotations/lowering in VIR
    or sema rather than type-detection special cases in codegen — codegen should read decisions, 
    not make them.
</IMPORTANT>


### Workspace Structure

```
src/
├── vole/            # CLI, commands, binaries
├── crates/
│   ├── vole-identity/   # NameId, NameTable, entity IDs
│   ├── vole-frontend/   # lexer, parser, AST, interner
│   ├── vole-sema/       # type checking, module loading
│   ├── vole-vir/        # Vole Intermediate Representation
│   ├── vole-runtime/    # builtins, values, instance
│   ├── vole-codegen/    # Cranelift JIT (isolated - heavy deps)
│   ├── vole-fmt/        # Code formatter
│   └── vole-log/        # Logging / tracing
└── tools/           # Development tools (vole-snap, vole-stress, vole-reduce, vole-leak, vole-doccheck)
```

## Tools

Just
```bash
just pre-commit     # Pre-commit checks with auto-fixes (format, clippy, test, snap, mem, doc-check)
just check          # Fast type check (run after ANY change)
just ci             # All CI checks (format, clippy, test, snap, mem-all, doc-check)
just unit           # Run vole unit tests (parallel across cores)
just snap           # Run snapshot tests
just mem            # Run memory leak tests
just dev            # List dev tools (debug, trace-keyword, next-error, etc.)
just agent          # Agent workflow tools (worktree, start-ticket, checklist, etc.)
just agent checklist VirExpr  # Show all files referencing an enum, classified by role
just trace run file.vole      # Tracing with VOLE_LOG
```

Cargo
```bash
cargo run -- run file.vole    # Execute
cargo run -- test dir/        # Run test blocks
```

Additional tools
```
ast-grep    # Use for large scale renames and finds with -l rust
tk          # Use for tracking work
rg          # Ripgrep
lldb        # Debugger
gdb         # Debugger
```

## Testing

| Type | Location | Use For |
|------|----------|---------|
| Unit tests | `test/unit/` | Preferred. Code that runs. |
| Snapshot/check | `test/snapshot/check/` | Error messages |
| Snapshot/run | `test/snapshot/run/` | Smoke tests |

Format: `tests { test "name" { assert(...) } }`
Bless: `cargo run --bin vole-snap -- bless path/`

NEVER "simplify" tests, even if you just created them.

## Debugging

```bash
vole inspect ast file.vole         # Show AST
vole inspect vir file.vole         # Show VIR
vole inspect mir file.vole         # Show MIR
vole inspect ir file.vole          # Show Cranelift IR
just dev backtrace-test file.vole  # Debug segfaults
just trace run file.vole           # Tracing with VOLE_LOG
vole --timing run file.vole        # Compiler phase timing (stderr)
vole --timing=chrome:out.json run file.vole  # Chrome trace JSON
```

For release-only issues, use `cargo build --profile release-local` which keeps symbols for debugging while maintaining release optimizations.

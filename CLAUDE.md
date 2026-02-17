# CLAUDE.md
Vole is a fast little scripting language, with fancy types

This project uses a CLI ticket system for task management. Run `tk help` when you need to use it.

## Rules

<IMPORTANT>
- Use tools to investigate (run tests, use debuggers)
- Use tools to modify where needed (e.g. ast-grep)
- When planning work, do not write markdown files, use tickets with `tk`
- NEVER "simplfy" tests in `vole/test`; you are hiding  bugs doing so
- NEVER assume "pre-existing failures", you likely broke it.
- NEVER opt out of work, simplify, for think tasks are too complex, _especially_ from tickets
- NEVER add new just file commands unless the user asks you to
- If you take shortcuts, track them in tickets with `tk`
</IMPORTANT>


### Workspace Structure

```
src/
├── vole/            # CLI, commands, binaries
├── crates/
│   ├── vole-identity/   # NameId, NameTable, entity IDs
│   ├── vole-frontend/   # lexer, parser, AST, interner
│   ├── vole-sema/       # type checking, module loading
│   ├── vole-runtime/    # builtins, values, instance
│   └── vole-codegen/    # Cranelift JIT (isolated - heavy deps)
└── tools/           # Development tools (vole-snap, vole-stress)
```

## Tools

Just
```bash
just pre-commit     # Pre-commit checks, like  CI,  but will format and attempt to fix clippy
just check          # Fast type check (run after ANY change)
just ci             # All checks (format, clippy, test, snap)
just unit           # Run vole unit tests
just snap           # Run snapshot tests
just dev            # List dev tools (see just/dev.justfile)
just agent          # List agent specific tools (e.g. work tree management)
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
vole inspect ir file.vole          # Show Cranelift IR
just dev-backtrace-test file.vole  # Debug segfaults
just trace file.vole               # Tracing with VOLE_LOG
```

For release-only issues, use `cargo build --profile release-local` which keeps symbols for debugging while maintaining release optimizations.

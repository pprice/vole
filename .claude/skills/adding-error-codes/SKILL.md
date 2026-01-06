---
name: adding-error-codes
description: Use when adding new diagnostic error codes to the compiler
---

# Adding Error Codes

## Overview

Vole uses structured error codes: E0xxx (lexer), E1xxx (parser), E2xxx (semantic).

## Checklist

1. **Get next available code**:
   ```bash
   just dev-next-error sema    # For semantic errors (E2xxx)
   just dev-next-error parser  # For parser errors (E1xxx)
   just dev-next-error lexer   # For lexer errors (E0xxx)
   ```

2. **List existing errors** (for reference):
   ```bash
   just dev-list-errors sema
   just dev-list-errors parser
   ```

3. **Add error variant** to the appropriate file:
   | Error Type | File |
   |------------|------|
   | Lexer | `src/errors/lexer.rs` |
   | Parser | `src/errors/parser.rs` |
   | Semantic | `src/errors/sema.rs` |

4. **Emit the error** in the relevant analyzer/parser code:
   | Error Type | Emission Location |
   |------------|-------------------|
   | Lexer | `src/frontend/lexer.rs` |
   | Parser | `src/frontend/parser/*.rs` |
   | Semantic (expr) | `src/sema/analyzer/expr.rs` |
   | Semantic (stmt) | `src/sema/analyzer/stmt.rs` |
   | Semantic (patterns) | `src/sema/analyzer/patterns.rs` |

5. **Add snapshot test** for error message:
   - Create `test/snapshot/check/your_error.vole` with code that triggers the error
   - Run `cargo run --bin vole-snap -- bless test/snapshot/check/your_error.vole`

6. **Verify**:
   ```bash
   just ci
   ```

## Error Code Format

```rust
// In errors/sema.rs (example)
E2061 => "cannot use `break` outside of a loop",
```

## Diagnostic Builder

Use the diagnostic builder for rich error messages:

```rust
self.error(SemaError::YourError)
    .span(span)
    .label(span, "explanation here")
    .emit();
```

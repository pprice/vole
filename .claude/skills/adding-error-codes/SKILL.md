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
   just dev next-error sema    # For semantic errors (E2xxx)
   just dev next-error parser  # For parser errors (E1xxx)
   just dev next-error lexer   # For lexer errors (E0xxx)
   ```

2. **List existing errors** (for reference):
   ```bash
   just dev list-errors sema
   just dev list-errors parser
   just dev list-errors all    # All categories
   ```

3. **Add error variant** to the appropriate file:
   | Error Type | File |
   |------------|------|
   | Lexer | `src/crates/vole-frontend/src/errors/lexer.rs` |
   | Parser | `src/crates/vole-frontend/src/errors/parser.rs` |
   | Semantic | `src/crates/vole-sema/src/errors/mod.rs` |

4. **Emit the error** in the relevant analyzer/parser code:
   | Error Type | Emission Location |
   |------------|-------------------|
   | Lexer | `src/crates/vole-frontend/src/lexer.rs` |
   | Parser | `src/crates/vole-frontend/src/parser/*.rs` |
   | Semantic | `src/crates/vole-sema/src/analyzer/**/*.rs` |

   Sema errors use `self.add_error(SemanticError::Variant { span }, span)`.

5. **Add snapshot test** for error message:
   - Create `test/snapshot/check/sema/your_error.vole` with code that triggers the error
   - Run `cargo run -p vole-snap -- bless test/snapshot/check/sema/your_error.vole`

6. **Verify**:
   ```bash
   just pre-commit
   ```

---
name: adding-syntax
description: Use when adding new syntax (expressions, statements, declarations) to the language
---

# Adding Syntax

## Overview

New syntax requires changes across the pipeline. The exact files depend on what you're adding.

## Useful Tools

```bash
just dev-trace-keyword <keyword>  # Trace existing keyword through pipeline
just dev-tokens                   # List all token types
just dev-void-ref <file>          # Check Void's implementation
just dev-test-for <feature>       # Find related test files
```

## Syntax Type Checklist

### New Expression

1. **AST node** - `src/frontend/ast.rs`
   - Add variant to `Expr` enum

2. **Parser** - `src/frontend/parser/parse_expr.rs`
   - Add parsing logic

3. **Type checker** - `src/sema/analyzer/expr.rs`
   - Add type checking in `check_expr`

4. **Codegen** - `src/codegen/compiler/patterns.rs`
   - Add to `compile_expr` match

### New Statement

1. **AST node** - `src/frontend/ast.rs`
   - Add variant to `Stmt` enum

2. **Parser** - `src/frontend/parser/parse_stmt.rs`
   - Add parsing logic

3. **Type checker** - `src/sema/analyzer/stmt.rs`
   - Add type checking in `check_stmt`

4. **Codegen** - `src/codegen/stmt.rs`
   - Add to `compile_stmt` match

### New Declaration

1. **AST node** - `src/frontend/ast.rs`
   - Add variant to `Decl` enum

2. **Parser** - `src/frontend/parser/parse_decl.rs`
   - Add parsing logic

3. **Type checker** - `src/sema/analyzer/mod.rs`
   - Add handling in declaration analysis

4. **Codegen** - `src/codegen/compiler/mod.rs`
   - Add to declaration compilation

### New Keyword

1. **Token** - `src/frontend/token.rs`
   - Add to `Token` enum

2. **Lexer** - `src/frontend/lexer.rs`
   - Add keyword recognition in `identifier_or_keyword`

3. **Then follow expression/statement/declaration steps above**

## Common Patterns

### Adding a keyword with block body (like `while`, `if`)

```rust
// Parser pattern
fn parse_your_stmt(&mut self) -> Result<Stmt> {
    self.expect(Token::YourKeyword)?;
    let condition = self.parse_expr()?;
    let body = self.parse_block()?;
    Ok(Stmt::YourStmt { condition, body })
}
```

### Checking Void reference

```bash
# See how Void implements a feature
just dev-void-ref src/frontend/parser/parse_stmt.rs
```

## Testing

1. **Unit test** - `test/unit/language/<feature>.vole`
   ```vole
   tests {
       test "feature works" {
           // test code
       }
   }
   ```

2. **Error snapshot** (if adding new errors) - `test/snapshot/check/`

## Verify

```bash
just ci
```

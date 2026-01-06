---
name: adding-operators
description: Use when adding new operators (binary, unary, compound assignment) to the language
---

# Adding Operators

## Overview

Operators flow through the full pipeline: lexer → parser → sema → codegen. Each stage must be updated.

## Useful Tools

```bash
just dev-tokens              # List all token types
just dev-trace-keyword <op>  # Trace an existing operator through the pipeline
just dev-void-ref src/codegen/compiler/ops.rs  # Check Void's implementation
```

## Checklist

### 1. Lexer - Add Token

**File:** `src/frontend/lexer.rs`

- Add token variant to the lexer's token recognition
- Handle in the appropriate match arm (single char, double char, etc.)

**File:** `src/frontend/token.rs`

- Add variant to `Token` enum

### 2. Parser - Parse the Operator

**File:** `src/frontend/parser/parse_expr.rs`

- For binary ops: add to precedence table and `parse_binary_expr`
- For unary ops: handle in `parse_unary_expr`
- For compound assignment (+=, etc.): handle in expression parsing

### 3. AST - Add Node (if needed)

**File:** `src/frontend/ast.rs`

- Add variant to `BinaryOp`, `UnaryOp`, or `CompoundOp` enum as appropriate

### 4. Semantic Analysis - Type Check

**File:** `src/sema/analyzer/expr.rs`

- Add type checking logic for the operator
- Ensure operand types are valid
- Determine result type

### 5. Code Generation - Emit IR

**File:** `src/codegen/compiler/ops.rs`

- Add Cranelift IR generation for the operator
- Handle different type combinations (i32, i64, f64, etc.)

### 6. Add Tests

**File:** `test/unit/language/operators.vole` or new file

```vole
tests {
    test "new operator" {
        assert(2 <op> 3 == expected)
    }
}
```

### 7. Verify

```bash
just ci
```

## Reference: Operator Precedence

Check `parse_expr.rs` for the precedence table. Lower number = higher precedence.

## Reference: Void Implementation

```bash
just dev-void-ref src/codegen/compiler/ops.rs
```

# VIR Expression Lowering - Incremental Migration Tickets

**Created**: February 23, 2026
**Status**: All tickets created and dependency-ordered
**Source**: EXPRESSION_LOWERING_AUDIT.md research

---

## Overview

Eight migration tickets have been created to incrementally lower all 34 ExprKind variants to VIR. The tickets are structured in phases with explicit dependencies, allowing parallel work while respecting architectural constraints.

**Ticket hierarchy** (dependencies flow downward):

```
vol-t936 (Phase 1: 5 expressions)
   ↓
vol-mzum (Phase 2a: LocalLoad/Store)
   ↓
vol-iuyx (Phase 2b: FieldLoad/Store)
   ↓
vol-3afx (Phase 2c: RC operations)
   ↓
vol-d83x (Phase 3: Call dispatch design)
   ↓
vol-b2sy (Phase 3b: Call/MethodCall lowering)
   ↓
vol-ppx4 (Phase 4a: Match)
vol-6ev0 (Phase 4b: Utilities) ─────┘
   ↓
vol-2jcs (Split lower.rs)
```

---

## Phase 0 (Complete ✅)

**Status**: Already implemented and codegen complete
**Expressions**: 10 variants (29% coverage)

Already lowered in current codebase:
- IntLiteral, FloatLiteral, BoolLiteral, StringLiteral
- Binary, Unary (Neg, Not, BitNot)
- If, Block, Yield
- Grouping (special-cased, stripped during lowering)

No tickets needed; these are the foundation for subsequent phases.

---

## Phase 1 (Ready to Start)

### Ticket: **vol-t936** — Lower ArrayLiteral, StructLiteral, IsCheck, AsCast, Lambda

**Priority**: 0 (highest)
**Status**: Ready (no dependencies)
**Effort**: 1-2 days, ~200-300 LOC

**Expressions to migrate** (5 total):
1. ArrayLiteral → VirExpr::ArrayLiteral { elements, elem_ty }
2. StructLiteral → VirExpr::StructLiteral { type_def, fields }
3. IsCheck → VirExpr::IsCheck { value, result: IsCheckResult, ty }
4. AsCast → VirExpr::AsCast { value, target_ty, kind: AsCastKind }
5. Lambda → VirExpr::Lambda { func_id, captures, ty }

**Why these work without new codegen**:
- VirExpr variants already defined
- Codegen implementations exist or have documented todo!() arms
- No new architectural pieces needed

**Lowering changes** (src/crates/vole-vir/src/lower.rs):
```rust
// In lower_expr() match arm expansion:
ExprKind::ArrayLiteral(elements) => {
    let elem_ty = node_map.get_array_elem_type(expr.id)?;
    let lowered_elements = elements
        .iter()
        .map(|e| lower_expr(e, node_map, interner))
        .collect();
    Box::new(VirExpr::ArrayLiteral {
        elements: lowered_elements,
        elem_ty,
    })
}
// Similar for StructLiteral, IsCheck, AsCast, Lambda
```

**Codegen changes** (src/crates/vole-codegen/src/expr/mod.rs):
Replace 5 `todo!()` arms in `compile_vir_expr()` by delegating to existing handlers:
```rust
VirExpr::ArrayLiteral { elements, elem_ty } => {
    self.compile_vir_array_literal(elements, *elem_ty)?
}
VirExpr::StructLiteral { type_def, fields } => {
    self.compile_vir_struct_literal(*type_def, fields)?
}
// etc. — delegate to existing struct_literal(), is_expr(), etc.
```

**Old codegen to delete**:
- None; existing codegen methods still used but via VIR nodes

**Validation**:
- `just pre-commit` passes
- Array and struct tests pass
- Type checking (is/as) tests pass
- Lambda tests pass
- Snapshot tests stable

**Impact**: Eliminates 5 Ast wraps (~21% reduction)

---

## Phase 2 (Medium Priority)

Phase 2 requires statement lowering infrastructure. Split into 3 focused tickets:

### 2a: **vol-mzum** — Lower LocalLoad and LocalStore (variable binding)

**Priority**: 0
**Status**: Awaiting vol-t936
**Effort**: 1-2 days, ~150 LOC

**Expressions to migrate**:
1. Identifier (local variables) → VirExpr::LocalLoad { name, ty }
2. Assign (local variable assignment) → VirExpr::LocalStore { name, value }

**Note**: Global identifier resolution (modules, functions) deferred to Phase 4. This phase handles **local variable access only**.

**Lowering strategy**:
```rust
ExprKind::Identifier(sym) => {
    // Query sema for binding information
    if is_local_variable(sym, &node_map) {
        Box::new(VirExpr::LocalLoad { name: sym, ty })
    } else {
        // Global resolution — wrap in Ast for now
        Box::new(VirExpr::Ast { expr: Box::new(expr.clone()), ty })
    }
}
```

**Codegen**:
```rust
VirExpr::LocalLoad { name, ty } => {
    if let Some((var, _)) = self.vars.get(name) {
        let val = self.builder.use_var(*var);
        Ok(CompiledValue::new(val, self.cranelift_type(*ty), *ty))
    } else {
        Err(CodegenError::not_found("variable", ...))
    }
}
```

**Enables**:
- Statement Let bindings (vol-mzum enables vol-stmtXX for Let, For, While)
- Clears path for Phase 2b (FieldLoad/Store)

**Impact**: Enables statement lowering, foundational for control flow

### 2b: **vol-iuyx** — Lower FieldLoad and FieldStore (field access)

**Priority**: 1
**Status**: Awaiting vol-mzum
**Effort**: 2 days, ~250 LOC

**Expressions to migrate**:
1. FieldAccess → VirExpr::FieldLoad { object, field, storage, ty }
2. Field assignment (Assign target) → VirExpr::FieldStore { object, field, storage, value }

**Lowering**:
- Extract FieldStorage (offset info) from sema
- Lower object and value expressions recursively
- Emit typed field load/store

**Codegen**:
- Use FieldStorage offset to emit load/store instructions
- Handle struct stack vs heap allocation
- RC management for field operations

**Enables**:
- Object mutation
- Struct field initialization in Let bindings

**Impact**: Unlocks struct/class field operations

### 2c: **vol-3afx** — Lower RcInc, RcDec, RcMove (reference counting)

**Priority**: 1
**Status**: Awaiting vol-iuyx
**Effort**: 1 day, ~100 LOC

**Expressions to migrate**:
1. RcInc → VirExpr::RcInc { value }
2. RcDec → VirExpr::RcDec { value }
3. RcMove → VirExpr::RcMove { value }

**Note**: Currently RC operations are inferred by codegen. This phase makes them explicit.

**Lowering**:
- If sema marks RC operations, lower them
- Otherwise, wrap in Ast (defer sema integration)

**Codegen**:
- RcInc: compile value, call runtime rc_inc
- RcDec: compile value, call runtime rc_dec, discard
- RcMove: compile value, no inc/dec

**Impact**: Clarifies RC semantics, unblocks RC ownership auditing

---

## Phase 3 (Architecture Design Required)

### 3 (Design): **vol-d83x** — Unified Call Dispatch Annotation

**Priority**: 0 (blocking Phase 3b)
**Status**: Awaiting vol-3afx
**Effort**: 2-3 days, design + implementation

**Problem**: Call expressions remain wrapped because sema has ~15 dispatch paths but no unified annotation.

**Solution**: Add CallDispatchKind enum to sema NodeMap

**Work items**:
1. Audit all 15 call dispatch paths in codegen (vir_calls.rs)
2. Design CallDispatchKind enum:
   ```rust
   pub enum CallDispatchKind {
       DirectFunction(FunctionId),
       BuiltinMethod(&'static str), // "Array::push", etc.
       ClosureCall,
       InterfaceMethod(TypeDefId),
       DefaultMethod(MethodId),
       StaticMethod(MethodId),
       Intrinsic(String),
       // ... more as needed
   }
   ```
3. Add to NodeMap: `set_call_dispatch(NodeId, CallDispatchKind)`
4. Update sema analyzer (methods/call_args.rs) to classify calls
5. Document dispatch decision process

**Impact**: Unblocks Call/MethodCall lowering

### 3b (Lowering): **vol-b2sy** — Lower Call and MethodCall

**Priority**: 1
**Status**: Awaiting vol-d83x
**Effort**: 2-3 days, ~200 LOC

**Expressions to migrate**:
1. Call → VirExpr::Call { target: CallTarget, args, ty }
2. MethodCall → VirExpr::Call { target: CallTarget::Method(...), ... }

**Lowering**:
```rust
ExprKind::Call(call_expr) => {
    let dispatch = node_map.get_call_dispatch(expr.id)?;
    let target = CallTarget::from_dispatch(dispatch);
    let args = call_expr.args.iter().map(|a| lower_expr(a, ...));
    Box::new(VirExpr::Call { target, args, ty })
}
```

**Codegen refactor** (vir_calls.rs:26+):
- Read CallTarget variant instead of re-detecting dispatch
- Each variant routes to appropriate handler
- Simpler, faster codegen

**Old codegen to delete**:
- Dispatch detection logic from call() method
- ~15 dispatch branches replaced with CallTarget match

**Impact**: Eliminates 2-3 major Ast wraps, simplifies codegen

---

## Phase 4 (Complex Lowering)

### 4a: **vol-ppx4** — Lower Match Expression

**Priority**: 2
**Status**: Awaiting vol-b2sy
**Effort**: 3-5 days, ~400+ LOC

**Expression**: Match → VirExpr::Match { scrutinee, arms, ty }

**New work**: VirPattern lowering
- Extend VirPattern enum with concrete variants
- Add pattern lowering pass (lower_pattern)
- Integrate pattern analysis

**Lowering**:
```rust
ExprKind::Match(match_expr) => {
    let scrutinee = lower_expr(&match_expr.scrutinee, ...);
    let arms = match_expr.arms.iter().map(|arm| {
        let pattern = lower_pattern(&arm.pattern);
        let guard = arm.guard.as_ref().map(|g| lower_expr(g, ...));
        let body = lower_arm_body(&arm.body, ...);
        VirMatchArm { pattern, guard, body, ty: ... }
    }).collect();
    Box::new(VirExpr::Match { scrutinee, arms, ty })
}
```

**Codegen**: Delegate to existing match_expr() for now

**Future**: Refactor match_expr to read from VirPattern

**Impact**: Eliminates 1 complex Ast wrap, foundations for patterns

### 4b: **vol-6ev0** — Lower Remaining Utilities

**Priority**: 2
**Status**: Awaiting vol-b2sy (can run parallel with 4a)
**Effort**: 1-2 days, ~150 LOC

**Expressions** (4 total):
1. Unreachable → VirExpr::Unreachable
2. Range → VirExpr::RangeLiteral { start, end, inclusive, ty } or desugar to Range constructor call
3. NullCoalesce → Desugar to If (value if not null, else default)
4. Index → Either new VirExpr::Index or desugar to array indexing method call

**Lowering strategy**:
- Unreachable: trivial
- Range: lower start/end, emit with flag
- NullCoalesce: desugar to If (similar to And/Or)
- Index: desugar to method call (Array[i] → array.index(i))

**Codegen**: Varies by variant

**Impact**: Clears expression clutter, ~4 Ast wraps

---

## Phase 5 (Polish)

### Refactoring: **vol-2jcs** — Split lower.rs into Modules

**Priority**: 3
**Status**: Awaiting vol-6ev0
**Effort**: 1 day, pure refactoring

**Current**: lower.rs is 534 lines

**Target structure**:
```
src/crates/vole-vir/src/
├── lower/
│   ├── mod.rs (public API + re-exports)
│   ├── expr.rs (300+ lines, expression lowering)
│   ├── stmt.rs (150+ lines, statement lowering)
│   └── pattern.rs (100+ lines, pattern lowering — added later)
└── lower.rs (deprecated, remove)
```

**Benefits**:
- Clearer separation of concerns
- Easier navigation during incremental work
- Supports parallel development
- Reduces cognitive load

**Validation**: Pure refactoring, `just pre-commit` passes

---

## Ticket Summary Table

| ID | Phase | Title | Effort | Deps | Status |
|----|-------|-------|--------|------|--------|
| vol-t936 | 1 | Lower 5 simple expressions | 1-2d | None | Ready |
| vol-mzum | 2a | Variable load/store | 1-2d | t936 | Ready after t936 |
| vol-iuyx | 2b | Field load/store | 2d | mzum | Ready after mzum |
| vol-3afx | 2c | RC operations | 1d | iuyx | Ready after iuyx |
| vol-d83x | 3 | Call dispatch design | 2-3d | 3afx | Ready after 3afx |
| vol-b2sy | 3b | Call/MethodCall lowering | 2-3d | d83x | Ready after d83x |
| vol-ppx4 | 4a | Match expression | 3-5d | b2sy | Ready after b2sy |
| vol-6ev0 | 4b | Utilities (Index, Range, etc.) | 1-2d | b2sy | Ready after b2sy |
| vol-2jcs | 5 | Split lower.rs | 1d | 6ev0 | Ready after 6ev0 |

**Total effort**: ~16-21 days of work, distributed across phases

---

## Next Steps

1. **Immediate**: Start vol-t936 (Phase 1) — no dependencies
2. **After vol-t936**: vol-mzum becomes ready (Phase 2a)
3. **Track progress**: `tk ready` shows which tickets are unblocked
4. **Validation**: Each ticket requires `just pre-commit` to pass
5. **Review criteria**:
   - All tests pass
   - No Ast-wrapped expression removed without codegen implementation
   - Compilation faster (fewer AST traversals, more structural info)

---

## Measurement

After all phases complete:
- **Expressions lowered**: 34/34 (100%)
- **Ast escape hatches eliminated**: 24/24 (all non-Phase-0 expressions)
- **VIR codegen implementations**: 24+ (from 14)
- **Codegen complexity**: Reduced (read decisions from VIR, don't re-analyze)
- **Per-phase time**: Can measure commit messages and ticket close dates

---

## Design Decisions

### Why these phases?

**Phase 1** (5 simple expressions) establishes the pattern:
- Lowering → VirExpr variant → codegen implementation
- No sema changes needed
- Quick wins to build momentum

**Phase 2** (variable/field/RC ops) enables statement lowering:
- Local variable access is foundational
- Field access enables object mutation
- RC operations clarify semantics

**Phase 3** (call dispatch) requires architectural work:
- Call dispatch is complex (15+ paths)
- Sema refactoring needed for CallDispatchKind
- Worth doing before Phase 4

**Phase 4** (complex expressions) leverages Phase 3:
- Match benefits from pattern infrastructure
- Utilities are independent (can run parallel with Match)

### Why depend on earlier phases?

- Phase 1 is independent (no sema changes)
- Phase 2a (variables) enables Phase 2b (fields) — fields use variable scopes
- Phase 2b enables Phase 2c (RC) — RC needs precise binding locations
- Phase 3 (design) must precede Phase 3b (implementation)
- Phase 4 benefits from Phase 3b (unified dispatch)

---

## Risk Mitigation

**Risk**: Phase 3 design doesn't match implementation needs
- **Mitigation**: vol-d83x is design-focused with acceptance criteria; community review before vol-b2sy

**Risk**: Codegen performance regresses
- **Mitigation**: Each ticket includes `just pre-commit` validation; VIR nodes carry more info, reducing codegen work

**Risk**: Lowering misses edge cases
- **Mitigation**: Comprehensive snapshot tests; memory leak checker catches RC issues

---

## Related Tickets

These tickets are prerequisites or closely related:
- vol-2es9: EPIC VIR transition (parent epic)
- vol-ddx3: Remove Ast escape hatch (Phase 5+)
- vol-dgm3: Insert explicit RcInc/RcDec (coordinated with 2c)

---

## Files Referenced

- `/home/phil/code/personal/vole/EXPRESSION_LOWERING_AUDIT.md` — detailed variant analysis
- `/home/phil/code/personal/vole/VIR_CODEGEN_TODO_ARMS.md` — codegen todo!() catalog
- `src/crates/vole-vir/src/lower.rs` — lowering pass (entry point)
- `src/crates/vole-vir/src/expr.rs` — VirExpr enum
- `src/crates/vole-codegen/src/expr/mod.rs` — compile_vir_expr router

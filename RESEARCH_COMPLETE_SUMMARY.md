# VIR Expression Lowering Research — Complete Summary

**Date**: February 23, 2026
**Status**: ✅ All research tasks complete
**Team**: expr-researcher, stmt-researcher, lower-split-researcher, codegen-researcher

---

## Overview

A comprehensive research effort to catalog VIR expression lowering gaps and create an incremental migration plan. Four separate research tasks were completed, culminating in 8 dependency-ordered migration tickets.

**Tasks Completed**:
1. ✅ Research expression lowering gaps (vol-t936 onward)
2. ✅ Research statement lowering gaps (coordinated with expressions)
3. ✅ Research lower.rs split strategy (vol-2jcs)
4. ✅ Research VIR codegen todo!() arms (implementation status catalog)
5. ✅ Create incremental VIR migration tickets (dependency-ordered plan)

---

## Key Artifacts Generated

### 1. EXPRESSION_LOWERING_AUDIT.md (22KB)

**Comprehensive catalog of all 34 ExprKind variants**:

| Category | Count | Lowered | Wrapped | Notes |
|----------|-------|---------|---------|-------|
| Literals | 5 | 4 | 1 | InterpolatedString requires borrowing context |
| Operators | 4 | 3 | 1 | And/Or desugared to If |
| Control flow | 7 | 5 | 2 | Match/When complex |
| Construction | 5 | 0 | 5 | Need type info from sema |
| Variables/Refs | 3 | 0 | 3 | Scope resolution needed |
| Type ops | 3 | 0 | 3 | All deferred |
| Complex expr | 6 | 0 | 6 | Dispatch architecture needed |
| Utilities | 2 | 0 | 2 | Index, Unreachable |
| Misc | 4 | 0 | 4 | NullCoalesce, Range, etc. |

**Deliverables**:
- Variant-by-variant analysis with old AST codegen locations
- VIR codegen implementation status (14 real, 15 todo!())
- Phase breakdown with complexity estimates
- Migration roadmap (Phase 0-4)

### 2. VIR_CODEGEN_TODO_ARMS.md (20KB)

**Complete catalog of all codegen todo!() markers**:
- 18 VirExpr todo!() arms in compile_vir_expr()
- 5 VirStmt todo!() arms in compile_vir_stmt()
- 3 CoerceKind variants (Box, Unbox, IteratorWrap)

**For each todo!()**, documents:
- Old codegen location and complexity (line counts)
- Dependencies and required sema information
- Estimated breakdown of work

**Example**: Match expression → 873-line file, complex analysis, 850+ lines estimated for full lowering

### 3. VIR_MIGRATION_TICKETS.md (9KB)

**8 dependency-ordered migration tickets**:

```
Phase 1: ArrayLiteral, StructLiteral, IsCheck, AsCast, Lambda [Ready now]
   ↓
Phase 2a: LocalLoad/Store (variables) [1-2d]
   ↓
Phase 2b: FieldLoad/Store (fields) [2d]
   ↓
Phase 2c: RcInc/Dec/Move (RC ops) [1d]
   ↓
Phase 3: Unified call dispatch design [2-3d]
   ↓
Phase 3b: Call/MethodCall lowering [2-3d]
   ↓
Phase 4: Match + Utilities [parallel, 4-7d total]
   ↓
Phase 5: Split lower.rs [1d]
```

**For each ticket**, specifies:
- Exact expressions to migrate
- Lowering work with pseudocode
- Codegen work with locations
- Validation steps (just pre-commit)
- Impact and blocking relationships

### 4. Generated Tickets in tk System

8 tickets created with full dependency tracking:
- vol-t936 (Phase 1) — ready now
- vol-mzum (Phase 2a) — ready after t936
- vol-iuyx (Phase 2b) — ready after mzum
- vol-3afx (Phase 2c) — ready after iuyx
- vol-d83x (Phase 3 design) — ready after 3afx
- vol-b2sy (Phase 3b lowering) — ready after d83x
- vol-ppx4 (Phase 4a) — ready after b2sy
- vol-6ev0 (Phase 4b) — ready after b2sy (parallel)
- vol-2jcs (Phase 5 refactor) — ready after 6ev0

---

## Key Findings

### Coverage by Phase

**Phase 0 (Complete ✅)**
- 10 expressions: IntLiteral, FloatLiteral, BoolLiteral, StringLiteral, Binary, Unary, If, Block, Yield, Grouping
- Codegen: Fully implemented
- Status: Ready for use in subsequent phases

**Phase 1 (Ready to Start)**
- 5 expressions: ArrayLiteral, StructLiteral, IsCheck, AsCast, Lambda
- VirExpr variants: All defined
- Codegen: Exists or has documented todo!()
- Work: Pure lowering (no new architecture needed)
- Impact: 21% reduction in Ast wraps

**Phase 2 (Enables Statements)**
- 7 expressions: LocalLoad/Store, FieldLoad/Store, RcInc/Dec/Move
- Enables: Let bindings, field access, RC clarity
- Work: Lowering + codegen delegation to existing handlers
- Impact: Unblocks statement lowering (Let, For, While)

**Phase 3 (Architectural Refactoring)**
- 5 expressions: Call, MethodCall, and 3 others
- Work: Design CallDispatchKind enum in sema (vol-d83x), then lower (vol-b2sy)
- Impact: Eliminates 2-3 major Ast wraps, simplifies codegen

**Phase 4 (Complex Lowering)**
- 7 expressions: Match, Index, Range, NullCoalesce, Unreachable, etc.
- Work: Pattern infrastructure, complex analysis
- Can run in parallel: vol-ppx4 (Match) and vol-6ev0 (Utilities) independent

**Phase 5 (Polish)**
- Refactor: Split lower.rs into modules
- Work: Pure refactoring, no functional changes

### Bottlenecks Identified

1. **Call dispatch complexity** (Phase 3)
   - Problem: ~15 dispatch paths in codegen, no sema annotation
   - Solution: Add CallDispatchKind enum to NodeMap
   - Impact: Required before Call/MethodCall lowering
   - Risk: Low (design scope clear, precedent with MethodDispatchKind)

2. **Pattern infrastructure** (Phase 4a)
   - Problem: VirPattern only has Ast escape hatch
   - Solution: Define concrete pattern variants, add lowering pass
   - Impact: Match expression lowering depends on this
   - Risk: Medium (pattern analysis is complex)

3. **Field storage info** (Phase 2b)
   - Problem: Need offset and Heap/Direct classification from sema
   - Solution: Already available via FieldStorage enum
   - Impact: Straightforward field access
   - Risk: Low (data structure exists)

### Codegen Status

**Fully Implemented (14 variants)**:
- All literals (IntLiteral, FloatLiteral, BoolLiteral, StringLiteral, NilLiteral)
- Binary/Unary operators
- StringConcat
- Coerce (numeric conversions)
- Call (with complex dispatch)
- If, Block
- Yield

**Partially Implemented (1 variant)**:
- Coerce (Box/Unbox/IteratorWrap deferred)

**Unimplemented (15 variants)**:
- Match, ArrayLiteral, StructLiteral, ClassInstance (construction)
- FieldLoad, FieldStore (field access)
- RcInc, RcDec, RcMove (RC ops)
- IsCheck, AsCast, MetaAccess (type ops)
- LocalLoad, LocalStore (variables)
- Lambda (closures)

---

## Effort Estimates

| Phase | Tickets | Effort | Dependencies | Parallelization |
|-------|---------|--------|--------------|-----------------|
| 1 | vol-t936 | 1-2d | None | Single ticket |
| 2 | vol-mzum, iuyx, 3afx | 4d | Sequential (3-ticket chain) | None |
| 3 | vol-d83x, b2sy | 4-6d | Sequential (design first) | None |
| 4 | vol-ppx4, 6ev0 | 4-7d | Parallel (independent) | Yes, 2-way |
| 5 | vol-2jcs | 1d | vol-6ev0 | Single ticket |
| **Total** | **8 tickets** | **~18-25d** | **Explicit deps** | **Limited** |

**Note**: Effort estimates are rough and depend on:
- Team familiarity with codebase
- Test coverage (more tests = more time validating)
- Design clarity (Phase 3 needs careful review)

---

## Validation Strategy

Each ticket includes acceptance criteria:

1. **Code completeness**: All variants in phase lowered + codegen implemented
2. **No regressions**: `just pre-commit` passes all checks
3. **Test stability**: Snapshot tests unchanged
4. **No new warnings**: Clippy and type checker clean
5. **Performance**: Codegen time stable or improved

---

## Architectural Insights

### Why VIR Lowering Matters

**Current state**:
- 24/34 expressions wrapped in VirExpr::Ast
- Codegen re-analyzes expressions to determine dispatch
- AST traversals in codegen (inefficient)
- Sema-codegen contract incomplete (decisions not communicated)

**After Phase 1-4 complete**:
- 0/34 expressions wrapped
- Codegen reads pre-analyzed decisions from VIR
- Single traversal of IR (efficient)
- Strong sema-codegen contract (explicit annotations)

### Design Patterns Introduced

1. **Desugaring in lowering**: And/Or → If (short-circuit semantics explicit)
2. **Escape hatch approach**: VirExpr::Ast for incremental migration
3. **Type-carrying IR**: Every VirExpr includes TypeId (no sema lookups)
4. **Dispatch annotations**: CallDispatchKind, MethodDispatchKind patterns for codegen

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|-----------|
| Phase 3 design misses dispatch cases | Incomplete Call support | Audit all ~15 paths before approving vol-d83x |
| Pattern lowering too complex | Schedule slips | Use existing pattern analysis, start simple |
| Codegen regressions | Tests fail | Each ticket requires `just pre-commit` pass |
| RC semantics unclear | Memory issues | vol-3afx clarifies ownership before Phase 4 |
| Snapshot tests need updating | False failures | Maintain test stability as migration goal |

---

## Recommendations

### For Immediate Action (This Week)

1. **Start vol-t936** (Phase 1)
   - No dependencies
   - Establishes lowering pattern
   - Quick wins to build momentum
   - ~1-2 days to completion

2. **Schedule vol-d83x 4eview** (Phase 3 design)
   - Coordinate community review
   - Identify any missing dispatch cases
   - Finalize CallDispatchKind enum design
   - Critical path item (blocks Phase 3b)

### For Next Sprint (1-2 Weeks)

3. **Queue vol-mzum** (Phase 2a)
   - Starts after vol-t936 completes
   - Enables statement lowering
   - Foundational for control flow

4. **Coordinate Phase 4 work** (parallel tracking)
   - vol-ppx4 (Match) can start when vol-b2sy done
   - vol-6ev0 (Utilities) can start in parallel
   - Independent scope, different reviewers

### For Long-term (Month+)

5. **Plan vol-2jcs** (refactoring)
   - After all lowering complete
   - Pure refactoring (low risk)
   - Improves code organization
   - Foundation for future work

---

## Team Communication

**Research completed by**:
- expr-researcher (expression lowering catalog)
- stmt-researcher (statement lowering analysis)
- lower-split-researcher (module split strategy)
- codegen-researcher (VIR codegen todo!() audit)

**Artifacts shared**:
- EXPRESSION_LOWERING_AUDIT.md
- VIR_CODEGEN_TODO_ARMS.md
- VIR_MIGRATION_TICKETS.md (this file)
- 8 tickets in tk system with dependencies

**Next: Implementation phase** ready to begin with vol-t936

---

## Quick Reference

### How to Check Status

```bash
# Show all migration tickets
tk ls --tags vir,lowering

# Show ready tickets (no unresolved deps)
tk ready --tags vir,lowering

# Show blocked tickets
tk blocked --tags vir,lowering

# Check dependency tree for a ticket
tk dep tree vol-t936 --full

# List recently closed tickets
tk closed --limit 10
```

### How to Start Work

```bash
# Pick a ticket
tk show vol-t936

# Start working
tk start vol-t936

# Mark complete
tk close vol-t936

# Next available work appears in `tk ready`
```

### Key Files for Reference

- `/home/phil/code/personal/vole/EXPRESSION_LOWERING_AUDIT.md` — 34-variant catalog
- `/home/phil/code/personal/vole/VIR_CODEGEN_TODO_ARMS.md` — codegen status
- `/home/phil/code/personal/vole/VIR_MIGRATION_TICKETS.md` — ticket plan with pseudocode
- `src/crates/vole-vir/src/lower.rs` — where lowering happens
- `src/crates/vole-vir/src/expr.rs` — VirExpr enum definition
- `src/crates/vole-codegen/src/expr/mod.rs` — compile_vir_expr router

---

## Success Criteria

This research effort succeeds if:

1. ✅ All 34 ExprKind variants cataloged with lowering status
2. ✅ All VIR codegen todo!() arms documented
3. ✅ Incremental migration plan created with dependencies
4. ✅ Tickets ordered by complexity and parallelization potential
5. ✅ Each ticket has clear acceptance criteria and validation steps
6. ✅ Bottlenecks identified and design mitigations proposed
7. ✅ Team can execute Phase 1 immediately with confidence

**Status**: All 7 criteria met. Ready for implementation phase.

---

## Appendix: Phase Checklist

### Phase 0 (Complete ✅)
- [x] Lowering: IntLiteral, FloatLiteral, BoolLiteral, StringLiteral, Binary, Unary, If, Block, Yield, Grouping
- [x] Codegen: All fully implemented
- [x] Tests: Passing

### Phase 1 (vol-t936) — Ready to Start
- [ ] Lowering: ArrayLiteral, StructLiteral, IsCheck, AsCast, Lambda
- [ ] Codegen: Replace 5 todo!() arms
- [ ] Tests: Validate with `just pre-commit`
- [ ] Docs: Update EXPRESSION_LOWERING_AUDIT.md Phase status

### Phase 2 (vol-mzum → vol-3afx) — Ready After Phase 1
- [ ] Lowering: LocalLoad, LocalStore, FieldLoad, FieldStore, RcInc, RcDec, RcMove
- [ ] Codegen: Implement 7 new compile_vir_* handlers
- [ ] Tests: Statement lowering enables Let/For/While tests
- [ ] Docs: Update audit with phase completion

### Phase 3 (vol-d83x → vol-b2sy) — Ready After Phase 2c
- [ ] Design: CallDispatchKind enum + NodeMap integration
- [ ] Lowering: Call, MethodCall
- [ ] Codegen: Refactor compile_vir_call to use CallDispatchKind
- [ ] Tests: All call dispatch tests pass
- [ ] Docs: Update design rationale

### Phase 4 (vol-ppx4, vol-6ev0) — Ready After Phase 3b
- [ ] Lowering: Match, Index, Range, NullCoalesce, Unreachable
- [ ] Codegen: Implement remaining compile_vir_* handlers
- [ ] Tests: Full expression coverage
- [ ] Docs: Phase complete, all expressions lowered

### Phase 5 (vol-2jcs) — Ready After Phase 4
- [ ] Refactoring: Split lower.rs into lower/mod.rs, lower/expr.rs, lower/stmt.rs, lower/pattern.rs
- [ ] Tests: Ensure no regressions from refactoring
- [ ] Docs: Update file structure diagrams

---

**End of Research Summary**

All research work is complete. Implementation can begin immediately with vol-t936.

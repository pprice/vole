# VIR Expression Lowering Research — Complete Index

**Date**: February 23, 2026
**Status**: ✅ All research complete
**Total documentation**: ~2000 lines across 4 files

---

## Quick Start

**For project leads**: Start with `RESEARCH_COMPLETE_SUMMARY.md`
- Overview of all findings
- Effort estimates and risk mitigation
- Recommended next steps

**For implementers**: Use `VIR_MIGRATION_TICKETS.md` as the execution plan
- 9 tickets ready in `tk` system
- Each with exact scope, dependencies, pseudocode
- Acceptance criteria for each phase

**For detailed analysis**: See individual audit documents
- `EXPRESSION_LOWERING_AUDIT.md` — variant-by-variant catalog
- `VIR_CODEGEN_TODO_ARMS.md` — codegen status and complexity

---

## Document Catalog

### 1. EXPRESSION_LOWERING_AUDIT.md
**Type**: Detailed research audit
**Size**: 461 lines (22KB)
**Audience**: Implementers, architects

**Contents**:
- All 34 ExprKind variants analyzed
- Current lowering status (10 lowered, 24 wrapped in Ast)
- VIR codegen implementation status (14 real, 15 todo!())
- Old AST codegen locations with line counts
- 5-phase migration roadmap with complexity tiers

**Key tables**:
- "Lowering Coverage Matrix" — phases 0-3 with coverage percentages
- "Summary Table: All 34 ExprKind Variants" — complete status reference
- "Migration Roadmap Priority" — effort estimates by phase

**Use case**: Understanding current state, planning which variants to tackle

---

### 2. VIR_CODEGEN_TODO_ARMS.md
**Type**: Implementation catalog
**Size**: 647 lines (20KB)
**Audience**: Implementers, codegen specialists

**Contents**:
- All 24 `todo!()` markers in VIR codegen (18 expr, 5 stmt, 3 CoerceKind)
- For each: old codegen location, complexity, dependencies
- Line count estimates (250-850+ LOC per major item)
- Implementation breakdown suggestions

**Key information**:
- Match (873-line old implementation) → 850+ LOC estimated
- StructLiteral (803-line old file) → 500+ LOC for field handling
- Call dispatch (15+ paths) → needs sema refactoring

**Use case**: Understanding implementation effort, planning resource allocation

---

### 3. VIR_MIGRATION_TICKETS.md
**Type**: Execution plan
**Size**: 472 lines (15KB)
**Audience**: Team leads, implementers

**Contents**:
- 8 dependency-ordered migration tickets (vol-t936 through vol-2jcs)
- For each ticket: expressions to migrate, lowering pseudocode, codegen changes
- Validation steps and impact analysis
- Dependency graph visualization

**Ticket structure** (all created in `tk` system):
1. vol-t936 (Phase 1) — ArrayLiteral, StructLiteral, IsCheck, AsCast, Lambda
2. vol-mzum (Phase 2a) — LocalLoad/Store (variables)
3. vol-iuyx (Phase 2b) — FieldLoad/Store (fields)
4. vol-3afx (Phase 2c) — RcInc/Dec/Move (RC ops)
5. vol-d83x (Phase 3 design) — CallDispatchKind in sema
6. vol-b2sy (Phase 3b) — Call/MethodCall lowering
7. vol-ppx4 (Phase 4a) — Match expression
8. vol-6ev0 (Phase 4b) — Utilities (Index, Range, NullCoalesce, Unreachable)
9. vol-2jcs (Phase 5) — Split lower.rs into modules

**Use case**: Day-to-day execution, understanding exactly what code needs to change

---

### 4. RESEARCH_COMPLETE_SUMMARY.md
**Type**: Executive summary
**Size**: 411 lines (14KB)
**Audience**: Project leads, team leads, stakeholders

**Contents**:
- Overview of all 4 research tasks
- Key findings and insights
- Architectural patterns introduced
- Effort breakdown by phase (total: 18-25 days)
- Risk mitigation strategies
- Success criteria

**Key sections**:
- "Coverage by Phase" — progression from 10/34 to 34/34 expressions
- "Bottlenecks Identified" — 3 architectural challenges with solutions
- "Effort Estimates" — 1-2d Phase 1, 4d Phase 2, 4-6d Phase 3, etc.
- "Team Communication" — who did what research
- "Quick Reference" — commands for tracking progress

**Use case**: Understanding high-level strategy, making go/no-go decisions

---

## How to Use These Documents

### For Initial Review (15 minutes)
1. Read RESEARCH_COMPLETE_SUMMARY.md (Executive Summary section)
2. Review effort estimates and timeline
3. Check recommended next steps

### For Implementation Planning (30 minutes)
1. Read VIR_MIGRATION_TICKETS.md (Ticket Summary Table)
2. Check dependencies: `tk dep tree vol-t936 --full`
3. Review phase breakdown with effort estimates
4. Identify potential parallelization (Phase 4)

### For Detailed Technical Work (varies)
1. Read EXPRESSION_LOWERING_AUDIT.md for specific variants
2. Cross-reference VIR_CODEGEN_TODO_ARMS.md for codegen complexity
3. Use VIR_MIGRATION_TICKETS.md pseudocode during implementation
4. Check old codegen locations from audit for reference implementations

### For Architecture Decisions
1. Focus on Phase 3 design (vol-d83x) in VIR_MIGRATION_TICKETS.md
2. Review "CallDispatchKind" discussion
3. Understand why design is required before lowering
4. Plan for community review before vol-b2sy approval

---

## Key Metrics

### Coverage
- **Current state (Phase 0)**: 10/34 expressions lowered (29%)
- **After Phase 1**: 15/34 (44%)
- **After Phase 2**: 22/34 (65%)
- **After Phase 3**: 27/34 (79%)
- **After Phase 4**: 34/34 (100%)

### Codegen Status
- **Fully implemented**: 14 VirExpr variants
- **Partially implemented**: 1 (Coerce — needs Box/Unbox/IteratorWrap)
- **Unimplemented (todo!)**: 15 (18 expr, 5 stmt, 3 CoerceKind)

### Effort
| Phase | Effort | Dependencies | Parallelization |
|-------|--------|--------------|-----------------|
| 1 | 1-2d | None | Single ticket |
| 2 | 4d | Sequential chain (3 tickets) | None |
| 3 | 4-6d | Sequential (design then impl) | None |
| 4 | 4-7d | After Phase 3b | 2-way parallel |
| 5 | 1d | After Phase 4 | Single ticket |
| **Total** | **~18-25d** | **Explicit** | **Limited** |

### Risk Factors
| Item | Severity | Mitigation |
|------|----------|-----------|
| Phase 3 design incomplete | High | Community review before vol-b2sy |
| Pattern infrastructure complexity | Medium | Leverage existing analysis |
| Codegen regressions | Low | `just pre-commit` validation per ticket |
| RC semantics clarity | Low | vol-3afx clarifies before Phase 4 |

---

## Files in VCS

All artifacts are committed to the repository:

```
/home/phil/code/personal/vole/
├── EXPRESSION_LOWERING_AUDIT.md      (22KB, 461 lines)
├── VIR_CODEGEN_TODO_ARMS.md          (20KB, 647 lines)
├── VIR_MIGRATION_TICKETS.md          (15KB, 472 lines)
├── RESEARCH_COMPLETE_SUMMARY.md      (14KB, 411 lines)
└── RESEARCH_INDEX.md                 (this file)
```

Plus 9 tickets in `.tickets/` directory:
- vol-t936.md, vol-mzum.md, vol-iuyx.md, vol-3afx.md
- vol-d83x.md, vol-b2sy.md, vol-ppx4.md, vol-6ev0.md, vol-2jcs.md

---

## Related Artifacts

### In codebase:
- `src/crates/vole-vir/src/lower.rs` — where lowering happens
- `src/crates/vole-vir/src/expr.rs` — VirExpr enum definition
- `src/crates/vole-vir/src/stmt.rs` — VirStmt enum definition
- `src/crates/vole-codegen/src/expr/mod.rs` — compile_vir_expr router
- `src/crates/vole-codegen/src/expr/control_flow.rs` — VIR if/block handlers
- `src/crates/vole-codegen/src/expr/vir_calls.rs` — VIR call dispatcher

### Commands:
```bash
# View all migration tickets
tk list --tags vir,lowering

# Show ready tickets (no unresolved deps)
tk ready --tags vir,lowering

# Show blocked tickets
tk blocked --tags vir,lowering

# Check dependency tree
tk dep tree vol-t936 --full

# List recently closed tickets
tk closed --limit 10 --tags vir,lowering
```

---

## Research Team

| Role | Researcher | Focus |
|------|-----------|-------|
| **Expression Lowering** | expr-researcher | 34-variant catalog, phase breakdown |
| **Statement Analysis** | stmt-researcher | Statement lowering dependencies |
| **Architecture** | lower-split-researcher | Module organization strategy |
| **Codegen** | codegen-researcher | Todo!() arms catalog, effort estimates |

All research integrated into unified migration plan with explicit dependencies.

---

## Next Steps (Recommended)

### This Week
1. ✅ **Review vol-t936 (Phase 1)**
   - Ready to implement immediately
   - 5 simple expressions, 1-2 days
   - Establishes pattern for subsequent phases

2. ✅ **Schedule vol-d83x (Phase 3 design) review**
   - Critical for Phase 3b unblocking
   - Design is clear, needs community input
   - Consider in parallel with Phase 2

### Next 1-2 Weeks
3. **Execute Phase 1** (vol-t936)
   - Quick wins build momentum
   - Phase 2a (vol-mzum) becomes ready after

4. **Design review completion** (vol-d83x)
   - Finalize CallDispatchKind enum
   - Document dispatch decision process
   - Clear vol-b2sy for implementation

### Following Sprint
5. **Parallel work possible**
   - Phase 2 (sequential chain): vol-mzum → vol-iuyx → vol-3afx
   - Phase 4 (parallel): vol-ppx4 and vol-6ev0 independent
   - Estimate calendar reduction with 2-3 person team

---

## Success Criteria

Research is successful if:
1. ✅ All 34 ExprKind variants cataloged
2. ✅ Lowering status clear for each
3. ✅ VIR codegen todo!() arms documented
4. ✅ Incremental migration plan with dependencies
5. ✅ Effort estimates realistic and bounded
6. ✅ Team can start Phase 1 immediately
7. ✅ Bottlenecks identified and mitigated

**Status**: All 7 criteria met ✅

---

## Document Navigation

- **First-time readers**: Start with RESEARCH_COMPLETE_SUMMARY.md
- **Technical leads**: VIR_MIGRATION_TICKETS.md for execution
- **Architects**: EXPRESSION_LOWERING_AUDIT.md + VIR_CODEGEN_TODO_ARMS.md
- **Managers**: This index + RESEARCH_COMPLETE_SUMMARY.md for timeline
- **Implementers**: VIR_MIGRATION_TICKETS.md + specific ticket details

---

**Research Completed**: February 23, 2026
**Ready for Implementation**: Yes
**Recommended Start**: vol-t936 (Phase 1)

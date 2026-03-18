# Codegen Arena Usage Audit
**Date**: 2026-02-27
**Scope**: `src/crates/vole-codegen/src/` — all 33 files with arena() calls
**Status**: READ-ONLY research completed

## Executive Summary

**Total arena() call sites**: ~150+ across codegen
**Files affected**: 33 files

**Distribution**:
- **Category 1** (VIR fallback wrapper): ~32 calls — ✓ IDEAL PATTERN
- **Category 2** (not yet enriched): ~60+ calls — ⚠️ CANDIDATES FOR ENRICHMENT
- **Category 3** (legitimate deep queries): ~40+ calls — ✓ OK AS-IS

---

## Category 1: VIR Fallback Wrappers — IDEAL PATTERN

**Status**: Already handled by hybrid VIR+Arena design
**Files**: `context.rs` (32 calls), `rc_state.rs` (13 calls secondary)

### Pattern in context.rs (14 wrapper methods)

All type-classification decisions routed through `vir_query_*` helpers:

```rust
pub fn vir_query_is_struct(&self, type_id: TypeId) -> bool {
    let vir_ty = self.vir_lookup(type_id);
    if vir_ty == VirTypeId::UNKNOWN {
        self.arena().is_struct(type_id)  // Fallback for monomorphs
    } else {
        crate::types::vir_conversions::vir_is_struct(vir_ty, self.vir_type_table())
    }
}
```

**14 wrapper methods**:
1. `vir_query_is_struct()` — line 383-390
2. `vir_query_is_union()` — line 395-402
3. `vir_query_is_unknown()` — line 407-414
4. `vir_query_is_payload_union()` — line 419-426
5. `vir_query_is_void()` — line 431-438
6. `vir_query_is_fallible()` — line 443-450
7. `vir_query_is_wide_fallible()` — line 455-462
8. `vir_query_is_wide()` — line 467-474
9. `vir_query_is_interface()` — line 479-486
10. `vir_query_unwrap_nominal()` — line 491-498
11. `vir_query_display_basic()` — line 503-510
12. `vir_query_field_byte_size()` — line 515-522
13. `vir_query_unknown_type_tag()` — line 527-530
14. `vir_query_type_to_cranelift()` — line 541-545

**Assessment**: ✓ GOOD
- Wrapped API provides clean fallback semantics
- Only falls back when `VirTypeId::UNKNOWN` (expected for non-VIR-lowered monomorphs)
- Transparent to callers — they don't know if result came from VIR or arena
- Safe and contained within `context.rs`

---

## Category 2: NOT YET ENRICHED — TYPE-DECISION GAPS

**Status**: These should have VIR annotations but currently re-detect types

### expr/mod.rs — 15 direct arena() calls

**High-impact sites**:

| Line | Call | Context | Enrichment Need |
|------|------|---------|-----------------|
| 131 | `arena().is_function()` | Check if export constant is function | Add `vir_is_function()` helper |
| 137 | `arena().is_sentinel()` | Check if export is sentinel | Add `vir_is_sentinel()` helper |
| 990 | `arena().is_sentinel()` | Literal defaulting | Need sentinel literal VIR node |
| 1071-1083 | `arena().unwrap_union()`, `is_integer()` | Union narrowing in pattern match | Annotate union variants in VIR |
| 1114 | `arena().is_function()` | Function reference | Need `vir_is_function()` helper |
| 1381 | `arena().unwrap_union()` | Union tag matching in is-check | Annotate union in VIR IsCheck |

**Effort to fix**:
- Lines 131, 137, 1114: **LOW** (add 2-3 helper methods)
- Lines 990, 1071-1083, 1381: **MEDIUM-HIGH** (needs sema enrichment)

---

### stmt.rs — 27 direct arena() calls

**High-impact sites**:

| Line | Call | Context | Enrichment Need |
|------|------|---------|-----------------|
| 89 | `is_interface()`, `is_iterator_interface()` | Let interface hint | Annotate Let node with LetStorageHint |
| 92, 136, 168-172 | `is_sentinel()` | Sentinel union detection | Add `vir_is_sentinel()` helper |
| 143-144 | `is_integer()` | Integer type widening | Annotate result type in VIR |
| 305-376 | `is_sentinel()` in union construction loop | Union field tag assignment | Annotate union variants in VIR |
| 578 | `is_function()` | Check function return type | Use VIR return type metadata |

**Sentinel detection** is the most frequent problem (6+ sites):
- Currently: `arena.is_sentinel(type_id)` check
- Solution: Add `vir_is_sentinel()` helper following context.rs pattern

**Effort to fix**:
- Sentinel checks: **LOW** (add 1 helper, replace 6 sites)
- Union construction: **MEDIUM** (sema enrichment needed)
- Interface hints: **MEDIUM** (requires Let metadata)

---

### value_builders.rs — 5 calls (mixed category)

**Assessment**:
- Lines 731, 753: `unwrap_struct()` — ✓ LEGITIMATE (field metadata lookup)
- Lines 1049, 1076: `is_struct()` — Can use `vir_query_is_struct()`
- Line 1326: `WideType::from_type_id()` — ✓ LEGITIMATE (wide type helper)

**Effort**: LOW (replace 2 calls with vir_query_* wrappers)

---

### coercion_ops.rs — 6 calls

**Assessment**:
- Lines 1049, 1076: `is_struct()` — Replace with `vir_query_is_struct()`
- Lines 1129, 1161-1167: `is_union()` — Replace with `vir_query_is_union()`
- Lines 1132-1133: `display_basic()` in error messages — ✓ OK to keep

**Effort**: LOW (replace 4 calls with vir_query_* wrappers)

---

### other/mod.rs files — intrinsic_compiler, compiler/impl_monomorph, etc.

**Assessment**:
- `compiler/impl_monomorph.rs`: 12 calls — ✓ LEGITIMATE (registration phase metaprogramming)
- `intrinsic_compiler/mod.rs`: 9 calls — Need to verify these aren't type decisions
- Other compiler files: Likely legitimate metaprogramming (registration, type registry lookups)

**Effort**: MEDIUM (audit each site individually)

---

## Category 3: LEGITIMATE DEEP STRUCTURAL QUERIES

**Status**: OK as-is. These require deep type inspection and may always need arena access.

### Core modules (pure structural analysis)

| Module | Calls | Purpose | Can Migrate? |
|--------|-------|---------|-------------|
| `rc_state.rs` | 13 | RC cleanup offset computation | Phase 2+ (low priority) |
| `types/conversions.rs` | 8 | Type size, layout calculations | Phase 3+ (maybe) |
| `types/vir_conversions.rs` | 8 | Bridge between sema and VIR types | Yes, but low priority |
| `structs/helpers.rs` | 2 | Struct field access, layout | Yes, structural |
| `interfaces/vtable.rs` | 1 | VTable construction | ✓ LEGITIMATE metaprogramming |
| `generator.rs` | 1 | Type generation helpers | ✓ LIKELY LEGITIMATE |

**Assessment**: ✓ GOOD
- These inspect deep structure (union variants, field offsets, RC types)
- Results are cached (e.g., `rc_state(type_id)`)
- Could migrate to VIR in later phases but not blocking

---

## Summary by Enrichment Effort

### Phase 1 (Week 1-2): Quick Wins
- [ ] Add `vir_is_function()` helper to `context.rs`
- [ ] Add `vir_is_sentinel()` helper to `context.rs`
- [ ] Replace 8-10 direct calls with wrappers in `expr/mod.rs`, `stmt.rs`, `coercion_ops.rs`
- **Effort**: 1-2 days
- **Impact**: Eliminates obvious type-classification re-detections

### Phase 2 (Week 3-4): Union Metadata
- [ ] Enrich VIR `UnionLiteral` with variant list from sema
- [ ] Enrich VIR `LetTuple` with union variant info
- [ ] Migrate `stmt.rs` union construction (lines 305-376) to VIR metadata
- [ ] Migrate `expr/mod.rs` union narrowing (lines 1071-1083) to VIR metadata
- **Effort**: 4-5 days
- **Impact**: Eliminates union structure re-inspection in core codegen paths

### Phase 3 (Week 5-6): Type Layout Helpers
- [ ] Audit `types/conversions.rs` for VIR-table compatibility
- [ ] Consider lazy VIR enrichment for `is_wide`, `is_fallible`, etc.
- [ ] Verify `rc_state.rs` caching is adequate
- **Effort**: 3-4 days
- **Impact**: Better separation of concerns, cleaner code

### Phase 4 (After VIR >80%): Full Migration
- [ ] Re-audit with complete VIR lowering
- [ ] Remove fallback path from context.rs wrappers (if VIR 100%)
- [ ] Measure codegen performance (VIR-only vs hybrid)
- **Effort**: 2-3 days
- **Impact**: Cleaner architecture, potential performance improvements

---

## Category Breakdown Table

```
FILE                                CALLS   CATEGORY   STATUS
────────────────────────────────────────────────────────────────
context.rs                            32      1         ✓ GOOD
rc_state.rs                           13      3         ✓ OK
type_ops.rs                           16      3         ✓ OK
types/conversions.rs                   8      3         ✓ OK
types/vir_conversions.rs               8      3         ✓ OK
compiler/impl_monomorph.rs            12      3         ✓ OK (registration)
intrinsic_compiler/mod.rs              9      ?         AUDIT
expr/mod.rs                           15      2         ⚠️ NEEDS ENRICHMENT
stmt.rs                               27      2         ⚠️ NEEDS ENRICHMENT
value_builders.rs                      5      2         ⚠️ PARTIAL (2 sites)
coercion_ops.rs                        6      2         ⚠️ PARTIAL (4 sites)
structs/helpers.rs                     2      3         ✓ OK
structs/*.rs (other)                  ~8      3         ✓ OK
calls/*.rs                             4      ?         AUDIT
expr/field_ops.rs, etc.               ~8      2         AUDIT
────────────────────────────────────────────────────────────────
TOTAL:                              ~150
  Category 1:                         ~32     (21%)
  Category 2:                         ~60     (40%)
  Category 3:                         ~40     (27%)
  Unknown (needs audit):              ~18     (12%)
```

---

## Recommended Immediate Actions

**For Phase Lead (team-lead)**:
1. Prioritize `vir_is_function()` and `vir_is_sentinel()` helpers (Phase 1)
2. Plan union metadata enrichment in sema (Phase 2 dependency)
3. Schedule audit of intrinsic/calls modules (lower priority)

**For VIR Lowering Team**:
1. When lowering `UnionLiteral`, include variant list from VIR node
2. When lowering `LetTuple`, include union info from sema
3. Ensure `VirTypeId` is populated for function/sentinel types in sema

**For Testing**:
1. Snapshot test for vir_is_function() with functions vs non-functions
2. Snapshot test for vir_is_sentinel() with sentinels
3. Verify no behavioral changes when replacing direct arena() with wrappers

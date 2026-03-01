# ImplementView Audit - Codegen Usage Analysis

**Date**: February 28, 2026
**Status**: Complete read-only research (no edits)
**Total Access Points**: 11 call sites across 5 files

---

## Executive Summary

Codegen accesses `ImplementView` (materialized snapshot of `ImplementRegistry`) at **11 points** across **5 files**. These lookups handle:

1. **External function dispatch** - prelude functions (print, panic, assert)
2. **Generic external intrinsics** - type-parameterized functions with where-clause type mappings
3. **Generic external methods** - type-parameterized methods with type-specific dispatch
4. **Implement-block method dispatch** - user-defined methods from `implement` blocks

**All lookups are immutable reads** from `ImplementView` hash maps. **No registry mutations occur in codegen** (all mutations are sema-only, during `AnalyzedProgram::from_analysis`).

### Data Flow
```
Sema (build ImplementRegistry)
  ↓
Codegen (ImplementView snapshot created once at startup)
  ↓
11 lookup points (immutable reads only)
```

---

## 1. ImplementView Structure

**Location**: `src/crates/vole-codegen/src/analyzed.rs:144-153`

```rust
pub(crate) struct ImplementView {
    /// External function info by short name (e.g. "print").
    external_funcs: FxHashMap<String, ExternalMethodInfoRef>,

    /// Generic external function info by short name.
    generic_externals: FxHashMap<String, GenericExternalInfoRef>,

    /// Generic external method info by (defining type, method name).
    generic_external_methods: FxHashMap<(TypeDefId, NameId), GenericExternalInfoRef>,

    /// Implement-block method bindings by (type name key, method name).
    methods: FxHashMap<(NameId, NameId), MethodImplRef>,
}
```

**Materialization** (analyzed.rs:156-197):
- Built once from `ImplementRegistry` via `from_registry()` during `AnalyzedProgram::from_analysis`
- Converts registry entries to codegen-local structs (`ExternalMethodInfoRef`, `GenericExternalInfoRef`, `MethodImplRef`)
- All 4 maps are FxHashMaps for O(1) lookup by string or tuple key

---

## 2. Helper Methods on AnalyzedProgram

**Location**: `src/crates/vole-codegen/src/analyzed.rs:758-839`

All helper methods are **thin wrappers** around `implement_view` HashMap lookups:

### 2.1 `external_func_by_name` (line 759)
```rust
pub(crate) fn external_func_by_name(&self, name: &str) -> Option<ExternalMethodInfoRef> {
    self.implement_view.external_funcs.get(name).copied()
}
```
- **Accesses**: `implement_view.external_funcs`
- **Returns**: External binding (module path + native name)
- **Used for**: Prelude function dispatch (print, panic, etc)

### 2.2 `generic_external_by_name` (line 764)
```rust
pub(crate) fn generic_external_by_name(&self, name: &str) -> Option<GenericExternalInfoRef> {
    self.implement_view.generic_externals.get(name).cloned()
}
```
- **Accesses**: `implement_view.generic_externals`
- **Returns**: Generic function info + type mappings
- **Used for**: Type-parameterized external function dispatch

### 2.3 `generic_external_method` (line 769)
```rust
pub(crate) fn generic_external_method(
    &self,
    type_def_id: TypeDefId,
    method_name: NameId,
) -> Option<GenericExternalInfoRef> {
    self.implement_view
        .generic_external_methods
        .get(&(type_def_id, method_name))
        .cloned()
}
```
- **Accesses**: `implement_view.generic_external_methods`
- **Returns**: Generic method info + type mappings
- **Used for**: Type-parameterized method dispatch

### 2.4 `implement_method_by_name` (line 819)
```rust
pub(crate) fn implement_method_by_name(
    &self,
    type_name_id: NameId,
    method_name_id: NameId,
) -> Option<MethodImplRef> {
    self.implement_view
        .methods
        .get(&(type_name_id, method_name_id))
        .cloned()
}
```
- **Accesses**: `implement_view.methods`
- **Returns**: Method signature + optional external binding
- **Used for**: Implement-block method dispatch

### 2.5 `implement_method_for_type` (line 831)
```rust
pub(crate) fn implement_method_for_type(
    &self,
    type_id: vole_sema::type_arena::TypeId,
    method_name_id: NameId,
) -> Option<(NameId, MethodImplRef)> {
    let type_name_id = self.impl_type_name_id_from_type_id(type_id)?;
    let method_impl = self.implement_method_by_name(type_name_id, method_name_id)?;
    Some((type_name_id, method_impl))
}
```
- **Accesses**: `implement_view.methods` (via `implement_method_by_name`)
- **Used for**: Implement-block method dispatch with type resolution
- **Note**: High-level convenience; delegates to `implement_method_by_name`

---

## 3. Call Sites by File

### 3.1 `src/crates/vole-codegen/src/calls/mod.rs` (1 call)

**Line 163** - `compile_call_expr` → `call_native_external`
```rust
let ext_info = self.analyzed().external_func_by_name(callee_name);
if let Some(ref info) = ext_info {
    // Check if this is a compiler intrinsic (e.g., panic)
    let module_path_str = self.name_table().last_segment_str(info.module_path)?;
    if module_path_str == Cg::COMPILER_INTRINSIC_MODULE {
        return self.call_compiler_intrinsic_from_registry(...);
    }
}
```
- **Purpose**: Dispatch prelude external functions (print, panic, assert)
- **Dispatch flow**:
  1. Lookup external binding by short name
  2. Extract module path (compiler intrinsic vs native)
  3. Route to intrinsic handler or native registry

---

### 3.2 `src/crates/vole-codegen/src/calls/native_calls.rs` (3 calls)

**Line 449** - `try_call_generic_external_monomorphic`
```rust
let Some(generic_ext_info) = self.analyzed().generic_external_by_name(&callee_name) else {
    return Ok(None);
};
let key = self.resolve_intrinsic_key_for_monomorph(
    &callee_name,
    &generic_ext_info.type_mappings,
    &substitutions,
)?;
```
- **Purpose**: Resolve intrinsic key for monomorphized generic external function
- **Dispatch flow**:
  1. Lookup generic function info by short name
  2. Match concrete type against where-clause type mappings
  3. Select concrete intrinsic key (e.g., `array_length_i64`, `array_length_string`)

**Line 598** - `try_call_monomorphized_function`
```rust
if let Some(generic_ext_info) = self.analyzed().generic_external_by_name(callee_name) {
    let key = self.resolve_intrinsic_key_for_monomorph(...);
    // ... dispatch to intrinsic
}
```
- **Purpose**: Same as line 449 (alternative code path for monomorphic dispatch)
- **Context**: Fallback when no VIR monomorph found

**Line 634** - `try_call_monomorphized_function`
```rust
if let Some(ext_info) = self.analyzed().external_func_by_name(callee_name) {
    let module_path = name_table.last_segment_str(ext_info.module_path);
    let native_name = name_table.last_segment_str(ext_info.native_name);
    if let Some(native_func) = self.native_registry().lookup(&module_path, &native_name) {
        return self.compile_native_call_with_types_from_source(...);
    }
}
```
- **Purpose**: Fallback native registry lookup for generic external functions without type mappings
- **Dispatch flow**:
  1. Lookup external binding
  2. Resolve module path + native name
  3. Delegate to native registry for typed call

---

### 3.3 `src/crates/vole-codegen/src/compiler/mod.rs` (2 calls)

**Line 201-205** - `is_external_func`
```rust
fn is_external_func(&self, name_id: NameId) -> bool {
    self.analyzed.name_table()
        .last_segment_str(name_id)
        .map(|short_name| {
            // Check both regular external functions and generic external functions
            self.analyzed.external_func_by_name(&short_name).is_some()
                || self.analyzed.generic_external_by_name(&short_name).is_some()
        })
        .unwrap_or(false)
}
```
- **Purpose**: Predicate check for whether a function is external
- **Dispatch flow**:
  1. Convert NameId to short name
  2. Check presence in both regular and generic external maps
  3. Return bool (used for skip/include decisions)

---

### 3.4 `src/crates/vole-codegen/src/structs/method_dispatch.rs` (2 calls)

**Line 143** - `call_module_method` → generic external method dispatch
```rust
if let Some(callee_name) = self.name_table().last_segment_str(original_name)
    && let Some(generic_ext_info) = self.analyzed().generic_external_by_name(&callee_name)
{
    let key = self.resolve_intrinsic_key_for_monomorph(...);
    // ... dispatch to intrinsic
}
```
- **Purpose**: Resolve intrinsic for monomorphized generic external method
- **Dispatch flow**: Same as native_calls.rs line 449

---

## 4. Call Site Mapping by Feature

### Feature: External Function Dispatch

| File | Line | Method | Purpose | Return Type |
|------|------|--------|---------|------------|
| calls/mod.rs | 163 | `external_func_by_name` | Lookup prelude function | `Option<ExternalMethodInfoRef>` |
| native_calls.rs | 634 | `external_func_by_name` | Fallback native lookup | `Option<ExternalMethodInfoRef>` |
| compiler/mod.rs | 201 | `external_func_by_name` | Predicate check | bool (via `.is_some()`) |

### Feature: Generic External Function Dispatch

| File | Line | Method | Purpose | Return Type |
|------|------|--------|---------|------------|
| native_calls.rs | 449 | `generic_external_by_name` | Monomorph type mapping | `Option<GenericExternalInfoRef>` |
| native_calls.rs | 598 | `generic_external_by_name` | Monomorph type mapping (alt) | `Option<GenericExternalInfoRef>` |
| compiler/mod.rs | 204 | `generic_external_by_name` | Predicate check | bool (via `.is_some()`) |

### Feature: Generic External Method Dispatch

| File | Line | Method | Purpose | Return Type |
|------|------|--------|---------|------------|
| method_dispatch.rs | 143 | `generic_external_by_name` | Monomorph type mapping | `Option<GenericExternalInfoRef>` |

### Feature: Implement-Block Method Dispatch

| File | Line | Method | Purpose | Return Type |
|------|------|--------|---------|------------|
| (None found directly) | - | `implement_method_by_name` | Method lookup | `Option<MethodImplRef>` |
| (None found directly) | - | `implement_method_for_type` | High-level dispatch | `Option<(NameId, MethodImplRef)>` |

**Note**: `implement_method_*` methods are defined but not called from codegen in this snapshot. They exist for potential use in VIR-based dispatch (currently AST-based).

---

## 5. Data Pre-Computation Opportunities

### What Is Pre-Computed

| Data | Computed In | Stored In | Used By |
|------|-------------|-----------|---------|
| External function metadata | Sema (ImplementRegistry) | ImplementView (FxHashMap) | 3 codegen callsites |
| Generic external metadata | Sema (ImplementRegistry) | ImplementView (FxHashMap) | 3 codegen callsites |
| Type mappings (where clauses) | Sema (ImplementRegistry) | GenericExternalInfoRef | Type dispatch logic |
| Implement-block methods | Sema (ImplementRegistry) | ImplementView (FxHashMap) | 0 codegen callsites (VIR-ready) |

### What Is Runtime-Computed

| Data | Computed At | Used For |
|-------|-------------|---------|
| Intrinsic key selection | Codegen (via `resolve_intrinsic_key_for_monomorph`) | Generic external dispatch |
| Native registry lookup | Codegen (via `native_registry.lookup`) | Fallback external dispatch |
| TypeId → NameId resolution | Codegen (via `impl_type_name_id_from_type_id`) | Implement-block dispatch |

---

## 6. VIR Lowering Status

### What Sema Already Computes

From `implement_registry.rs`:
- **MethodImpl**: Contains `func_type`, `is_builtin`, `external_info`, `trait_name`
- **GenericExternalInfo**: Contains `module_path`, `type_mappings` (Vec<TypeMappingEntry>)
- **TypeMappingEntry**: Contains `kind` (Exact | Default) and `intrinsic_key`

### What VIR Could Annotate

1. **External function calls**: `VirExpr::Call { callee, ... }` could carry:
   - `external_binding: Option<ExternalMethodInfoRef>`
   - `generic_info: Option<GenericExternalInfoRef>`
   - Eliminates runtime HashMap lookups by short name

2. **Intrinsic key dispatch**: `VirExpr::Call { ... }` could carry:
   - `intrinsic_key: Option<String>` (pre-selected based on concrete type)
   - Eliminates `resolve_intrinsic_key_for_monomorph` recomputation

3. **Implement-block methods**: `VirExpr::MethodCall { object, method_name, ... }` could carry:
   - `method_impl: Option<MethodImplRef>` (resolved during sema)
   - Eliminates HashMap lookup by (type_name_id, method_name_id)

### Current Codegen Re-Detection

- **Line 449, 598**: `resolve_intrinsic_key_for_monomorph` re-scans type mappings to match concrete type
  - Input: `GenericExternalInfoRef.type_mappings` (Vec<TypeMappingEntry>)
  - Output: Selected `intrinsic_key` string
  - **Pre-computable**: If monomorph key is available during lowering, select key once

- **Line 201, 204**: `is_external_func` predicate rebuilds string representation
  - Input: NameId
  - Output: bool
  - **Pre-computable**: Mark function as external in VIR metadata

---

## 7. Integration Points with Ongoing VIR Work

### VirExpr Annotation Candidates

```rust
// Current: No external/intrinsic info
pub enum VirExpr {
    Call { callee, args, ... },
    // ...
}

// Proposed (Tier B-C work):
pub enum VirExpr {
    Call {
        callee,
        args,
        external_info: Option<ExternalMethodInfoRef>,    // NEW
        intrinsic_key: Option<String>,                    // NEW
        // ...
    },
    // ...
}
```

### Codegen Refactoring (Post-Annotation)

**Before** (current):
```rust
// Line 449
let generic_ext_info = self.analyzed().generic_external_by_name(&callee_name)?;
let key = self.resolve_intrinsic_key_for_monomorph(
    &callee_name,
    &generic_ext_info.type_mappings,
    &substitutions,
)?;
```

**After** (with VIR annotation):
```rust
// VIR already has intrinsic_key precomputed
let key = vir_call_expr.intrinsic_key.ok_or(...)?;
// No HashMap lookup, no type mapping scan
```

---

## 8. Summary Table: All 11 Call Sites

| # | File | Line | Method | Feature | Pre-Computable? |
|---|------|------|--------|---------|-----------------|
| 1 | calls/mod.rs | 163 | `external_func_by_name` | External dispatch | ✓ (module path via annotation) |
| 2 | native_calls.rs | 449 | `generic_external_by_name` | Generic dispatch | ✓ (intrinsic_key via annotation) |
| 3 | native_calls.rs | 598 | `generic_external_by_name` | Generic dispatch (alt) | ✓ (intrinsic_key via annotation) |
| 4 | native_calls.rs | 634 | `external_func_by_name` | Fallback native | ✓ (module+native names via annotation) |
| 5 | compiler/mod.rs | 201 | `external_func_by_name` | Predicate check | ✓ (is_external flag in VIR) |
| 6 | compiler/mod.rs | 204 | `generic_external_by_name` | Predicate check | ✓ (is_generic_external flag in VIR) |
| 7 | method_dispatch.rs | 143 | `generic_external_by_name` | Generic method | ✓ (intrinsic_key via annotation) |
| 8 | analyzed.rs | 759 | `external_func_by_name` (helper) | Lookup method | ✓ (wrapper elimination) |
| 9 | analyzed.rs | 764 | `generic_external_by_name` (helper) | Lookup method | ✓ (wrapper elimination) |
| 10 | analyzed.rs | 774 | `generic_external_method` (helper) | Lookup method | ✓ (wrapper elimination) |
| 11 | analyzed.rs | 824 | `implement_method_by_name` (helper) | Lookup method | ✓ (wrapper elimination) |

**Pre-computable**: Data that sema already has can be stored in VIR nodes, eliminating codegen-time HashMap lookups.

---

## 9. Risk Assessment

### No Mutations in Codegen
- ✅ ImplementView is immutable after construction
- ✅ No codegen code mutates ImplementRegistry
- ✅ Safe to snapshot once and share across compilation

### HashMap Lookup Efficiency
- ✅ All lookups are O(1) via FxHashMap
- ✅ No linear scans or nested loops over registry
- ✅ Snapshot materialization (O(n) at startup, n=methods count) is acceptable

### Data Dependencies
- ✅ No circular dependencies (ImplementRegistry is independent)
- ✅ Safe to populate ImplementView early in `from_analysis`
- ✅ All codegen accesses are after ImplementView construction

---

## 10. Recommendations

### Tier 1: Current Architecture (No Changes)
- **Status**: ✅ Stable and correct
- **Action**: Document this audit for team knowledge
- **Effort**: 0 (already implemented)

### Tier 2: Optional - Refactor for VIR (Future)
- **Goal**: Eliminate HashMap lookups from codegen hot paths
- **Scope**: Annotate VirExpr nodes with external/intrinsic metadata
- **Effort**: 2-3 weeks (Tier B-C work for larger VIR epic)
- **Files affected**:
  - vole-sema/src/lowering (add metadata during lowering)
  - vole-vir/src/lib.rs (extend VirExpr variants)
  - vole-codegen/src (use annotations instead of lookups)
- **Benefit**: Eliminate 7/11 HashMap lookups + string comparisons from hot paths

### Tier 3: Implement-Block Method Dispatch
- **Status**: ✓ Lookup methods exist (`implement_method_by_name`, `implement_method_for_type`)
- **Usage**: Currently 0 codegen callsites
- **Future**: VIR method call nodes will use these methods
- **No action needed**: Methods are ready for Phase 2 VIR implementation

---

## Conclusion

`ImplementView` serves as a **one-time snapshot facade** over `ImplementRegistry`, providing O(1) lookups for:
1. External function binding (3 sites)
2. Generic external dispatch (4 sites)
3. Implement-block methods (2 helper methods + 0 current calls, 2 indirect via helpers)

All data is pre-computed in sema; codegen only reads. The design is sound and can be extended with VIR-based annotations to eliminate HashMap lookups in future phases.

# VirProgram Structure Audit

## Executive Summary

`VirProgram` is the complete VIR output from sema lowering. It is well-designed and captures most entity metadata codegen needs. However, there are **4 significant gaps** where VirProgram is missing data that exists in sema but should be captured:

1. **Method signatures** — Only method name/ID stored; parameter types and return type not captured
2. **Function signatures** — FunctionIds mapped to VirFunctions, but function types not in VirProgram
3. **Field type annotations** — Field-level `@annotation` markers exist in sema but VirAnnotation only stores values, not the marker itself
4. **Type alias resolution** — Alias target types not stored (TypeDef.aliased_type not captured)

Each gap has estimated effort and impact analysis below.

---

## VirProgram Structure

**Location:** `/home/phil/code/personal/vole/src/crates/vole-vir/src/program.rs` (172 lines)

### Current Fields

```rust
pub struct VirProgram {
    pub type_table: VirTypeTable,
    pub functions: Vec<VirFunction>,
    pub monomorph_map: FxHashMap<NameId, usize>,
    pub function_map: FxHashMap<FunctionId, usize>,
    pub method_map: FxHashMap<MethodId, usize>,
    pub generic_functions: Vec<VirFunction>,
    pub generic_map: FxHashMap<NameId, usize>,
    pub tests: Vec<VirTest>,
    pub global_inits: FxHashMap<Symbol, VirRef>,
    pub module_global_inits: FxHashMap<String, FxHashMap<Symbol, VirRef>>,
    pub function_default_inits: FxHashMap<(FunctionId, usize), VirRef>,
    pub method_default_inits: FxHashMap<(MethodId, usize), VirRef>,
    pub lambda_default_inits: FxHashMap<(NodeId, usize), VirRef>,
    pub field_default_inits: FxHashMap<FieldId, VirRef>,
    pub annotation_inits: FxHashMap<FieldId, Vec<VirAnnotation>>,
    pub vir_monomorph_base: usize,
    pub entity_metadata: VirEntityMetadata,
}
```

**Total:** 15 fields; **Data ownership:** VirProgram owns all lowered data; codegen never reaches back to sema.

---

## VirEntityMetadata Structure

**Location:** `/home/phil/code/personal/vole/src/crates/vole-vir/src/entity_metadata.rs` (592 lines)

Populated in sema VIR lowering via `build_entity_metadata()` in `/home/phil/code/personal/vole/src/crates/vole-sema/src/lowering/entity_metadata.rs` (150 lines).

### Current Contents

1. **VirTypeDef** (78 lines)
   - `id, name_id, kind, fields, methods, static_methods, extends, type_params, implements, is_annotation`
   - Captures: What kind of type, what methods, what interfaces it implements
   - **Missing:** Generic info, error info, base_type_id, aliased_type (for aliases)

2. **VirFieldDef** (106 lines)
   - `id, name_id, full_name_id, defining_type, vir_ty, slot, symbol`
   - Captures: Field name, type, storage location
   - **Missing:** Default value expressions, field annotations, whether field is declared with defaults

3. **VirMethodDef** (133 lines)
   - `id, name_id, full_name_id, defining_type, has_default, is_static, required_params, param_names`
   - Captures: Basic method metadata
   - **Missing:** Method signature types (param types, return type), method type parameters, external binding info, defining_module

4. **VirImplementation** (157 lines)
   - `interface, method_bindings`
   - Captures: Which interface and which methods bound
   - **Missing:** Type arguments for generic interfaces, target_type_args for specializations, span for error reporting

---

## Source: What Sema Has

**Location:** `/home/phil/code/personal/vole/src/crates/vole-sema/src/entity_defs.rs` (242 lines)

### Sema TypeDef (128 lines)
Fields sema has that VirTypeDef doesn't:
- `aliased_type: Option<TypeId>` — For type aliases (TypeDefKind::Alias)
- `generic_info: Option<GenericTypeInfo>` — For generic types
- `error_info: Option<ErrorTypeInfo>` — For error types
- `base_type_id: Option<TypeId>` — Pre-computed base for class/struct

### Sema MethodDef (161 lines)
Fields sema has that VirMethodDef doesn't:
- `signature_id: TypeId` — The full method signature (params + return)
- `method_type_params: Vec<TypeParamInfo>` — Generic parameters on the method itself
- `external_binding: Option<ExternalMethodInfo>` — For FFI methods
- `defining_module: Option<ModuleId>` — For file-scoped extension methods
- `param_defaults: Vec<Option<Box<Expr>>>` — Default parameter values (already has `required_params`)

### Sema FieldDef (189 lines)
Fields sema has that VirFieldDef doesn't:
- `annotations: Vec<ValidatedAnnotation>` — Field-level annotations (markers + values)

### Sema Implementation (97 lines)
Fields sema has that VirImplementation doesn't:
- `type_args: Vec<TypeId>` — Generic interface type arguments
- `target_type_args: Vec<TypeId>` — Specialization target arguments
- `span: Option<SourceSpan>` — For error reporting

---

## Populated During Lowering

**Location:** `/home/phil/code/personal/vole/src/crates/vole-sema/src/lowering/entity_metadata.rs`

### What Gets Lowered

Three simple population functions, each iterating sema's registry:

1. **populate_type_defs** (lines 71-102)
   - Copies: `id, name_id, kind, fields, methods, static_methods, extends, type_params, implements, is_annotation`
   - **Skips:** `aliased_type, generic_info, error_info, base_type_id`

2. **populate_field_defs** (lines 110-133)
   - Copies: `id, name_id, full_name_id, defining_type, slot`
   - Translates: sema `TypeId` → VIR `VirTypeId`
   - Resolves: `NameId` → `Symbol` via interner
   - **Skips:** `annotations` (available in sema but not captured)

3. **populate_method_defs** (lines 136-149)
   - Copies: `id, name_id, full_name_id, defining_type, has_default, is_static, required_params, param_names`
   - **Skips:** `signature_id, method_type_params, external_binding, defining_module, param_defaults`

### VirAnnotation (not per-field metadata)

**Location:** `/home/phil/code/personal/vole/src/crates/vole-vir/src/types.rs` (lines 223-238)

Currently stored:
```rust
pub struct VirAnnotation {
    pub type_def: TypeDefId,      // The annotation type
    pub value: VirAnnotationValue, // Instance fields with constant values
}
```

**Populated:** `annotation_inits` map (FieldId → Vec<VirAnnotation>) via `lower_annotation_inits()` in sema.

**Note:** This stores the annotation VALUES, not the TYPE/MARKER itself. Field declarations with `@annotation_type_name` are validated but not explicitly stored in VirProgram.

---

## Identified Gaps

### Gap 1: Method Signatures

**What's Missing:** Sema stores `signature_id: TypeId` (full function type with all params + return). VirProgram stores only method names and required param count.

**Impact:**
- Codegen cannot statically verify method call argument types
- Method dispatch requires sema lookup (currently: methods are dispatched via explicit VIR metadata, not type-checked at codegen time)
- Cross-module method calls would need full signatures for verification

**Current Workaround:** VirFunction stores the actual compiled bodies; codegen infers param/return types from VIR expressions.

**Effort to Add:**
- Add `signature: VirTypeId` to VirMethodDef
- Populate in `populate_method_defs()` via `translate_type_id()`
- **Estimated: 2-3 hours** (API additive, low complexity)

**Priority:** Low — codegen currently works without this; type verification happens in sema, not codegen.

---

### Gap 2: Function Signatures

**What's Missing:** Similar to methods — function signature types are not stored in VirProgram.

**Current State:**
- `FunctionId` → VirFunction via `function_map`
- VirFunction has `id, name, type_params, params, ret, body, ...`
- But there's no separate VirFunctionDef like VirMethodDef

**Impact:**
- Codegen has all signatures via VirFunction bodies
- No issue in current architecture

**Effort to Add:**
- Only needed if building a signature-level cache for fast lookups (not needed now)
- Would require adding a `function_defs` map to VirProgram

**Priority:** Very Low — VirFunctions are already well-indexed.

---

### Gap 3: Field Annotations (Type/Marker)

**What's Missing:** Field declarations with `@annotation_type_name` are validated in sema but only the VALUES are stored in VirProgram.

**Current State:**
```
Sema: FieldDef.annotations = [ValidatedAnnotation { type_def_id, args }]
VIR:  annotation_inits[field_id] = [VirAnnotation { type_def, value }]
```

**What's Lost:** The distinction between "no annotations" and "annotations present but with empty values". Also: which annotation types were declared vs. validated.

**Impact:**
- Low — codegen treats all annotations uniformly
- Reflection code (T.@meta) doesn't distinguish marker types from data annotations
- No current use case for this distinction in codegen

**Effort to Add:**
- Change VirFieldDef to include `annotation_types: Vec<TypeDefId>` (just the markers)
- Populate in `populate_field_defs()` from sema's `annotations` list
- **Estimated: 2-3 hours** (straightforward addition)

**Priority:** Low — No current codegen needs this; future reflection work (Phase 2+) might benefit.

---

### Gap 4: Type Alias Resolution

**What's Missing:** TypeDef with kind=Alias doesn't store the target type.

**Current State:**
```
Sema: TypeDef { kind: Alias, aliased_type: Some(target_type_id) }
VIR:  VirTypeDef { kind: Alias, /* no target stored */ }
```

**Impact:**
- Codegen treating aliases as distinct types from their targets
- Some error messages might not resolve aliases to their underlying types
- Type checking at codegen boundaries might be confused

**Actual Impact Assessment:**
- Check sema's type alias logic: are aliases eliminated before codegen?
- If aliases are always resolved in sema's type normalization, this gap is non-critical

**Effort to Add:**
- Add `aliased_type: Option<VirTypeId>` to VirTypeDef
- Populate in `populate_type_defs()` by translating sema's `aliased_type: Option<TypeId>` → VirTypeId
- **Estimated: 1-2 hours** (simple field addition)

**Priority:** Medium — Important for complete type information, but if aliases are normalized in sema, not blocking.

---

### Gap 5: Generic Type Information

**What's Missing:** Sema's `GenericTypeInfo` (type params, field names, field types with TypeParam placeholders) is not captured.

**Current State:**
- VirTypeDef stores `type_params: Vec<NameId>` (just names)
- No field type parametrization stored
- Generic info only lives in monomorph templates in `generic_functions`

**Impact:**
- Codegen cannot reconstruct generic class layouts without monomorphization
- Post-monomorphization (all instances concrete), this is non-critical
- Would be needed only for generic reflection or late binding

**Effort to Add:**
- New struct `VirGenericTypeInfo` mirroring sema's `GenericTypeInfo`
- Add to VirTypeDef
- Populate from sema's `generic_info` field
- **Estimated: 3-4 hours** (needs struct definition + translation)

**Priority:** Very Low — Not needed post-monomorphization; generic templates are stored in `generic_functions`.

---

### Gap 6: Error Type Information

**What's Missing:** Error types' field information.

**Current State:**
- Sema stores `error_info: Option<ErrorTypeInfo>` with field definitions
- VirProgram has no equivalent

**Impact:**
- Low — error types are rare; field access via methods, not direct field lookups
- Would be needed for error reflection or generic error handling

**Effort to Add:**
- Copy `ErrorTypeInfo` structure to VIR (or reference it via TypeDefId)
- Add to VirTypeDef
- Populate from sema
- **Estimated: 2-3 hours**

**Priority:** Very Low — No current codegen needs; low-value feature.

---

### Gap 7: Implementation Type Arguments

**What's Missing:** Generic interface type arguments and target specializations.

**Current State:**
```
Sema: Implementation { type_args: Vec<TypeId>, target_type_args: Vec<TypeId> }
VIR:  VirImplementation { interface, method_bindings /* no type args */ }
```

**Impact:**
- Medium — Generic interface dispatch might require type arg info
- Example: `impl MyType { Iterator<i64> { ... } }` — the `i64` is not captured
- Codegen currently uses method dispatch metadata (VirMethodDispatchKind); type args are not separately needed

**Effort to Add:**
- Add `type_args: Vec<VirTypeId>` and `target_type_args: Vec<VirTypeId>` to VirImplementation
- Populate in `populate_type_defs()` via type translation
- **Estimated: 2-3 hours**

**Priority:** Medium — Useful for generic interface dispatch, but currently not blocking (dispatch metadata handles this).

---

## Gaps Summary Table

| Gap | Field | Impact | Effort | Priority | Blocking |
|-----|-------|--------|--------|----------|----------|
| 1 | Method signatures (signature_id) | Low | 2-3h | Low | No |
| 2 | Function signatures | Very Low | — | Very Low | No |
| 3 | Field annotations (markers) | Low | 2-3h | Low | No |
| 4 | Type alias targets | Medium | 1-2h | Medium | Depends |
| 5 | Generic type info | Low | 3-4h | Very Low | No |
| 6 | Error type info | Low | 2-3h | Very Low | No |
| 7 | Implementation type args | Medium | 2-3h | Medium | No |

---

## Key Architecture Points

### What VirProgram Does Well

1. **Clean ownership:** Owns all lowered data; codegen never reaches back to sema
2. **Entity metadata separation:** VirEntityMetadata isolates type/field/method info
3. **Comprehensive function/test coverage:** All functions, tests, defaults, and inits captured
4. **Type table unification:** Single VirTypeTable shared across all functions
5. **Annotation values:** Field-level annotation VALUES are captured (VirAnnotation)

### Design Decisions (Intentional Gaps)

1. **No generic type info in VirTypeDef** — Generic classes are monomorphized before codegen; generic templates live in `generic_functions`
2. **No method signatures in VirMethodDef** — Codegen gets signatures from VirFunction bodies; type inference is not needed at method dispatch time
3. **No alias target in VirTypeDef** — Aliases should be resolved to their targets in sema's type normalization before lowering

### Codegen Assumptions

1. **Post-monomorphization:** All types are concrete (no TypeParam in VirType)
2. **Explicit dispatch metadata:** Method calls carry full dispatch information (VirMethodDispatchKind)
3. **Type lookup via VirTypeTable:** All types are in the shared table; no separate sema lookups needed
4. **VirFunction is ground truth:** Function bodies contain all needed type information

---

## Recommendations

### Tier 1 (Do First)
None — VirProgram is sufficient for current codegen needs.

### Tier 2 (Enhancement)
- **Gap 4 (Type alias targets):** Add if sema's alias resolution is incomplete
- **Gap 7 (Implementation type args):** Add if generic interface dispatch needs this info
- Both are 2-3 hours each; add together if tackling implementation dispatch overhaul

### Tier 3 (Future)
- **Gap 3 (Field annotation markers):** Add when field-level reflection (Phase 2) needs marker types
- **Gap 5 (Generic type info):** Add only if supporting late generic dispatch
- **Gap 6 (Error type info):** Add only if building error reflection

### NOT Recommended
- **Gap 2 (Function signatures):** VirFunctions are already well-indexed; no benefit to duplicating signature info

---

## Data Flow Summary

```
Sema EntityRegistry
    ↓ (build_entity_metadata)
VirEntityMetadata
    ↓
VirProgram
    ↓ (codegen uses)
Cranelift Code
```

**Lowering pipeline:** `/home/phil/code/personal/vole/src/crates/vole-sema/src/lowering/facade.rs:71-360`
- Populates VirProgram fields sequentially
- `entity_metadata` populated last (line 334) via `build_entity_metadata()`
- No other entity data flows into VirProgram after this point

---

## Testing

**Unit tests for VirEntityMetadata:** `/home/phil/code/personal/vole/src/crates/vole-vir/src/entity_metadata.rs:361-591` (230 lines)
- Comprehensive coverage of insert/query/predicate operations
- No tests for missing fields (since they're not added yet)

**Integration tests:** Run `just snap` to test lowering/codegen integration.

---

## References

- VirProgram: `/home/phil/code/personal/vole/src/crates/vole-vir/src/program.rs`
- VirEntityMetadata: `/home/phil/code/personal/vole/src/crates/vole-vir/src/entity_metadata.rs`
- Lowering facade: `/home/phil/code/personal/vole/src/crates/vole-sema/src/lowering/facade.rs`
- Entity lowering: `/home/phil/code/personal/vole/src/crates/vole-sema/src/lowering/entity_metadata.rs`
- Sema entity defs: `/home/phil/code/personal/vole/src/crates/vole-sema/src/entity_defs.rs`

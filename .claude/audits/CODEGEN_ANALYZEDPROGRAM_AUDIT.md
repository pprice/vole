# Audit: Codegen Reads from AnalyzedProgram Fields

**Date**: February 28, 2026
**Scope**: Exhaustive catalog of every place codegen reads from AnalyzedProgram
**Total accesses**: 395 across 61 distinct field/method reads
**Search pattern**: `.analyzed.*` in `/src/crates/vole-codegen/src/`

---

## Summary by Field Category

### 1. **VIR Program Data** (8 accesses)

#### `vir_program()`
- **Data accessed**: `VirProgram` struct containing lowered VIR functions, tests, globals, type table
- **Access locations**:
  - `compiler/common.rs:548,557` — converting VIR type IDs to sema TypeIds via type_table
  - `context.rs:359,843,854` — global variable initializer lookup, per-module globals
  - `compiler/mod.rs` — type registry initialization
- **VirProgram equivalent**: YES, fully stored in `vir_program`
- **Notes**:
  - `vir_program().type_table` used for type conversions (vir → sema)
  - `vir_program().module_global_inits` for module-scoped globals
  - `vir_program().global_inits` for main program globals
  - Type table is VIR's representation of sema TypeArena

---

### 2. **Type Arena / Type System Data** (16 accesses)

#### `type_arena()`
- **Data accessed**: `TypeArena` — all type metadata (structs, classes, interfaces, unions, generics)
- **Access locations**:
  - `generator.rs:84,209,288` — expression type resolution during VIR compilation
  - `compiler/common.rs:549` — type ID conversion
  - `context.rs:731` — struct unwrapping for annotation type detection
  - `compiler/mod.rs:153` — type registry initialization
- **VirProgram equivalent**: PARTIAL
  - VIR has `type_table: VirTypeTable` but it's indexed by `VirTypeId` (different from sema `TypeId`)
  - VirTypeTable doesn't store full type metadata (struct layout, generics, etc.)
  - Codegen still needs TypeArena for non-VIR paths (NodeMap-based fallback)
- **Critical gap**: VIR-to-sema type lookups require bidirectional mapping

#### `display_type_id_short()`
- **Data accessed**: TypeArena, NameTable, EntityView (for debug/error display)
- **Access locations**: `vir_printer.rs:1002`
- **VirProgram equivalent**: NO — this is diagnostic/debug only
- **Notes**: Used for pretty-printing type names in debug output

---

### 3. **Entity Registry Data** (90+ accesses across 20+ helper methods)

#### Entity Lookups by TypeDefId / FieldId / FunctionId / MethodId

**`type_def()` / `get_type()`** (17 accesses)
- Resolves sema `TypeDef` by ID
- Locations: `compiler/impl_dispatch.rs:788`, `type_registry.rs:53,188`, `compiler/impl_monomorph.rs`
- Data: struct/class/interface metadata, fields, methods, module membership, annotations
- **VirProgram equivalent**: NO
- **Gap**: VIR functions store `FunctionId`/`MethodId` but codegen still needs TypeDef for field layout, method dispatch

**`field_def()` / `get_field()`** (2 accesses)
- Resolves `FieldDef` by FieldId
- Locations: `type_registry.rs:226,235`
- Data: field name, type, index in struct
- **VirProgram equivalent**: NO — VIR stores flat field lists in VirClassDef but codegen reaches to EntityRegistry for metadata

**`function_def()`** (10 accesses)
- Resolves `FunctionDef` by FunctionId
- Locations: `compiler/generic_collection.rs:270`, `compiler/signatures.rs:140`, `compiler/mod.rs:183`
- Data: generic info, signature, defaults, module membership
- **VirProgram equivalent**: PARTIAL (VirFunction exists but lacks generic_info)

**`method_def()`** (1 access)
- Resolves `MethodDef` by MethodId
- Locations: `compiler/signatures.rs:157`
- Data: method metadata, defaults
- **VirProgram equivalent**: PARTIAL (VirFunction for methods but no MethodDef equivalent)

**`method_at()`** (implicit via node_map)
- Returns resolved method metadata from NodeMap per call site
- Data: method dispatch kind, implementation target
- **VirProgram equivalent**: PARTIAL (VirMethodDispatch in VirExpr but only for some cases)

---

#### Type Relationship Queries

**`type_params()`** → `entity_type_params()` (1 call)
- Get declared type parameter NameIds for generics
- Location: `compiler/impl_monomorph.rs`
- **VirProgram equivalent**: NO — Type params not stored in VIR

**`implemented_interfaces()`** (2 accesses)
- Get list of interfaces a type implements
- Locations: `compiler/impl_monomorph.rs:1795,2029`
- **VirProgram equivalent**: NO

**`interface_impl_type_param_subs()`** (implicit)
- Build type param substitutions for interface implementations
- **VirProgram equivalent**: NO

**`is_interface_type()`** (implicit)
- Check if a TypeDef is an interface
- **VirProgram equivalent**: PARTIAL (VirClassKind exists but not queried during codegen)

**`is_external_only()`** (1 access)
- Check if type has only external method implementations
- Location: `interfaces/vtable.rs:2107`
- **VirProgram equivalent**: NO

**`methods_on_type()` / `type_methods()`** (implicit)
- Get all method IDs declared on a type
- **VirProgram equivalent**: PARTIAL (VirClassDef.methods but not queried directly)

**`find_method()` / `find_static_method()`** (5 accesses)
- Resolve method by name on a type
- Locations: `compiler/impl_monomorph.rs:154,467,1366,1489`
- **VirProgram equivalent**: NO

**`method_full_name()`** (3 accesses)
- Get canonical NameId for a method
- Locations: `compiler/impl_dispatch.rs:35`, `type_registry.rs:542`, `impl_monomorph.rs:1502`
- **VirProgram equivalent**: NO

**`is_functional_interface()`** (implicit)
- Check if interface has single abstract method
- **VirProgram equivalent**: NO

---

### 4. **Name Table / Symbol Resolution** (17 accesses)

#### `name_table()`
- **Data accessed**: All name-to-ID mappings (types, functions, methods, globals in each module)
- **Access locations**: `context.rs:339,830,842`, `generic_collection.rs:151,205`, multiple dispatch locations
- **VirProgram equivalent**: NO
- **Notes**: Used for resolving NameId from Symbol or segments, querying module paths

#### `interner()` / `interner_rc()` (16 accesses)
- **Data accessed**: Symbol → string mapping in main program
- **Access locations**: `compiler/mod.rs:14,158`, `generic_collection.rs:103`, `impl_dispatch.rs:55`, etc.
- **VirProgram equivalent**: NO (but partially mitigated by precomputing names in VIR)
- **Notes**: Used for rendering diagnostic strings, resolving method names for dispatch

---

### 5. **NodeMap / Per-Expression Metadata** (2 direct accesses, 10+ indirect via helper methods)

#### `node_map()`
- **Data accessed**: Expression-level type, method resolution, generic instantiation keys, coercion info
- **Access locations**: `context.rs:707`, `compiler/program.rs:66`
- **VirProgram equivalent**: NO (VIR nodes embed this metadata directly)
- **Coverage**: Used by AST-fallback codegen path (non-VIR functions)
- **Notes**:
  - `get_type(node_id)` — expression type
  - `get_method(node_id)` — method resolution
  - `get_generic(node_id)` — generic instantiation keys
  - `get_static_method_generic(node_id)` — static method monomorph keys
  - `get_synthetic_it_lambda(node_id)` — implicit `it` lambda synthesis

---

### 6. **Module Program Data** (17 accesses)

#### `module_programs()`
- **Data accessed**: Parsed Program AST + Interner for each imported module
- **Access locations**:
  - `generic_collection.rs:160,213` — collecting generic instances from module code
  - `impl_dispatch.rs:233` — looking up method implementations in module AST
  - `compiler/program.rs:519,653` — iterating over module paths
- **VirProgram equivalent**: PARTIAL
  - VIR stores module programs for per-module VIR functions
  - AST programs needed for non-VIR paths (generic collection, dispatch lookup)
- **Notes**: Contains interface method bodies that codegen reads during vtable generation

---

### 7. **Identity/Lookup Helpers** (40+ accesses)

#### Name/ID Resolution

**`try_name_id()` / `name_id()`** (3 accesses)
- Resolve NameId from module + symbol segments
- Locations: `generic_collection.rs:41,52,96`
- Uses: NameTable + Interner

**`try_name_id_with_interner()`** (4 accesses)
- Same but with explicit interner (for module code)
- Locations: `generic_collection.rs:166,179,218`

**`function_id_by_name_id()` / `function_id()`** (3 accesses)
- Resolve FunctionId from NameId or module+symbol
- Locations: `compiler/mod.rs:281`, `compiler/program.rs:294,872`

**`try_function_name_id()`** (3 accesses)
- Resolve function NameId from module + symbol
- Locations: `compiler/mod.rs:318`, `compiler/program.rs:27,228`

**`function_name_id()`** (3 accesses)
- Same as above, panics if not found
- Locations: `compiler/generic_collection.rs:263`, `compile_tests.rs:203`, `program.rs:328`

**`try_method_name_id_by_str()` / `method_name_id_by_str()`** (implicit)
- Resolve method NameId from short string (e.g., "push")
- Used in dispatch for array methods, iterator methods

**`try_type_def_id()`** (22 accesses)
- Resolve TypeDefId from NameId
- Locations: `impl_dispatch.rs:641`, `type_registry.rs:69,123`, many others
- **VirProgram equivalent**: PARTIAL (VirTypeId exists but is different from TypeDefId)
- **Gap**: Bidirectional mapping TypeDefId ↔ VirTypeId needed

**`resolve_type_def_by_str()`** (1 access)
- Resolve TypeDefId from module + string
- Location: `impl_monomorph.rs:284`

**`type_by_short_name()`** (implicit)
- Look up type by last-segment name
- Used for WellKnownTypes lookups

**`entity_type_name_id()`** (implicit)
- Get NameId for a TypeDefId (inverse of try_type_def_id)

**`impl_type_name_id_from_type_id()`** (8 accesses)
- Resolve implement-registry NameId from sema TypeId
- Locations: `impl_monomorph.rs:70,75,357`
- **VirProgram equivalent**: NO

**`module_id_or_main()` / `module_id_if_known()`** (9 accesses)
- Look up ModuleId from module path string
- Locations: `impl_dispatch.rs:268`, `program.rs:456,477`, etc.

---

### 8. **Monomorphization Caches** (8 accesses)

#### Monomorph Cache Access

**`monomorph_cache()`** (4 accesses)
- Get free-function monomorph instantiation cache
- Locations: `context.rs:954`, `compiler/monomorphization.rs:75,115`
- Data: KeySet of (generic_key) → compiled status
- **VirProgram equivalent**: NO

**`class_method_monomorph_cache()`** (2 accesses)
- Get class-method monomorph instantiation cache
- Locations: `compiler/monomorphization.rs:1106,1890`

**`static_method_monomorph_cache()`** (2 accesses)
- Get static-method monomorph instantiation cache
- Locations: `compiler/monomorphization.rs:1056,1908`

**`monomorph_for()`** (implicit via node_map)
- Get monomorph key for a call node

**`static_method_generic_at()`** (implicit via node_map)
- Get static method monomorph key

---

### 9. **VIR Function/Test Lookups** (14 accesses)

#### VIR Access

**`get_vir_function()`** (3 accesses)
- Resolve VirFunction by semantic FunctionId
- Locations: `compiler/compile_tests.rs:357`, `program.rs:775,881`
- Returns: `Option<&VirFunction>` or None if not lowered

**`get_vir_method()`** (8 accesses)
- Resolve VirFunction by semantic MethodId
- Locations: `compiler/impl_dispatch.rs:369,482,599`
- Returns: Method body in VIR form

**`get_vir_monomorph()`** (1 access)
- Resolve VirFunction by mangled NameId (generic instance)
- Location: `compiler/monomorphization.rs:208`

**`get_vir_test()`** (2 accesses)
- Resolve test VirBody by Span
- Locations: `compiler/compile_tests.rs:83,420`

**`vir_function_in_module()`** (implicit)
- Check if a VirFunction belongs to given module

---

### 10. **Global & Default Parameter Data** (3+ accesses)

#### `has_global()`
- Check if global variable exists by NameId
- Location: `context.rs:832`

#### `global_type_id()` (implicit)
- Get declared type of a global by NameId

#### `has_function_default_expr()` / `has_method_default_expr()`
- Check if function/method parameter has default
- Used for non-VIR parameter compilation

#### `global_type_id()` (implicit)
- Get type of a global variable

---

### 11. **Generic External Methods** (9 accesses)

#### `generic_external_method()`
- Look up generic external method metadata by (TypeDefId, NameId)
- Locations: derived from implement_view
- Data: type mappings for dispatch

#### `generic_external_by_name()`
- Look up generic external function metadata
- Data: type parameter mappings

#### `external_func_by_name()`
- Look up external function binding metadata
- Location: `compiler/mod.rs:201`

---

### 12. **Module/Program Metadata** (10+ accesses)

#### `module_id()`
- Get main/root module ID
- Locations: `context.rs:829`, `stmt.rs:1323`, `compiler/mod.rs:153`

#### `module_paths()`
- Get list of all imported module paths
- Locations: `program.rs:519,653`

#### `module_interner()`
- Get Interner for imported module by ModuleId
- Used to resolve symbols in module code

#### `module_paths()` / `module_programs()`
- Iterate over imported modules for dispatch lookup, generic collection

#### `tests_virtual_module()`
- Resolve virtual ModuleId for test block by Span
- Location: `compile_tests.rs:131`

#### `modules_with_errors()`
- Get set of module paths with sema errors
- Location: `program.rs:183`
- Used to skip compiling functions from error modules

---

### 13. **Implement Registry / Method Binding Data** (20+ accesses)

#### Direct ImplementView Access

**`implement_method_by_name()`**
- Look up method impl by (NameId, NameId) key
- Used by dispatch paths for concrete type method resolution

**`implement_method_for_type()`**
- Resolve and look up method impl from sema TypeId
- Combines impl_type_name_id_from_type_id + implement_method_by_name

#### Method Binding Queries

**`method_binding()` / `method_binding_return_type()`**
- Get interface method binding metadata
- Locations: implicit in dispatch
- Data: method signature, implementation details

**`method_external_binding()`**
- Check if method has external binding metadata
- Location: `compiler/impl_dispatch.rs` dispatch paths

---

## Data Access Patterns

### By Category

| Category | Count | VIR Coverage | Gap Severity |
|----------|-------|--------------|--------------|
| VIR Program (direct) | 8 | 100% | None |
| TypeArena access | 16 | 30% | HIGH — type lookups, display |
| EntityRegistry (types/fields/functions) | 90+ | 10% | CRITICAL — entity metadata everywhere |
| NameTable | 17 | 0% | HIGH — name resolution dependency |
| NodeMap | 12 | 0% | MEDIUM — fallback for non-VIR |
| Module Programs | 17 | 50% | MEDIUM — AST dispatch lookup |
| Monomorph Caches | 8 | 0% | MEDIUM — instantiation tracking |
| Name/ID resolution | 40+ | 0% | HIGH — pervasive lookups |
| Interface/Generic External | 9 | 0% | MEDIUM — dispatch metadata |
| Module/Program metadata | 10+ | 20% | MEDIUM — module context |

---

## Critical Data Flow Paths

### 1. **Type Resolution Chain**
```
Call site (AST node)
  → node_map.get_type(node_id) [NodeMap]
  → type_arena.resolve_type(type_id) [TypeArena]
  → vir_program.type_table.get(vir_type_id)? [VirProgram]
```
**Gap**: VirTypeId ≠ TypeId — need bidirectional mapping

### 2. **Entity Lookup Chain**
```
TypeId
  → impl_type_name_id_from_type_id(type_id) [entity_view]
  → type_def_id (reverse) [missing]
  → get_type(type_def_id) [entity_view]
  → field_layout, methods, etc. [EntityRegistry]
```
**Gap**: VIR stores VirTypeId but codegen still needs TypeDefId for entity metadata

### 3. **Method Dispatch Chain**
```
Method call (node_id)
  → node_map.get_method(node_id) [NodeMap]
  → ResolvedMethod { dispatch_kind, target, ... }
  → dispatch_kind determines:
     - Module method: look up FunctionId in EntityRegistry
     - Implement block: look up in implement_view
     - Interface: vtable access + vtable method implementation
     - Builtin: use IntrinsicKey from ResolvedMethod
```
**Gap**: Some dispatch resolution still happens at codegen time (e.g., Iterator/Iterable coercion)

### 4. **Monomorphization Tracking**
```
Generic function call (monomorph_key)
  → monomorph_cache.get(key) [EntityRegistry]
  → Already compiled? → get compiled FuncId
  → Not yet? → queue for compilation
```
**Gap**: VIR doesn't track which generics have been compiled; codegen must track manually

---

## Removal Priority & Migration Path

### Phase 1: Safe to Migrate to VirProgram (Tier A: 2-4 weeks)
1. **Replace TypeArena lookups** with VirTypeTable + mapping layer
   - Create VirTypeId ↔ TypeId bidirectional map
   - Migrate all type_arena() calls through map

2. **Replace NodeMap for VIR functions** with embedded VirExpr metadata
   - Already done for most expressions
   - Remaining: synthetic_it_lambdas, coercion metadata

3. **Replace NameTable** with precomputed name tables in VirProgram
   - Collect all NameIds during VIR lowering
   - Store in VirProgram.name_map

### Phase 2: Deferred to Future Phases (Tier B: 4-8 weeks)
1. **EntityRegistry → VirEntityMetadata**
   - Flatten type/field/method/function defs into VIR
   - Reconstruct entity queries from VIR

2. **Monomorph caches → VirMonomorphCache**
   - Track compilation state per generic instance
   - Store in VirProgram

3. **Interface/Generic External → VirDispatchMetadata**
   - Move dispatch resolution earlier (sema time)
   - Store decisions in VIR annotations

### Phase 3: Cannot Migrate (Architectural Limits)
- **Module Programs (AST)**: Needed for runtime generic collection
  - Module generics require parsing + analyzing module AST on demand
  - Cannot pre-compute all instances statically
  - Will always be accessed from AST, not VIR

---

## File Organization by Access Frequency

| File | Accesses | Primary Use |
|------|----------|-------------|
| `compiler/mod.rs` | 40+ | Main compiler orchestration |
| `compiler/impl_monomorph.rs` | 35+ | Generic monomorphization |
| `compiler/impl_dispatch.rs` | 30+ | Method dispatch routing |
| `compiler/monomorphization.rs` | 20+ | Generic collection |
| `context.rs` | 15+ | Codegen context helpers |
| `compiler/program.rs` | 15+ | Program compilation |
| `compiler/type_registry.rs` | 15+ | Type metadata registration |
| `generator.rs` | 10+ | VIR compilation (fallback) |
| `generic_collection.rs` | 10+ | Generic instance discovery |
| Other | 155+ | Various |

---

## Recommendations

### Immediate (Next Sprint)
1. **Document this audit in codebase** ✓ (this file)
2. **Create TypeId ↔ VirTypeId mapping layer** to unblock VIR type conversions
3. **Catalog VirProgram gaps** (separate audit)

### Short-term (2-4 sprints)
1. **Migrate type_arena() calls** → VirTypeTable + mapping
2. **Migrate NodeMap for VIR paths** → use embedded VirExpr metadata
3. **Add NameTable to VirProgram** for symbol resolution

### Medium-term (4-8 sprints)
1. **Flatten EntityRegistry** into VirProgram (VirEntityMetadata)
2. **Add monomorph tracking** to VirProgram
3. **Move interface/external dispatch** into sema annotations

### Long-term (Phase 3)
1. Keep Module Program ASTs (architectural requirement for generic collection)
2. Consider lazy codegen (vol-m3xo) for deferred generic instantiation

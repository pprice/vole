// entity_metadata.rs
//
// VIR-native entity metadata: type definitions, fields, methods, and
// implementations.  This data replaces codegen's `EntityView` dependency
// on sema's `EntityRegistry`.
//
// Populated once during VIR lowering (which has full sema access), then
// consumed by codegen without reaching back into sema.

use rustc_hash::FxHashMap;
use vole_identity::{
    FieldId, FunctionId, FunctionType, GlobalId, Interner, MethodId, ModuleId, NameId, NameTable,
    Resolver, Symbol, TypeDefId, TypeId, VirTypeId,
};

use crate::expr::VirExternalMethodInfo;
use crate::type_table::VirTypeTable;
use crate::types::{VirPrimitiveKind, VirType};

// ---------------------------------------------------------------------------
// Field type tag — RC cleanup classification
// ---------------------------------------------------------------------------

/// RC cleanup classification for a field in a struct or class instance.
///
/// Mirrors `vole_runtime::type_registry::FieldTypeTag` without depending on
/// `vole-runtime`.  Computed once during VIR lowering so codegen can read the
/// tag directly from `VirFieldDef` instead of re-deriving it at compile time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VirFieldTypeTag {
    /// Non-reference type (i64, f64, bool, etc.) — no cleanup needed.
    Value,
    /// Reference-counted field (String, Array, Instance) — needs rc_dec.
    Rc,
    /// Union heap buffer field (e.g. `Person?` in a class) — needs union_heap_cleanup.
    UnionHeap,
    /// Interface fat pointer field — heap-allocated `[data_word, vtable_ptr]`.
    Interface,
    /// Unknown-typed TaggedValue field — heap-allocated `[tag: u64, value: u64]`.
    UnknownHeap,
}

impl VirFieldTypeTag {
    /// Whether this field type needs any form of RC cleanup.
    pub fn needs_cleanup(self) -> bool {
        !matches!(self, Self::Value)
    }
}

/// Compute the `VirFieldTypeTag` for a VIR type.
///
/// This is the canonical classification used by both VIR lowering and codegen's
/// `vir_type_id_to_field_tag`.  The logic mirrors the runtime's `FieldTypeTag`
/// semantics: Unknown → UnknownHeap, Interface → Interface, RC types → Rc,
/// unions/optionals with RC variants → UnionHeap, everything else → Value.
pub fn compute_field_type_tag(vir_ty: VirTypeId, table: &VirTypeTable) -> VirFieldTypeTag {
    match table.get(vir_ty) {
        VirType::Unknown => VirFieldTypeTag::UnknownHeap,
        VirType::Interface { .. } => VirFieldTypeTag::Interface,
        VirType::Primitive(VirPrimitiveKind::String)
        | VirType::Array { .. }
        | VirType::Class { .. }
        | VirType::Function { .. } => VirFieldTypeTag::Rc,
        VirType::Union { variants } => {
            for &variant in variants {
                if compute_field_type_tag(variant, table).needs_cleanup() {
                    return VirFieldTypeTag::UnionHeap;
                }
            }
            VirFieldTypeTag::Value
        }
        VirType::Optional { inner } => {
            if compute_field_type_tag(*inner, table).needs_cleanup() {
                VirFieldTypeTag::UnionHeap
            } else {
                VirFieldTypeTag::Value
            }
        }
        _ => {
            // Handle type (TypeId::HANDLE) maps to VirType::Primitive(Handle)
            if vir_ty == VirTypeId::HANDLE {
                VirFieldTypeTag::Rc
            } else {
                VirFieldTypeTag::Value
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Type definition kind
// ---------------------------------------------------------------------------

/// What kind of entity a type definition represents.
///
/// Mirrors `sema::entity_defs::TypeDefKind` without depending on sema.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirTypeDefKind {
    Interface,
    Class,
    Struct,
    ErrorType,
    Primitive,
    Alias,
    Sentinel,
}

impl VirTypeDefKind {
    /// Whether this is a sentinel type (zero-field struct).
    pub fn is_sentinel(self) -> bool {
        matches!(self, Self::Sentinel)
    }

    /// Whether this is a class, struct, or sentinel.
    pub fn is_class_struct_or_sentinel(self) -> bool {
        matches!(self, Self::Class | Self::Struct | Self::Sentinel)
    }

    /// Whether this is an interface.
    pub fn is_interface(self) -> bool {
        matches!(self, Self::Interface)
    }

    /// Whether this is a class (heap-allocated, RC-managed).
    pub fn is_class(self) -> bool {
        matches!(self, Self::Class)
    }

    /// Type kind string for error messages ("class", "struct", etc.).
    pub fn type_kind_str(self) -> &'static str {
        match self {
            Self::Interface => "interface",
            Self::Class => "class",
            Self::Struct => "struct",
            Self::ErrorType => "error",
            Self::Primitive => "primitive",
            Self::Alias => "alias",
            Self::Sentinel => "sentinel",
        }
    }
}

// ---------------------------------------------------------------------------
// Type definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a type definition.
///
/// Carries the entity-level data that codegen queries via `EntityView`:
/// kind, fields, methods, implemented interfaces, and type parameters.
#[derive(Debug, Clone)]
pub struct VirTypeDef {
    /// The sema entity ID for this type.
    pub id: TypeDefId,
    /// The canonical name of this type.
    pub name_id: NameId,
    /// What kind of type this is.
    pub kind: VirTypeDefKind,
    /// Field IDs declared on this type (ordered by declaration).
    pub fields: Vec<FieldId>,
    /// Concrete VIR type for each field, parallel to `fields`.
    ///
    /// Populated during VIR lowering by translating each field's sema
    /// `TypeId` to `VirTypeId`.  For non-generic types this contains the
    /// final concrete types; for generic types these are the un-substituted
    /// types (may contain `VirType::Param`).  Codegen uses this to compute
    /// struct layout, field offsets, and RC state without reaching back
    /// into sema.
    pub field_types: Vec<VirTypeId>,
    /// Instance method IDs declared on this type.
    pub methods: Vec<MethodId>,
    /// Static method IDs declared on this type.
    pub static_methods: Vec<MethodId>,
    /// Interfaces this type extends (for interfaces) or empty.
    pub extends: Vec<TypeDefId>,
    /// Type parameter names (e.g. T, K, V).
    pub type_params: Vec<NameId>,
    /// Interfaces implemented by this type.
    pub implements: Vec<VirImplementation>,
    /// Whether this type is an annotation type.
    pub is_annotation: bool,
    /// Pre-computed base type for Class/Struct types.
    ///
    /// The base TypeId (with empty type args), pre-computed by sema so
    /// codegen can look up without mutable arena access.  Uses sema `TypeId`
    /// (not `VirTypeId`) because codegen callers still operate on `TypeId`.
    pub base_type_id: Option<TypeId>,
    /// Which module this type is declared in.
    pub module: ModuleId,
    /// Whether this type has generic parameters (i.e. `generic_info.is_some()`).
    pub is_generic: bool,
    /// Generic field types translated to `VirTypeId`s.
    ///
    /// From sema `TypeDef::generic_info.field_types`.  Used by
    /// codegen for generic type substitution via `substitute_vir_ids`.
    /// `None` for non-generic types.
    pub generic_field_types: Option<Vec<VirTypeId>>,
    /// Field names as stable `NameId`s for generic field lookup.
    ///
    /// From sema `GenericTypeInfo::field_names`.  Used by
    /// `get_field_slot_and_type_id_cg()` in structs/helpers.rs.
    /// `None` for non-generic types.
    pub generic_field_names: Option<Vec<NameId>>,
}

impl VirTypeDef {
    /// Whether this type has generic type parameters.
    pub fn has_type_params(&self) -> bool {
        !self.type_params.is_empty()
    }

    /// Whether this is a class (heap-allocated, RC-managed).
    pub fn is_class(&self) -> bool {
        self.kind.is_class()
    }

    /// Type kind string for error messages ("class", "struct", etc.).
    pub fn type_kind(&self) -> &'static str {
        self.kind.type_kind_str()
    }
}

// ---------------------------------------------------------------------------
// Field definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a field definition.
///
/// Contains the field name, type, and slot index — everything codegen
/// needs for field access without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirFieldDef {
    /// The sema entity ID for this field.
    pub id: FieldId,
    /// The field name.
    pub name_id: NameId,
    /// Fully qualified field name (e.g. `Point::x`).
    pub full_name_id: NameId,
    /// The type that owns this field.
    pub defining_type: TypeDefId,
    /// The field's VIR type.
    ///
    /// Reliable for all types including generic type parameters.  Interned
    /// into the main VirTypeTable (not a clone), so VirTypeIds are always
    /// valid in the codegen type table.
    pub vir_ty: VirTypeId,
    /// The field's slot index in the type's storage layout.
    pub slot: usize,
    /// Interned symbol for the field name (for name matching during
    /// monomorph rederive without requiring the interner).
    pub symbol: Option<Symbol>,
    /// Pre-computed RC cleanup classification for this field.
    ///
    /// Computed during VIR lowering from the field's `vir_ty` so codegen
    /// can read the tag directly without re-deriving it from the type.
    /// For generic type parameters this defaults to `Value`; codegen
    /// recomputes the tag post-monomorphization for concrete types.
    pub field_type_tag: VirFieldTypeTag,
}

// ---------------------------------------------------------------------------
// Method definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a method definition.
///
/// Contains method name, signature info, and dispatch metadata for
/// codegen without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirMethodDef {
    /// The sema entity ID for this method.
    pub id: MethodId,
    /// The method's short name (e.g. `next`).
    pub name_id: NameId,
    /// Fully qualified method name (e.g. `Iterator::next`).
    pub full_name_id: NameId,
    /// The type that defines this method.
    pub defining_type: TypeDefId,
    /// The sema TypeId for the method signature.
    ///
    /// Used by `method_signature_id()` and heavily in `impl_dispatch.rs` +
    /// `signatures.rs` for `unwrap_function()` calls.  This is a raw sema
    /// TypeId — Phase 3 (TypeArena migration) will convert to VIR-native
    /// types.
    pub signature_id: TypeId,
    /// Whether this method has a default implementation.
    pub has_default: bool,
    /// Whether this is a static method.
    pub is_static: bool,
    /// External binding for this method (if any).
    ///
    /// Contains the native module path and function name for FFI dispatch.
    /// Used by `method_external_binding()`, `is_external_only()`, and
    /// `type_registry.rs` to check `external_binding.is_some()`.
    pub external_binding: Option<VirExternalMethodInfo>,
    /// Whether each parameter has a default expression.
    ///
    /// Index corresponds to parameter index.  Codegen only checks
    /// `is_some()` on the original `param_defaults`, so we store just
    /// the booleans here (the actual AST default expressions are compiled
    /// separately via VIR default init).
    pub has_param_defaults: Vec<bool>,
    /// Method-level type parameters (e.g., `func convert<U>` has `U`).
    ///
    /// Distinct from class type params which are stored on `VirTypeDef`.
    /// Minimal usage in codegen currently but needed for completeness.
    pub method_type_params: Vec<NameId>,
    /// Number of required parameters (without defaults).
    pub required_params: usize,
    /// Parameter names in declaration order (excluding `self`).
    pub param_names: Vec<String>,
    /// Parameter types in declaration order (excluding `self`).
    ///
    /// Translated from the sema signature's param TypeIds to VirTypeIds
    /// during lowering.  Replaces the need to call
    /// `arena.unwrap_function(method_def.signature_id)` in codegen.
    pub param_types: Vec<VirTypeId>,
    /// Return type of this method.
    ///
    /// Translated from the sema signature's return TypeId to a VirTypeId
    /// during lowering.
    pub return_type: VirTypeId,
}

// ---------------------------------------------------------------------------
// Implementation metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for an interface implementation.
///
/// Records which interface a type implements, the type arguments for
/// generic interfaces, and its method bindings.
#[derive(Debug, Clone)]
pub struct VirImplementation {
    /// The interface being implemented.
    pub interface: TypeDefId,
    /// Type arguments for generic interface implementations.
    ///
    /// For example, `implement Iterable<i64> for MyType` would have
    /// `type_args: [VirTypeId::I64]`.  Empty for non-generic interfaces.
    /// Translated from sema `TypeId`s to `VirTypeId`s during lowering.
    pub type_args: Vec<VirTypeId>,
    /// Original sema `TypeId`s for the type arguments.
    ///
    /// Kept temporarily so codegen can build `FxHashMap<NameId, TypeId>`
    /// substitution maps without reaching into `EntityView`.  Will be
    /// removed once Phase 3 converts all codegen callers to `VirTypeId`.
    pub sema_type_args: Vec<TypeId>,
    /// Method bindings for this implementation.
    pub method_bindings: Vec<VirMethodBinding>,
}

/// A single method binding in an implementation block.
#[derive(Debug, Clone)]
pub struct VirMethodBinding {
    /// The method name.
    pub method_name: NameId,
    /// Whether this is a builtin method.
    pub is_builtin: bool,
    /// The return type of the bound method's func_type signature.
    ///
    /// Translated from `func_type.return_type_id` (sema `TypeId`) to
    /// `VirTypeId` during lowering so codegen can read it without the
    /// sema type arena.
    pub return_type: VirTypeId,
    /// The original sema function type (params + return as sema TypeIds).
    ///
    /// Temporary — kept so codegen callers that inspect `func_type.params_id`
    /// and `func_type.return_type_id` can continue to work without reaching
    /// back into `EntityView`.  Will be removed once Phase 3 converts all
    /// codegen callers to VIR-native types.
    pub sema_func_type: FunctionType,
    /// External (native) method binding info, when present.
    ///
    /// Contains the module path and native function name for FFI dispatch.
    /// Migrated from `EntityView::find_method_binding` → `MethodBinding::external_info`.
    pub external_info: Option<VirExternalMethodInfo>,
}

// ---------------------------------------------------------------------------
// Implement block entry (codegen iteration)
// ---------------------------------------------------------------------------

/// VIR-native metadata for a single implement block.
///
/// Captures everything codegen needs to register and compile an implement
/// block without walking AST `ImplementBlock` nodes.  Populated during VIR
/// lowering from sema's `ImplementRegistry` + `EntityRegistry`.
#[derive(Debug, Clone)]
pub struct VirImplementBlockEntry {
    /// The target type definition (e.g. `Point` in `extend Point with Show`).
    pub type_def_id: TypeDefId,
    /// The sema `TypeId` for `self` in this implement block's methods.
    ///
    /// For named types this is the type's base TypeId; for primitives it's
    /// `TypeId::I64` etc.; for arrays it's the canonical array TypeId.
    pub self_type_id: TypeId,
    /// Instance method IDs declared in this implement block (ordered by declaration).
    pub instance_methods: Vec<MethodId>,
    /// Static method IDs declared in this implement block (ordered by declaration).
    pub static_methods: Vec<MethodId>,
    /// The module this implement block belongs to.
    pub module_id: ModuleId,
}

// ---------------------------------------------------------------------------
// Global variable definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a global variable definition.
///
/// Contains the global's name, type, and module — everything codegen
/// needs for global variable access without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirGlobalDef {
    /// The sema entity ID for this global.
    pub id: GlobalId,
    /// The global's name.
    pub name_id: NameId,
    /// The global's VIR type (translated from sema `TypeId` during lowering).
    pub vir_ty: VirTypeId,
    /// The module this global is declared in.
    pub module_id: ModuleId,
}

// ---------------------------------------------------------------------------
// Function definition metadata
// ---------------------------------------------------------------------------

/// VIR-native metadata for a free function definition.
///
/// Contains the function's name, signature, module, and auxiliary info
/// (defaults, generics, generator element type) — everything codegen
/// needs for function dispatch without reaching back into sema.
#[derive(Debug, Clone)]
pub struct VirFunctionDef {
    /// The sema entity ID for this function.
    pub id: FunctionId,
    /// The function's short name (e.g. `sin`).
    pub name_id: NameId,
    /// Fully qualified function name (e.g. `math::sin`).
    pub full_name_id: NameId,
    /// The module this function is declared in.
    pub module: ModuleId,
    /// Parameter types in declaration order.
    ///
    /// Translated from the sema signature's param TypeIds to VirTypeIds
    /// during lowering.
    pub param_types: Vec<VirTypeId>,
    /// Return type of this function.
    ///
    /// Translated from the sema signature's return TypeId to a VirTypeId
    /// during lowering.
    pub return_type: VirTypeId,
    /// Parameter names in declaration order.
    pub param_names: Vec<String>,
    /// Number of required parameters (without defaults).
    /// Parameters 0..required_params are required, rest have defaults.
    pub required_params: usize,
    /// Which parameters have default expressions.
    ///
    /// Index corresponds to parameter index.  Codegen only needs to know
    /// whether a default exists (not the expression itself), so we store
    /// booleans rather than cloning AST nodes.
    pub has_defaults: Vec<bool>,
    /// Whether this function is generic (has type parameters).
    pub is_generic: bool,
    /// Whether this function is an external (FFI) function.
    pub is_external: bool,
    /// If this function is a generator, the element type `T` of its
    /// `Iterator<T>` return type.  Codegen reads this instead of walking
    /// the AST.
    pub generator_element_type: Option<VirTypeId>,

    // ----- Temporary sema TypeId copies (until Phase 3 VIR migration) -----
    /// Original sema parameter TypeIds, for callers that still build
    /// Cranelift signatures via `build_signature_from_type_ids`.
    pub sema_param_types: Vec<TypeId>,
    /// Original sema return TypeId, for callers that still register
    /// return types in FunctionRegistry.
    pub sema_return_type: TypeId,
    /// Original sema generator element TypeId, for callers that still
    /// call `lookup_runtime_iterator` on the sema TypeArena.
    pub sema_generator_element_type: Option<TypeId>,
}

// ---------------------------------------------------------------------------
// VirEntityMetadata — the top-level container
// ---------------------------------------------------------------------------

/// Complete entity metadata for a VIR program.
///
/// Replaces `EntityView` as the codegen-accessible source of type, field,
/// and method metadata.  Populated once during VIR lowering from sema's
/// `EntityRegistry`.
#[derive(Debug, Clone, Default)]
pub struct VirEntityMetadata {
    /// Type definitions keyed by `TypeDefId`.
    type_defs: FxHashMap<TypeDefId, VirTypeDef>,
    /// Field definitions keyed by `FieldId`.
    field_defs: FxHashMap<FieldId, VirFieldDef>,
    /// Method definitions keyed by `MethodId`.
    method_defs: FxHashMap<MethodId, VirMethodDef>,
    /// Global variable definitions keyed by `GlobalId`.
    global_defs: FxHashMap<GlobalId, VirGlobalDef>,
    /// Reverse lookup: `NameId` → `GlobalId`.
    global_by_name: FxHashMap<NameId, GlobalId>,
    /// Function definitions keyed by `FunctionId`.
    function_defs: FxHashMap<FunctionId, VirFunctionDef>,
    /// Reverse lookup: `NameId` → `FunctionId`.
    ///
    /// Mirrors `EntityRegistry::function_by_name_map` / `EntityView::function_by_name`.
    function_by_name: FxHashMap<NameId, FunctionId>,
    /// Reverse lookup: `NameId` → `TypeDefId`.
    ///
    /// Mirrors `EntityRegistry::type_by_name_map` / `EntityView::type_by_name`.
    /// Used by `try_type_def_id()` in codegen to resolve a type definition
    /// from its canonical name.
    type_by_name: FxHashMap<NameId, TypeDefId>,
    /// The `NameId` for the built-in `Array` type, used for array implement
    /// dispatch (e.g. `extend [T] with Iterable<T>`).
    ///
    /// Mirrors `EntityRegistry::array_name_id()` / `EntityView::array_name`.
    array_name_id: Option<NameId>,
    /// Short-name (last segment) → `TypeDefId`s lookup.
    ///
    /// Built eagerly during VIR lowering from all type definitions.
    /// Maps a type's short name (e.g. `"Point"` from `mymod::Point`) to
    /// the list of `TypeDefId`s that share that short name.
    ///
    /// Mirrors `EntityView::short_name_map`.
    short_name_map: FxHashMap<String, Vec<TypeDefId>>,
    /// Pre-computed implement-registry type names for primitive, Range, and
    /// Handle types.
    ///
    /// Maps the sema `TypeId` (interned in the type arena during sema) to
    /// the canonical `NameId` used by the implement registry.  Only covers
    /// the finite set of simple types (14 primitives + Range + Handle = 16
    /// entries); Class, Struct, and Array types are resolved dynamically via
    /// `type_name_id()` and `array_name_id()`.
    ///
    /// Populated during VIR lowering in `build_entity_metadata`.  Queried
    /// by `AnalyzedProgram::impl_type_name_id_from_type_id` as a fast-path
    /// before falling back to TypeArena inspection.
    impl_type_names: FxHashMap<TypeId, NameId>,
    /// Pre-computed index: `(ModuleId, VirTypeDefKind)` → list of `TypeDefId`s.
    ///
    /// Populated eagerly during `insert_type_def()` so that
    /// `module_type_defs_by_kind()` is O(1) instead of scanning all type defs.
    type_defs_by_module_kind: FxHashMap<(ModuleId, VirTypeDefKind), Vec<TypeDefId>>,
    /// Implement block entries for the main program.
    ///
    /// Ordered by declaration order.  Codegen iterates these instead of
    /// walking AST `Decl::Implement` nodes.
    implement_blocks: Vec<VirImplementBlockEntry>,
    /// Implement block entries for imported modules.
    ///
    /// Keyed by module path string.  Each module's entries are ordered by
    /// declaration order within that module.
    module_implement_blocks: FxHashMap<String, Vec<VirImplementBlockEntry>>,
}

// ---------------------------------------------------------------------------
// Mutation (population during lowering)
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Create an empty metadata container.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a type definition.
    ///
    /// Also updates the `type_by_name` reverse-lookup map.
    pub fn insert_type_def(&mut self, type_def: VirTypeDef) {
        self.type_by_name.insert(type_def.name_id, type_def.id);
        self.type_defs_by_module_kind
            .entry((type_def.module, type_def.kind))
            .or_default()
            .push(type_def.id);
        self.type_defs.insert(type_def.id, type_def);
    }

    /// Register a field definition.
    pub fn insert_field_def(&mut self, field_def: VirFieldDef) {
        self.field_defs.insert(field_def.id, field_def);
    }

    /// Register a method definition.
    pub fn insert_method_def(&mut self, method_def: VirMethodDef) {
        self.method_defs.insert(method_def.id, method_def);
    }

    /// Set the built-in array type `NameId`.
    pub fn set_array_name_id(&mut self, name_id: NameId) {
        self.array_name_id = Some(name_id);
    }

    /// Insert an entry into the short-name lookup map.
    ///
    /// Called during VIR lowering for each type definition whose `NameId`
    /// has a resolvable last segment.
    pub fn insert_short_name(&mut self, short_name: String, type_def_id: TypeDefId) {
        self.short_name_map
            .entry(short_name)
            .or_default()
            .push(type_def_id);
    }

    /// Register a function definition.
    ///
    /// Also updates the `function_by_name` reverse-lookup map using
    /// the function's `name_id`.  For additional name mappings (e.g.
    /// `full_name_id`), call [`insert_function_by_name`] separately.
    pub fn insert_function_def(&mut self, function_def: VirFunctionDef) {
        self.function_by_name
            .insert(function_def.name_id, function_def.id);
        self.function_defs.insert(function_def.id, function_def);
    }

    /// Register an additional `NameId` → `FunctionId` mapping.
    ///
    /// The sema `EntityRegistry` stores both `name_id` and `full_name_id`
    /// entries in its function-by-name map.  `insert_function_def` only
    /// inserts by `name_id`, so the lowering pass calls this to mirror
    /// the full registry map.
    pub fn insert_function_by_name(&mut self, name_id: NameId, function_id: FunctionId) {
        self.function_by_name.insert(name_id, function_id);
    }

    /// Register a global variable definition.
    pub fn insert_global_def(&mut self, global_def: VirGlobalDef) {
        self.global_by_name
            .insert(global_def.name_id, global_def.id);
        self.global_defs.insert(global_def.id, global_def);
    }

    /// Register an implement-registry type name for a sema `TypeId`.
    ///
    /// Called during VIR lowering for each primitive type, Range, and Handle
    /// to pre-compute the `TypeId → NameId` mapping that
    /// `impl_type_name_id_from_type_id` uses as a fast-path.
    pub fn insert_impl_type_name(&mut self, type_id: TypeId, name_id: NameId) {
        self.impl_type_names.insert(type_id, name_id);
    }

    /// Register an implement block entry for the main program.
    pub fn insert_implement_block(&mut self, entry: VirImplementBlockEntry) {
        self.implement_blocks.push(entry);
    }

    /// Register an implement block entry for an imported module.
    pub fn insert_module_implement_block(
        &mut self,
        module_path: String,
        entry: VirImplementBlockEntry,
    ) {
        self.module_implement_blocks
            .entry(module_path)
            .or_default()
            .push(entry);
    }

    /// Set all module implement block entries at once.
    ///
    /// Used on cache hit to inject cached module implement block entries
    /// into freshly-built entity metadata, skipping the expensive
    /// `populate_implement_block_entries_modules` pass.
    pub fn set_module_implement_blocks(
        &mut self,
        blocks: FxHashMap<String, Vec<VirImplementBlockEntry>>,
    ) {
        self.module_implement_blocks = blocks;
    }

    /// Take ownership of the module implement block entries.
    ///
    /// Returns the full map, leaving an empty map in its place.
    /// Used to extract module implement blocks for caching without cloning.
    pub fn take_module_implement_blocks(
        &mut self,
    ) -> FxHashMap<String, Vec<VirImplementBlockEntry>> {
        std::mem::take(&mut self.module_implement_blocks)
    }
}

// ---------------------------------------------------------------------------
// Type queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a type definition by ID.
    pub fn get_type_def(&self, id: TypeDefId) -> Option<&VirTypeDef> {
        self.type_defs.get(&id)
    }

    /// Return the kind of a type definition.
    pub fn type_def_kind(&self, id: TypeDefId) -> Option<VirTypeDefKind> {
        self.type_defs.get(&id).map(|td| td.kind)
    }

    /// Return field IDs declared on a type.
    pub fn fields_on_type(&self, id: TypeDefId) -> Option<&[FieldId]> {
        self.type_defs.get(&id).map(|td| td.fields.as_slice())
    }

    /// Return instance method IDs declared on a type.
    pub fn methods_on_type(&self, id: TypeDefId) -> Option<&[MethodId]> {
        self.type_defs.get(&id).map(|td| td.methods.as_slice())
    }

    /// Return static method IDs declared on a type.
    pub fn static_methods_on_type(&self, id: TypeDefId) -> Option<&[MethodId]> {
        self.type_defs
            .get(&id)
            .map(|td| td.static_methods.as_slice())
    }

    /// Return interfaces implemented by a type.
    pub fn implemented_interfaces(&self, id: TypeDefId) -> Vec<TypeDefId> {
        self.type_defs
            .get(&id)
            .map(|td| td.implements.iter().map(|i| i.interface).collect())
            .unwrap_or_default()
    }

    /// Return the VIR type arguments for a specific interface implementation.
    ///
    /// For example, if `MyType` implements `Iterable<i64>`, calling
    /// `implementation_type_args(my_type_id, iterable_id)` returns
    /// `&[VirTypeId::I64]`.  Returns an empty slice if the type does not
    /// implement the given interface or the implementation is non-generic.
    pub fn implementation_type_args(
        &self,
        type_def_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> &[VirTypeId] {
        let Some(td) = self.type_defs.get(&type_def_id) else {
            return &[];
        };
        for impl_ in &td.implements {
            if impl_.interface == interface_id {
                return &impl_.type_args;
            }
        }
        &[]
    }

    /// Return the original sema `TypeId` type arguments for a specific
    /// interface implementation.
    ///
    /// Temporary accessor — will be removed once Phase 3 converts codegen
    /// callers to `VirTypeId`.
    pub fn implementation_sema_type_args(
        &self,
        type_def_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> &[TypeId] {
        let Some(td) = self.type_defs.get(&type_def_id) else {
            return &[];
        };
        for impl_ in &td.implements {
            if impl_.interface == interface_id {
                return &impl_.sema_type_args;
            }
        }
        &[]
    }

    /// Return type parameter names for a type.
    pub fn type_params(&self, id: TypeDefId) -> Option<&[NameId]> {
        self.type_defs.get(&id).map(|td| td.type_params.as_slice())
    }

    /// Return the canonical name of a type.
    pub fn type_name_id(&self, id: TypeDefId) -> Option<NameId> {
        self.type_defs.get(&id).map(|td| td.name_id)
    }

    /// Return the extends list (parent interfaces) for a type.
    pub fn type_extends(&self, id: TypeDefId) -> Option<&[TypeDefId]> {
        self.type_defs.get(&id).map(|td| td.extends.as_slice())
    }

    /// Whether a type is an annotation type.
    pub fn is_annotation(&self, id: TypeDefId) -> bool {
        self.type_defs.get(&id).is_some_and(|td| td.is_annotation)
    }

    /// Return the number of registered type definitions.
    pub fn type_def_count(&self) -> usize {
        self.type_defs.len()
    }

    /// Resolve a `TypeDefId` by its canonical `NameId`.
    ///
    /// Mirrors `EntityView::type_by_name` / `AnalyzedProgram::try_type_def_id`.
    pub fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        self.type_by_name.get(&name_id).copied()
    }

    /// Return the `NameId` for the built-in array type.
    ///
    /// Used by array implement dispatch (e.g. `extend [T] with Iterable<T>`).
    /// Mirrors `EntityView::array_name_id`.
    pub fn array_name_id(&self) -> Option<NameId> {
        self.array_name_id
    }

    /// Look up a pre-computed implement-registry type name for a sema `TypeId`.
    ///
    /// Returns the canonical `NameId` for primitive types, Range, and Handle
    /// that was pre-computed during VIR lowering.  Returns `None` for
    /// Class, Struct, Array, and other types that need dynamic resolution
    /// via `type_name_id()` or `array_name_id()`.
    pub fn impl_type_name(&self, type_id: TypeId) -> Option<NameId> {
        self.impl_type_names.get(&type_id).copied()
    }

    /// Find a type by its short (last-segment) name.
    ///
    /// Returns the first `TypeDefId` registered under the given short name.
    /// Mirrors `EntityView::type_by_short_name`.
    pub fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.short_name_map
            .get(short_name)
            .and_then(|ids| ids.first().copied())
    }

    /// Return all `TypeDefId`s registered under a short (last-segment) name.
    ///
    /// Returns `None` if no types are registered under the given name.
    pub fn types_by_short_name(&self, short_name: &str) -> Option<&[TypeDefId]> {
        self.short_name_map
            .get(short_name)
            .map(|ids| ids.as_slice())
    }
}

// ---------------------------------------------------------------------------
// Field queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a field definition by ID.
    pub fn get_field_def(&self, id: FieldId) -> Option<&VirFieldDef> {
        self.field_defs.get(&id)
    }

    /// Return the VIR type of a field.
    pub fn field_vir_type(&self, id: FieldId) -> Option<VirTypeId> {
        self.field_defs.get(&id).map(|fd| fd.vir_ty)
    }

    /// Return the slot index of a field.
    pub fn field_slot(&self, id: FieldId) -> Option<usize> {
        self.field_defs.get(&id).map(|fd| fd.slot)
    }

    /// Return the name of a field.
    pub fn field_name_id(&self, id: FieldId) -> Option<NameId> {
        self.field_defs.get(&id).map(|fd| fd.name_id)
    }

    /// Return the defining type of a field.
    pub fn field_defining_type(&self, id: FieldId) -> Option<TypeDefId> {
        self.field_defs.get(&id).map(|fd| fd.defining_type)
    }

    /// Return the number of registered field definitions.
    pub fn field_def_count(&self) -> usize {
        self.field_defs.len()
    }

    /// Find a field on a type by its interned `Symbol`.
    ///
    /// Iterates the type's field list and returns the first `VirFieldDef`
    /// whose `symbol` matches.  Returns `None` if the type has no fields,
    /// is not registered, or no field matches the symbol.
    pub fn find_field_by_symbol(
        &self,
        type_def_id: TypeDefId,
        target: Symbol,
    ) -> Option<&VirFieldDef> {
        let td = self.type_defs.get(&type_def_id)?;
        for &field_id in &td.fields {
            if let Some(fd) = self.field_defs.get(&field_id)
                && fd.symbol == Some(target)
            {
                return Some(fd);
            }
        }
        None
    }
}

// ---------------------------------------------------------------------------
// Method queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a method definition by ID.
    pub fn get_method_def(&self, id: MethodId) -> Option<&VirMethodDef> {
        self.method_defs.get(&id)
    }

    /// Return the full name of a method.
    pub fn method_full_name_id(&self, id: MethodId) -> Option<NameId> {
        self.method_defs.get(&id).map(|md| md.full_name_id)
    }

    /// Return whether a method has a default implementation.
    pub fn method_has_default(&self, id: MethodId) -> Option<bool> {
        self.method_defs.get(&id).map(|md| md.has_default)
    }

    /// Return the defining type of a method.
    pub fn method_defining_type(&self, id: MethodId) -> Option<TypeDefId> {
        self.method_defs.get(&id).map(|md| md.defining_type)
    }

    /// Return the sema signature TypeId for a method.
    pub fn method_signature_id(&self, id: MethodId) -> Option<TypeId> {
        self.method_defs.get(&id).map(|md| md.signature_id)
    }

    /// Return the external binding for a method, if any.
    pub fn method_external_binding(&self, id: MethodId) -> Option<&VirExternalMethodInfo> {
        self.method_defs
            .get(&id)
            .and_then(|md| md.external_binding.as_ref())
    }

    /// Return whether a method parameter has a default expression.
    pub fn method_has_param_default(&self, id: MethodId, param_idx: usize) -> Option<bool> {
        self.method_defs
            .get(&id)
            .and_then(|md| md.has_param_defaults.get(param_idx).copied())
    }

    /// Return the method-level type parameters.
    pub fn method_type_params(&self, id: MethodId) -> Option<&[NameId]> {
        self.method_defs
            .get(&id)
            .map(|md| md.method_type_params.as_slice())
    }

    /// Return the parameter types of a method.
    pub fn method_param_types(&self, id: MethodId) -> Option<&[VirTypeId]> {
        self.method_defs
            .get(&id)
            .map(|md| md.param_types.as_slice())
    }

    /// Return the return type of a method.
    pub fn method_return_type(&self, id: MethodId) -> Option<VirTypeId> {
        self.method_defs.get(&id).map(|md| md.return_type)
    }

    /// Return the number of registered method definitions.
    pub fn method_def_count(&self) -> usize {
        self.method_defs.len()
    }
}

// ---------------------------------------------------------------------------
// Global queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a global variable definition by ID.
    pub fn get_global_def(&self, id: GlobalId) -> Option<&VirGlobalDef> {
        self.global_defs.get(&id)
    }

    /// Look up a global's `GlobalId` by its `NameId`.
    pub fn global_by_name(&self, name_id: NameId) -> Option<GlobalId> {
        self.global_by_name.get(&name_id).copied()
    }

    /// Return whether a global exists for the given `NameId`.
    pub fn has_global(&self, name_id: NameId) -> bool {
        self.global_by_name.contains_key(&name_id)
    }

    /// Return the VIR type of a global variable.
    pub fn global_vir_type(&self, id: GlobalId) -> Option<VirTypeId> {
        self.global_defs.get(&id).map(|gd| gd.vir_ty)
    }

    /// Return the number of registered global definitions.
    pub fn global_def_count(&self) -> usize {
        self.global_defs.len()
    }
}

// ---------------------------------------------------------------------------
// Function queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Look up a function definition by ID.
    pub fn get_function_def(&self, id: FunctionId) -> Option<&VirFunctionDef> {
        self.function_defs.get(&id)
    }

    /// Look up a function's `FunctionId` by its `NameId`.
    pub fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        self.function_by_name.get(&name_id).copied()
    }

    /// Return whether a function exists for the given `NameId`.
    pub fn has_function(&self, name_id: NameId) -> bool {
        self.function_by_name.contains_key(&name_id)
    }

    /// Return the number of registered function definitions.
    pub fn function_def_count(&self) -> usize {
        self.function_defs.len()
    }

    /// Return function definitions declared in a specific module.
    ///
    /// Iterates all registered function definitions and returns those whose
    /// `module` matches the given `module_id`.  Results are collected into a
    /// `Vec` for borrow-safe iteration.
    pub fn module_function_defs(&self, module_id: ModuleId) -> Vec<&VirFunctionDef> {
        self.function_defs
            .values()
            .filter(|fd| fd.module == module_id)
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Module-level type iteration
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Return type definitions declared in a specific module with the given kind.
    ///
    /// Uses a pre-computed `(ModuleId, VirTypeDefKind)` → `Vec<TypeDefId>`
    /// index built during `insert_type_def()` for O(1) lookup.
    pub fn module_type_defs_by_kind(
        &self,
        module_id: ModuleId,
        kind: VirTypeDefKind,
    ) -> Vec<&VirTypeDef> {
        self.type_defs_by_module_kind
            .get(&(module_id, kind))
            .map(|ids| ids.iter().filter_map(|id| self.type_defs.get(id)).collect())
            .unwrap_or_default()
    }
}

// ---------------------------------------------------------------------------
// Implement block queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Return implement block entries for the main program.
    pub fn implement_blocks(&self) -> &[VirImplementBlockEntry] {
        &self.implement_blocks
    }

    /// Return implement block entries for a specific module.
    pub fn module_implement_blocks(&self, module_path: &str) -> &[VirImplementBlockEntry] {
        self.module_implement_blocks
            .get(module_path)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Iterate all module implement block entries with their module paths.
    pub fn all_module_implement_blocks(
        &self,
    ) -> impl Iterator<Item = (&str, &[VirImplementBlockEntry])> {
        self.module_implement_blocks
            .iter()
            .map(|(path, entries)| (path.as_str(), entries.as_slice()))
    }
}

// ---------------------------------------------------------------------------
// Composite queries
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Return interface method IDs in deterministic vtable slot order.
    ///
    /// Recursively collects methods from parent interfaces first, then own
    /// methods.  Skips duplicate method names from parent interfaces.
    pub fn interface_methods_ordered(&self, interface_id: TypeDefId) -> Vec<MethodId> {
        let mut methods = Vec::new();
        let mut seen_interfaces = std::collections::HashSet::new();
        let mut seen_methods = std::collections::HashSet::new();
        self.collect_interface_methods_inner(
            interface_id,
            &mut methods,
            &mut seen_interfaces,
            &mut seen_methods,
        );
        methods
    }

    /// Recursive helper: collect interface methods in vtable order.
    fn collect_interface_methods_inner(
        &self,
        interface_id: TypeDefId,
        methods: &mut Vec<MethodId>,
        seen_interfaces: &mut std::collections::HashSet<TypeDefId>,
        seen_methods: &mut std::collections::HashSet<NameId>,
    ) {
        if !seen_interfaces.insert(interface_id) {
            return;
        }
        let Some(td) = self.type_defs.get(&interface_id) else {
            return;
        };
        // Parent interfaces first
        for &parent in &td.extends {
            self.collect_interface_methods_inner(parent, methods, seen_interfaces, seen_methods);
        }
        // Then own methods (skip already-seen from parents)
        for &method_id in &td.methods {
            if let Some(md) = self.method_defs.get(&method_id)
                && seen_methods.insert(md.name_id)
            {
                methods.push(method_id);
            }
        }
    }

    /// Find an instance method on a type by method `NameId`.
    ///
    /// Searches the type's instance method list in reverse order so that
    /// later-registered methods (e.g. interface defaults copied onto the
    /// implementing type) shadow earlier entries with the same `name_id`,
    /// matching the `HashMap` last-write-wins semantics of the sema
    /// `methods_by_type` map.
    pub fn find_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        let td = self.type_defs.get(&type_def_id)?;
        for &mid in td.methods.iter().rev() {
            if let Some(md) = self.method_defs.get(&mid)
                && md.name_id == method_name_id
            {
                return Some(mid);
            }
        }
        None
    }

    /// Find a static method on a type by method `NameId`.
    ///
    /// Searches in reverse order for the same reason as
    /// [`find_method_on_type`](Self::find_method_on_type).
    pub fn find_static_method_on_type(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        let td = self.type_defs.get(&type_def_id)?;
        for &mid in td.static_methods.iter().rev() {
            if let Some(md) = self.method_defs.get(&mid)
                && md.name_id == method_name_id
            {
                return Some(mid);
            }
        }
        None
    }

    /// Find a method binding for a type's interface implementation by method
    /// name.
    ///
    /// Searches all implementation blocks on the type, returning the first
    /// `VirMethodBinding` whose `method_name` matches.  Mirrors
    /// `EntityView::find_method_binding` but operates on VIR-native data.
    pub fn find_method_binding(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<&VirMethodBinding> {
        let td = self.type_defs.get(&type_def_id)?;
        for impl_ in &td.implements {
            for binding in &impl_.method_bindings {
                if binding.method_name == method_name_id {
                    return Some(binding);
                }
            }
        }
        None
    }

    /// Check if a type is a functional interface (single abstract method, no fields).
    ///
    /// Returns `Some(method_id)` when the type has no fields and exactly one
    /// non-default method, `None` otherwise.
    pub fn is_functional(&self, type_def_id: TypeDefId) -> Option<MethodId> {
        let td = self.type_defs.get(&type_def_id)?;
        if !td.fields.is_empty() {
            return None;
        }
        let abstract_methods: Vec<MethodId> = td
            .methods
            .iter()
            .copied()
            .filter(|&mid| self.method_defs.get(&mid).is_some_and(|md| !md.has_default))
            .collect();
        if abstract_methods.len() == 1 {
            Some(abstract_methods[0])
        } else {
            None
        }
    }

    /// Resolve a type definition by short name, matching the sema
    /// `resolve_type_str_or_interface` resolution chain.
    ///
    /// Uses the identity-layer `Resolver` for scoped NameId lookup, then
    /// maps through `type_by_name`.  Falls back to short-name search
    /// across all registered types (interfaces, classes, structs, sentinels).
    ///
    /// Mirrors `EntityView::resolve_type_def_by_str`.
    pub fn resolve_type_def_by_str(
        &self,
        interner: &Interner,
        names: &NameTable,
        module_id: ModuleId,
        name: &str,
    ) -> Option<TypeDefId> {
        // Sentinel priority: "nil" and "Done" must resolve to their sentinel
        // TypeDefId, not a primitive or other type with the same short name.
        if (name == "nil" || name == "Done")
            && let Some(id) = self.sentinel_by_short_name(name, names)
        {
            return Some(id);
        }
        // Scoped NameId resolution (primitives, current module, builtin).
        let resolver = Resolver::new(interner, names, module_id, &[]);
        if let Some(name_id) = resolver.resolve_str(name)
            && let Some(id) = self.type_by_name(name_id)
        {
            return Some(id);
        }
        // Short-name fallback (covers sentinel, interface, class, struct).
        self.type_by_short_name(name)
    }

    /// Check if all methods on a type have external bindings (no vole-native
    /// methods).
    ///
    /// Returns `true` when the type has at least one method and every method
    /// has an `external_binding` and is not a default method.  Returns `false`
    /// for types with no methods or any non-external method.
    ///
    /// Mirrors `EntityView::is_external_only`.
    pub fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        let Some(td) = self.type_defs.get(&type_def_id) else {
            return false;
        };
        if td.methods.is_empty() {
            return false;
        }
        td.methods.iter().all(|&method_id| {
            self.method_defs
                .get(&method_id)
                .is_some_and(|md| md.external_binding.is_some() && !md.has_default)
        })
    }

    /// Find a sentinel type by its short (last-segment) name.
    fn sentinel_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        self.short_name_map.get(short_name).and_then(|ids| {
            ids.iter().copied().find(|&id| {
                let Some(td) = self.type_defs.get(&id) else {
                    return false;
                };
                td.kind.is_sentinel()
                    && names.last_segment_str(td.name_id).as_deref() == Some(short_name)
            })
        })
    }
}

// ---------------------------------------------------------------------------
// Crate-internal mutable access for VirTypeId remapping
// ---------------------------------------------------------------------------

impl VirEntityMetadata {
    /// Mutable access to type definitions (for remapping).
    pub(crate) fn type_defs_mut(&mut self) -> &mut FxHashMap<TypeDefId, VirTypeDef> {
        &mut self.type_defs
    }

    /// Mutable access to field definitions (for remapping).
    pub(crate) fn field_defs_mut(&mut self) -> &mut FxHashMap<FieldId, VirFieldDef> {
        &mut self.field_defs
    }

    /// Mutable access to method definitions (for remapping).
    pub(crate) fn method_defs_mut(&mut self) -> &mut FxHashMap<MethodId, VirMethodDef> {
        &mut self.method_defs
    }

    /// Mutable access to global definitions (for remapping).
    pub(crate) fn global_defs_mut(&mut self) -> &mut FxHashMap<GlobalId, VirGlobalDef> {
        &mut self.global_defs
    }

    /// Mutable access to function definitions (for remapping).
    pub(crate) fn function_defs_mut(&mut self) -> &mut FxHashMap<FunctionId, VirFunctionDef> {
        &mut self.function_defs
    }
}

// ---------------------------------------------------------------------------
// Unit tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_type_def_id(n: u32) -> TypeDefId {
        TypeDefId::new(n)
    }

    fn make_field_id(n: u32) -> FieldId {
        FieldId::new(n)
    }

    fn make_method_id(n: u32) -> MethodId {
        MethodId::new(n)
    }

    fn make_name_id(n: u32) -> NameId {
        NameId::new_for_test(n)
    }

    fn make_global_id(n: u32) -> GlobalId {
        GlobalId::new(n)
    }

    fn make_function_id(n: u32) -> FunctionId {
        FunctionId::new(n)
    }

    fn make_module_id(n: u32) -> ModuleId {
        ModuleId::new(n)
    }

    #[test]
    fn empty_metadata() {
        let meta = VirEntityMetadata::new();
        assert_eq!(meta.type_def_count(), 0);
        assert_eq!(meta.field_def_count(), 0);
        assert_eq!(meta.method_def_count(), 0);
        assert_eq!(meta.global_def_count(), 0);
        assert_eq!(meta.function_def_count(), 0);
    }

    #[test]
    fn insert_and_query_type_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let field_id = make_field_id(10);
        let method_id = make_method_id(20);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![field_id],
            field_types: vec![VirTypeId::I64],
            methods: vec![method_id],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![make_name_id(200)],
            implements: vec![VirImplementation {
                interface: make_type_def_id(2),
                type_args: vec![VirTypeId::I64],
                sema_type_args: vec![TypeId::I64],
                method_bindings: vec![],
            }],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert_eq!(meta.type_def_count(), 1);

        let td = meta.get_type_def(id).expect("should find type def");
        assert_eq!(td.kind, VirTypeDefKind::Class);
        assert_eq!(td.fields, vec![field_id]);
        assert_eq!(td.methods, vec![method_id]);

        assert_eq!(meta.type_def_kind(id), Some(VirTypeDefKind::Class));
        assert_eq!(meta.fields_on_type(id), Some(&[field_id][..]));
        assert_eq!(meta.methods_on_type(id), Some(&[method_id][..]));
        assert_eq!(meta.type_name_id(id), Some(make_name_id(100)));
        assert_eq!(meta.type_params(id), Some(&[make_name_id(200)][..]));
        assert_eq!(meta.implemented_interfaces(id), vec![make_type_def_id(2)]);
        assert_eq!(
            meta.implementation_type_args(id, make_type_def_id(2)),
            &[VirTypeId::I64]
        );
        assert_eq!(
            meta.implementation_sema_type_args(id, make_type_def_id(2)),
            &[TypeId::I64]
        );
        assert!(!meta.is_annotation(id));
    }

    #[test]
    fn insert_and_query_field_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_field_id(5);

        meta.insert_field_def(VirFieldDef {
            id,
            name_id: make_name_id(50),
            full_name_id: make_name_id(51),
            defining_type: make_type_def_id(1),
            vir_ty: VirTypeId::I64,
            slot: 3,
            symbol: None,
            field_type_tag: VirFieldTypeTag::Value,
        });

        assert_eq!(meta.field_def_count(), 1);

        let fd = meta.get_field_def(id).expect("should find field def");
        assert_eq!(fd.slot, 3);
        assert_eq!(fd.vir_ty, VirTypeId::I64);

        assert_eq!(meta.field_vir_type(id), Some(VirTypeId::I64));
        assert_eq!(meta.field_slot(id), Some(3));
        assert_eq!(meta.field_name_id(id), Some(make_name_id(50)));
        assert_eq!(meta.field_defining_type(id), Some(make_type_def_id(1)));
    }

    #[test]
    fn insert_and_query_method_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_method_id(7);

        meta.insert_method_def(VirMethodDef {
            id,
            name_id: make_name_id(70),
            full_name_id: make_name_id(71),
            defining_type: make_type_def_id(2),
            signature_id: TypeId::I64,
            has_default: true,
            is_static: false,
            external_binding: Some(VirExternalMethodInfo {
                module_path: make_name_id(80),
                native_name: make_name_id(81),
            }),
            has_param_defaults: vec![false, true],
            method_type_params: vec![make_name_id(90)],
            required_params: 2,
            param_names: vec!["x".into(), "y".into()],
            param_types: vec![VirTypeId::I64, VirTypeId::STRING],
            return_type: VirTypeId::BOOL,
        });

        assert_eq!(meta.method_def_count(), 1);

        let md = meta.get_method_def(id).expect("should find method def");
        assert!(md.has_default);
        assert!(!md.is_static);
        assert_eq!(md.required_params, 2);
        assert_eq!(md.param_names, vec!["x", "y"]);
        assert_eq!(md.param_types, vec![VirTypeId::I64, VirTypeId::STRING]);
        assert_eq!(md.return_type, VirTypeId::BOOL);

        assert_eq!(meta.method_full_name_id(id), Some(make_name_id(71)));
        assert_eq!(meta.method_has_default(id), Some(true));
        assert_eq!(meta.method_defining_type(id), Some(make_type_def_id(2)));
        assert_eq!(meta.method_signature_id(id), Some(TypeId::I64));
        assert_eq!(
            meta.method_external_binding(id),
            Some(&VirExternalMethodInfo {
                module_path: make_name_id(80),
                native_name: make_name_id(81),
            })
        );
        assert_eq!(meta.method_has_param_default(id, 0), Some(false));
        assert_eq!(meta.method_has_param_default(id, 1), Some(true));
        assert_eq!(meta.method_type_params(id), Some(&[make_name_id(90)][..]));
        assert_eq!(
            meta.method_param_types(id),
            Some(&[VirTypeId::I64, VirTypeId::STRING][..])
        );
        assert_eq!(meta.method_return_type(id), Some(VirTypeId::BOOL));
    }

    #[test]
    fn missing_lookups_return_none() {
        let meta = VirEntityMetadata::new();
        assert!(meta.get_type_def(make_type_def_id(99)).is_none());
        assert!(meta.get_field_def(make_field_id(99)).is_none());
        assert!(meta.get_method_def(make_method_id(99)).is_none());
        assert!(meta.get_function_def(make_function_id(99)).is_none());
        assert!(meta.type_def_kind(make_type_def_id(99)).is_none());
        assert!(meta.field_vir_type(make_field_id(99)).is_none());
        assert!(meta.method_full_name_id(make_method_id(99)).is_none());
        assert!(meta.method_param_types(make_method_id(99)).is_none());
        assert!(meta.method_return_type(make_method_id(99)).is_none());
        assert!(meta.implemented_interfaces(make_type_def_id(99)).is_empty());
        assert!(
            meta.implementation_type_args(make_type_def_id(99), make_type_def_id(1))
                .is_empty()
        );
        assert!(
            meta.implementation_sema_type_args(make_type_def_id(99), make_type_def_id(1))
                .is_empty()
        );
        assert!(meta.function_by_name(make_name_id(99)).is_none());
        assert!(!meta.has_function(make_name_id(99)));
    }

    #[test]
    fn type_def_kind_predicates() {
        assert!(VirTypeDefKind::Sentinel.is_sentinel());
        assert!(!VirTypeDefKind::Class.is_sentinel());

        assert!(VirTypeDefKind::Class.is_class_struct_or_sentinel());
        assert!(VirTypeDefKind::Struct.is_class_struct_or_sentinel());
        assert!(VirTypeDefKind::Sentinel.is_class_struct_or_sentinel());
        assert!(!VirTypeDefKind::Interface.is_class_struct_or_sentinel());

        assert!(VirTypeDefKind::Interface.is_interface());
        assert!(!VirTypeDefKind::Class.is_interface());
    }

    #[test]
    fn annotation_type() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(42);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(420),
            kind: VirTypeDefKind::Struct,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: true,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert!(meta.is_annotation(id));
    }

    #[test]
    fn interface_with_extends() {
        let mut meta = VirEntityMetadata::new();
        let parent = make_type_def_id(1);
        let child = make_type_def_id(2);

        meta.insert_type_def(VirTypeDef {
            id: child,
            name_id: make_name_id(200),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![make_method_id(30)],
            static_methods: vec![],
            extends: vec![parent],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert_eq!(meta.type_extends(child), Some(&[parent][..]));
    }

    #[test]
    fn overwrite_type_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![make_field_id(1)],
            field_types: vec![VirTypeId::I64],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Overwrite with different data.
        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(101),
            kind: VirTypeDefKind::Struct,
            fields: vec![make_field_id(2), make_field_id(3)],
            field_types: vec![VirTypeId::I64, VirTypeId::I64],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert_eq!(meta.type_def_count(), 1);
        let td = meta.get_type_def(id).unwrap();
        assert_eq!(td.kind, VirTypeDefKind::Struct);
        assert_eq!(td.fields.len(), 2);
        assert_eq!(td.name_id, make_name_id(101));
    }

    #[test]
    fn insert_and_query_global_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_global_id(3);
        let name = make_name_id(300);

        meta.insert_global_def(VirGlobalDef {
            id,
            name_id: name,
            vir_ty: VirTypeId::I64,
            module_id: make_module_id(0),
        });

        assert_eq!(meta.global_def_count(), 1);

        let gd = meta.get_global_def(id).expect("should find global def");
        assert_eq!(gd.vir_ty, VirTypeId::I64);
        assert_eq!(gd.name_id, name);
        assert_eq!(gd.module_id, make_module_id(0));

        assert_eq!(meta.global_by_name(name), Some(id));
        assert!(meta.has_global(name));
        assert_eq!(meta.global_vir_type(id), Some(VirTypeId::I64));
    }

    #[test]
    fn global_missing_lookups() {
        let meta = VirEntityMetadata::new();
        assert!(meta.get_global_def(make_global_id(99)).is_none());
        assert!(meta.global_by_name(make_name_id(99)).is_none());
        assert!(!meta.has_global(make_name_id(99)));
        assert!(meta.global_vir_type(make_global_id(99)).is_none());
    }

    #[test]
    fn insert_and_query_function_def() {
        let mut meta = VirEntityMetadata::new();
        let id = make_function_id(5);
        let name = make_name_id(500);
        let full_name = make_name_id(501);

        meta.insert_function_def(VirFunctionDef {
            id,
            name_id: name,
            full_name_id: full_name,
            module: make_module_id(1),
            param_types: vec![VirTypeId::I64, VirTypeId::STRING],
            return_type: VirTypeId::BOOL,
            param_names: vec!["x".into(), "y".into()],
            required_params: 1,
            has_defaults: vec![false, true],
            is_generic: false,
            is_external: false,
            generator_element_type: None,
            sema_param_types: vec![TypeId::I64, TypeId::STRING],
            sema_return_type: TypeId::BOOL,
            sema_generator_element_type: None,
        });

        assert_eq!(meta.function_def_count(), 1);

        let fd = meta.get_function_def(id).expect("should find function def");
        assert_eq!(fd.name_id, name);
        assert_eq!(fd.full_name_id, full_name);
        assert_eq!(fd.module, make_module_id(1));
        assert_eq!(fd.param_types, vec![VirTypeId::I64, VirTypeId::STRING]);
        assert_eq!(fd.return_type, VirTypeId::BOOL);
        assert_eq!(fd.param_names, vec!["x", "y"]);
        assert_eq!(fd.required_params, 1);
        assert_eq!(fd.has_defaults, vec![false, true]);
        assert!(!fd.is_generic);
        assert!(!fd.is_external);
        assert!(fd.generator_element_type.is_none());

        // Reverse lookup by name.
        assert_eq!(meta.function_by_name(name), Some(id));
        assert!(meta.has_function(name));
        assert!(!meta.has_function(make_name_id(999)));
    }

    #[test]
    fn insert_function_def_generic_generator() {
        let mut meta = VirEntityMetadata::new();
        let id = make_function_id(10);

        meta.insert_function_def(VirFunctionDef {
            id,
            name_id: make_name_id(600),
            full_name_id: make_name_id(601),
            module: make_module_id(0),
            param_types: vec![VirTypeId::I64],
            return_type: VirTypeId::I64,
            param_names: vec!["n".into()],
            required_params: 1,
            has_defaults: vec![false],
            is_generic: true,
            is_external: false,
            generator_element_type: Some(VirTypeId::I64),
            sema_param_types: vec![TypeId::I64],
            sema_return_type: TypeId::I64,
            sema_generator_element_type: Some(TypeId::I64),
        });

        let fd = meta.get_function_def(id).unwrap();
        assert!(fd.is_generic);
        assert_eq!(fd.generator_element_type, Some(VirTypeId::I64));
    }

    #[test]
    fn function_missing_lookups() {
        let meta = VirEntityMetadata::new();
        assert!(meta.get_function_def(make_function_id(99)).is_none());
        assert!(meta.function_by_name(make_name_id(99)).is_none());
        assert!(!meta.has_function(make_name_id(99)));
    }

    #[test]
    fn type_by_name_populated_on_insert() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let name = make_name_id(100);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: name,
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert_eq!(meta.type_by_name(name), Some(id));
        assert!(meta.type_by_name(make_name_id(999)).is_none());
    }

    #[test]
    fn type_by_name_overwrite() {
        let mut meta = VirEntityMetadata::new();
        let id1 = make_type_def_id(1);
        let id2 = make_type_def_id(2);
        let name = make_name_id(100);

        meta.insert_type_def(VirTypeDef {
            id: id1,
            name_id: name,
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Second type with the same name overwrites the reverse map.
        meta.insert_type_def(VirTypeDef {
            id: id2,
            name_id: name,
            kind: VirTypeDefKind::Struct,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        assert_eq!(meta.type_by_name(name), Some(id2));
    }

    #[test]
    fn array_name_id_default_none() {
        let meta = VirEntityMetadata::new();
        assert!(meta.array_name_id().is_none());
    }

    #[test]
    fn set_and_query_array_name_id() {
        let mut meta = VirEntityMetadata::new();
        let name = make_name_id(42);

        meta.set_array_name_id(name);
        assert_eq!(meta.array_name_id(), Some(name));
    }

    #[test]
    fn short_name_map_single_entry() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);

        meta.insert_short_name("Point".to_string(), id);

        assert_eq!(meta.type_by_short_name("Point"), Some(id));
        assert!(meta.type_by_short_name("Line").is_none());
    }

    #[test]
    fn short_name_map_multiple_entries() {
        let mut meta = VirEntityMetadata::new();
        let id1 = make_type_def_id(1);
        let id2 = make_type_def_id(2);

        meta.insert_short_name("Point".to_string(), id1);
        meta.insert_short_name("Point".to_string(), id2);

        // type_by_short_name returns the first entry.
        assert_eq!(meta.type_by_short_name("Point"), Some(id1));

        // types_by_short_name returns all entries.
        let all = meta.types_by_short_name("Point").unwrap();
        assert_eq!(all, &[id1, id2]);
    }

    #[test]
    fn types_by_short_name_missing() {
        let meta = VirEntityMetadata::new();
        assert!(meta.types_by_short_name("Nonexistent").is_none());
    }

    #[test]
    fn is_external_only_empty_methods() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Empty methods → false
        assert!(!meta.is_external_only(id));
    }

    #[test]
    fn is_external_only_all_external() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let m1 = make_method_id(10);
        let m2 = make_method_id(11);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![m1, m2],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Both methods have external bindings and no default
        meta.insert_method_def(VirMethodDef {
            id: m1,
            name_id: make_name_id(200),
            full_name_id: make_name_id(201),
            defining_type: id,
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: Some(VirExternalMethodInfo {
                module_path: make_name_id(300),
                native_name: make_name_id(301),
            }),
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });
        meta.insert_method_def(VirMethodDef {
            id: m2,
            name_id: make_name_id(202),
            full_name_id: make_name_id(203),
            defining_type: id,
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: Some(VirExternalMethodInfo {
                module_path: make_name_id(302),
                native_name: make_name_id(303),
            }),
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });

        assert!(meta.is_external_only(id));
    }

    #[test]
    fn is_external_only_mixed_methods() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let m1 = make_method_id(10);
        let m2 = make_method_id(11);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![m1, m2],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // m1 has external binding, m2 does not
        meta.insert_method_def(VirMethodDef {
            id: m1,
            name_id: make_name_id(200),
            full_name_id: make_name_id(201),
            defining_type: id,
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: Some(VirExternalMethodInfo {
                module_path: make_name_id(300),
                native_name: make_name_id(301),
            }),
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });
        meta.insert_method_def(VirMethodDef {
            id: m2,
            name_id: make_name_id(202),
            full_name_id: make_name_id(203),
            defining_type: id,
            signature_id: TypeId::I64,
            has_default: false,
            is_static: false,
            external_binding: None,
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });

        // One non-external method → false
        assert!(!meta.is_external_only(id));
    }

    #[test]
    fn is_external_only_with_default() {
        let mut meta = VirEntityMetadata::new();
        let id = make_type_def_id(1);
        let m1 = make_method_id(10);

        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Interface,
            fields: vec![],
            field_types: vec![],
            methods: vec![m1],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: make_module_id(0),
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Method has external binding but also has_default → false
        meta.insert_method_def(VirMethodDef {
            id: m1,
            name_id: make_name_id(200),
            full_name_id: make_name_id(201),
            defining_type: id,
            signature_id: TypeId::I64,
            has_default: true,
            is_static: false,
            external_binding: Some(VirExternalMethodInfo {
                module_path: make_name_id(300),
                native_name: make_name_id(301),
            }),
            has_param_defaults: vec![],
            method_type_params: vec![],
            required_params: 0,
            param_names: vec![],
            param_types: vec![],
            return_type: VirTypeId::I64,
        });

        assert!(!meta.is_external_only(id));
    }

    #[test]
    fn is_external_only_missing_type() {
        let meta = VirEntityMetadata::new();
        // Non-existent type → false
        assert!(!meta.is_external_only(make_type_def_id(99)));
    }

    #[test]
    fn resolve_type_def_by_str_short_name_fallback() {
        let mut meta = VirEntityMetadata::new();
        let interner = Interner::new();
        let names = NameTable::new();
        let module_id = names.main_module();

        let id = make_type_def_id(1);
        meta.insert_short_name("Point".to_string(), id);
        meta.insert_type_def(VirTypeDef {
            id,
            name_id: make_name_id(100),
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: module_id,
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });

        // Falls back to short-name lookup.
        assert_eq!(
            meta.resolve_type_def_by_str(&interner, &names, module_id, "Point"),
            Some(id)
        );
        assert_eq!(
            meta.resolve_type_def_by_str(&interner, &names, module_id, "NoSuchType"),
            None
        );
    }

    #[test]
    fn resolve_type_def_by_str_sentinel_priority() {
        let mut meta = VirEntityMetadata::new();
        let interner = Interner::new();
        let mut names = NameTable::new();
        let module_id = names.main_module();

        // Create a sentinel and a non-sentinel both named "nil".
        let sentinel_id = make_type_def_id(1);
        let other_id = make_type_def_id(2);

        // Register sentinel with a proper NameId that has "nil" as last segment.
        let nil_name = names.intern_raw(module_id, &["nil"]);

        meta.insert_type_def(VirTypeDef {
            id: sentinel_id,
            name_id: nil_name,
            kind: VirTypeDefKind::Sentinel,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: module_id,
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });
        meta.insert_short_name("nil".to_string(), sentinel_id);

        meta.insert_type_def(VirTypeDef {
            id: other_id,
            name_id: make_name_id(999),
            kind: VirTypeDefKind::Class,
            fields: vec![],
            field_types: vec![],
            methods: vec![],
            static_methods: vec![],
            extends: vec![],
            type_params: vec![],
            implements: vec![],
            is_annotation: false,
            base_type_id: None,
            module: module_id,
            is_generic: false,
            generic_field_types: None,

            generic_field_names: None,
        });
        meta.insert_short_name("nil".to_string(), other_id);

        // "nil" should resolve to the sentinel, not the class.
        assert_eq!(
            meta.resolve_type_def_by_str(&interner, &names, module_id, "nil"),
            Some(sentinel_id)
        );
    }
}

// entity_view.rs
//! Codegen-local metadata view for entity-registry lookups.
//!
//! `EntityView` holds a snapshot of every type, method, field, function,
//! and global definition that codegen needs at compile time.  It is
//! populated once during `AnalyzedProgram::from_analysis` and all
//! `AnalyzedProgram` helper methods read from it instead of from
//! `Rc<EntityRegistry>`.

use rustc_hash::FxHashMap;

use vole_identity::{
    FieldId, FunctionId, GlobalId, MethodId, NameId, NameTable, TypeDefId, TypeId,
};
use vole_sema::EntityRegistry;
use vole_sema::entity_defs::{FieldDef, FunctionDef, GlobalDef, MethodDef, TypeDef};
use vole_sema::generic::{ClassMethodMonomorphCache, MonomorphCache, StaticMethodMonomorphCache};
use vole_sema::implement_registry::PrimitiveTypeId;
use vole_sema::type_arena::{SemaType, TypeArena};
use vole_sema::types::PrimitiveType;

use crate::analyzed::ExternalMethodInfoRef;

// ---------------------------------------------------------------------------
// EntityView
// ---------------------------------------------------------------------------

/// Codegen-local metadata view for entity-registry data.
///
/// Populated once during `from_analysis` from the sema `EntityRegistry`.
/// All helpers on `AnalyzedProgram` that previously read `Rc<EntityRegistry>`
/// now read from this view instead.
pub(crate) struct EntityView {
    // -- Storage (IDs are indices into these vectors) --
    type_defs: Vec<TypeDef>,
    method_defs: Vec<MethodDef>,
    field_defs: Vec<FieldDef>,
    function_defs: Vec<FunctionDef>,
    global_defs: Vec<GlobalDef>,

    // -- Primary lookups by NameId --
    type_by_name: FxHashMap<NameId, TypeDefId>,
    function_by_name: FxHashMap<NameId, FunctionId>,
    global_by_name: FxHashMap<NameId, GlobalId>,

    // -- Miscellaneous --
    array_name: Option<NameId>,
    /// Primitive type NameIds (i64, string, bool, ...).
    primitive_names: FxHashMap<PrimitiveTypeId, NameId>,

    /// Eagerly-built short-name cache (last segment -> TypeDefIds).
    short_name_map: FxHashMap<String, Vec<TypeDefId>>,

    // -- Monomorph caches --
    monomorph_cache: MonomorphCache,
    class_method_monomorph_cache: ClassMethodMonomorphCache,
    static_method_monomorph_cache: StaticMethodMonomorphCache,
}

impl EntityView {
    /// Build a codegen-local view by cloning all entries from an `EntityRegistry`.
    pub(crate) fn from_registry(registry: &EntityRegistry, names: &NameTable) -> Self {
        let type_defs = registry.all_type_defs().to_vec();
        let short_name_map = build_short_name_map(&type_defs, names);

        Self {
            type_defs,
            method_defs: registry.all_method_defs().to_vec(),
            field_defs: registry.all_field_defs().to_vec(),
            function_defs: registry.all_function_defs().to_vec(),
            global_defs: registry.all_global_defs().to_vec(),

            type_by_name: registry.type_by_name_map().clone(),
            function_by_name: registry.function_by_name_map().clone(),
            global_by_name: registry.global_by_name_map().clone(),

            array_name: registry.array_name_id(),
            primitive_names: registry.primitive_name_entries().collect(),
            short_name_map,

            monomorph_cache: registry.monomorph_cache.clone(),
            class_method_monomorph_cache: registry.class_method_monomorph_cache.clone(),
            static_method_monomorph_cache: registry.static_method_monomorph_cache.clone(),
        }
    }

    // ===== Type lookups =====

    /// The NameId for the built-in array type (for implement dispatch).
    pub(crate) fn array_name_id(&self) -> Option<NameId> {
        self.array_name
    }

    /// Return a type definition by ID.
    pub(crate) fn get_type(&self, type_def_id: TypeDefId) -> &TypeDef {
        &self.type_defs[type_def_id.index() as usize]
    }

    /// Resolve TypeDefId by NameId.
    pub(crate) fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        self.type_by_name.get(&name_id).copied()
    }

    /// Find a type by its short (last-segment) name.
    pub(crate) fn type_by_short_name(&self, short_name: &str) -> Option<TypeDefId> {
        self.short_name_map
            .get(short_name)
            .and_then(|ids| ids.first().copied())
    }

    /// Return type arguments for a specific interface implementation.
    pub(crate) fn implementation_type_args(
        &self,
        type_def_id: TypeDefId,
        interface_id: TypeDefId,
    ) -> &[TypeId] {
        let type_def = self.get_type(type_def_id);
        for impl_ in &type_def.implements {
            if impl_.interface == interface_id {
                return &impl_.type_args;
            }
        }
        &[]
    }

    /// Find a method binding for a type's interface implementation.
    pub(crate) fn find_method_binding(
        &self,
        type_def_id: TypeDefId,
        method_name: NameId,
    ) -> Option<&vole_sema::entity_defs::MethodBinding> {
        let type_def = self.get_type(type_def_id);
        for impl_ in &type_def.implements {
            for binding in &impl_.method_bindings {
                if binding.method_name == method_name {
                    return Some(binding);
                }
            }
        }
        None
    }

    /// Check if all methods on a type have external bindings.
    pub(crate) fn is_external_only(&self, type_def_id: TypeDefId) -> bool {
        let type_def = self.get_type(type_def_id);
        if type_def.methods.is_empty() {
            return false;
        }
        type_def.methods.iter().all(|&method_id| {
            let method = self.get_method(method_id);
            method.external_binding.is_some() && !method.has_default
        })
    }

    // ===== Field lookups =====

    /// Return a field definition by ID.
    pub(crate) fn get_field(&self, field_id: FieldId) -> &FieldDef {
        &self.field_defs[field_id.index() as usize]
    }

    // ===== Function lookups =====

    /// Return a function definition by ID.
    pub(crate) fn get_function(&self, function_id: FunctionId) -> &FunctionDef {
        &self.function_defs[function_id.index() as usize]
    }

    /// Resolve FunctionId by NameId.
    pub(crate) fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        self.function_by_name.get(&name_id).copied()
    }

    // ===== Method lookups =====

    /// Return a method definition by ID.
    pub(crate) fn get_method(&self, method_id: MethodId) -> &MethodDef {
        &self.method_defs[method_id.index() as usize]
    }

    /// Return external binding metadata for a method, when available.
    pub(crate) fn method_external_binding(
        &self,
        method_id: MethodId,
    ) -> Option<ExternalMethodInfoRef> {
        self.get_method(method_id)
            .external_binding
            .as_ref()
            .map(|info| ExternalMethodInfoRef {
                module_path: info.module_path,
                native_name: info.native_name,
            })
    }

    // ===== Global lookups =====

    /// Look up a global by NameId.
    pub(crate) fn global_by_name(&self, name_id: NameId) -> Option<GlobalId> {
        self.global_by_name.get(&name_id).copied()
    }

    /// Return a global definition by ID.
    pub(crate) fn get_global(&self, global_id: GlobalId) -> &GlobalDef {
        &self.global_defs[global_id.index() as usize]
    }

    // ===== Monomorph caches =====

    /// Get the free-function monomorph cache.
    pub(crate) fn monomorph_cache(&self) -> &MonomorphCache {
        &self.monomorph_cache
    }

    /// Get the class-method monomorph cache.
    pub(crate) fn class_method_monomorph_cache(&self) -> &ClassMethodMonomorphCache {
        &self.class_method_monomorph_cache
    }

    /// Get the static-method monomorph cache.
    pub(crate) fn static_method_monomorph_cache(&self) -> &StaticMethodMonomorphCache {
        &self.static_method_monomorph_cache
    }

    /// Resolve the implement-registry type-key NameId from a concrete sema TypeId.
    ///
    /// Replicates `ImplTypeId::from_type_id` logic using the EntityView's
    /// own type defs and primitive name table, without reaching back into
    /// the EntityRegistry.
    pub(crate) fn impl_type_name_id_from_type_id(
        &self,
        type_id: TypeId,
        arena: &TypeArena,
    ) -> Option<NameId> {
        match arena.get(type_id) {
            SemaType::Primitive(prim) => {
                let prim_id = match prim {
                    PrimitiveType::I8 => PrimitiveTypeId::I8,
                    PrimitiveType::I16 => PrimitiveTypeId::I16,
                    PrimitiveType::I32 => PrimitiveTypeId::I32,
                    PrimitiveType::I64 => PrimitiveTypeId::I64,
                    PrimitiveType::I128 => PrimitiveTypeId::I128,
                    PrimitiveType::U8 => PrimitiveTypeId::U8,
                    PrimitiveType::U16 => PrimitiveTypeId::U16,
                    PrimitiveType::U32 => PrimitiveTypeId::U32,
                    PrimitiveType::U64 => PrimitiveTypeId::U64,
                    PrimitiveType::F32 => PrimitiveTypeId::F32,
                    PrimitiveType::F64 => PrimitiveTypeId::F64,
                    PrimitiveType::F128 => PrimitiveTypeId::F128,
                    PrimitiveType::Bool => PrimitiveTypeId::Bool,
                    PrimitiveType::String => PrimitiveTypeId::String,
                };
                self.primitive_names.get(&prim_id).copied()
            }
            SemaType::Range => self.primitive_names.get(&PrimitiveTypeId::Range).copied(),
            SemaType::Handle => self.primitive_names.get(&PrimitiveTypeId::Handle).copied(),
            SemaType::Array(_) => self.array_name,
            SemaType::Class { type_def_id, .. } | SemaType::Struct { type_def_id, .. } => {
                Some(self.get_type(*type_def_id).name_id)
            }
            _ => None,
        }
    }

    /// Resolve a type definition by short name, matching the sema
    /// `resolve_type_str_or_interface` resolution chain.
    ///
    /// Uses the identity-layer `Resolver` for scoped NameId lookup, then
    /// maps through `type_by_name`.  Falls back to short-name search
    /// across all registered types (interfaces, classes, structs, sentinels).
    pub(crate) fn resolve_type_def_by_str(
        &self,
        interner: &vole_frontend::Interner,
        names: &NameTable,
        module_id: vole_identity::ModuleId,
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
        let resolver = vole_identity::Resolver::new(interner, names, module_id, &[]);
        if let Some(name_id) = resolver.resolve_str(name)
            && let Some(id) = self.type_by_name(name_id)
        {
            return Some(id);
        }
        // Short-name fallback (covers sentinel, interface, class, struct).
        self.type_by_short_name(name)
    }

    /// Find a sentinel type by its short (last-segment) name.
    fn sentinel_by_short_name(&self, short_name: &str, names: &NameTable) -> Option<TypeDefId> {
        self.short_name_map.get(short_name).and_then(|ids| {
            ids.iter().copied().find(|&id| {
                let td = self.get_type(id);
                td.kind.is_sentinel()
                    && names.last_segment_str(td.name_id).as_deref() == Some(short_name)
            })
        })
    }
}

// ---------------------------------------------------------------------------
// TypeDefProvider impl
// ---------------------------------------------------------------------------

impl vole_sema::TypeDefProvider for EntityView {
    fn get_type(&self, id: TypeDefId) -> &TypeDef {
        EntityView::get_type(self, id)
    }
}

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

/// Eagerly build the short-name cache from all type definitions.
fn build_short_name_map(
    type_defs: &[TypeDef],
    names: &NameTable,
) -> FxHashMap<String, Vec<TypeDefId>> {
    let mut map: FxHashMap<String, Vec<TypeDefId>> = FxHashMap::default();
    for type_def in type_defs {
        if let Some(last_segment) = names.last_segment_str(type_def.name_id) {
            map.entry(last_segment).or_default().push(type_def.id);
        }
    }
    map
}

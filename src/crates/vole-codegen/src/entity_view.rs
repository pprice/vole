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
    ClassMethodMonomorphCache, FunctionId, GlobalId, MonomorphCache, NameId, NameTable,
    StaticMethodMonomorphCache, TypeDefId,
};
use vole_sema::EntityRegistry;
use vole_sema::entity_defs::{GlobalDef, TypeDef};

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
    global_defs: Vec<GlobalDef>,

    // -- Primary lookups by NameId --
    type_by_name: FxHashMap<NameId, TypeDefId>,
    function_by_name: FxHashMap<NameId, FunctionId>,
    global_by_name: FxHashMap<NameId, GlobalId>,

    // -- Miscellaneous --
    array_name: Option<NameId>,

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
            global_defs: registry.all_global_defs().to_vec(),

            type_by_name: registry.type_by_name_map().clone(),
            function_by_name: registry.function_by_name_map().clone(),
            global_by_name: registry.global_by_name_map().clone(),

            array_name: registry.array_name_id(),
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

    // ===== Function lookups =====

    /// Resolve FunctionId by NameId.
    pub(crate) fn function_by_name(&self, name_id: NameId) -> Option<FunctionId> {
        self.function_by_name.get(&name_id).copied()
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

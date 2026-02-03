//! Type registration and lookup for EntityRegistry.

use crate::entity_defs::{TypeDef, TypeDefKind};
use rustc_hash::FxHashMap;
use vole_identity::{ModuleId, NameId, TypeDefId};

use super::EntityRegistry;

impl EntityRegistry {
    /// Count total static methods registered (for debugging)
    pub fn static_method_count(&self) -> usize {
        self.method_defs.iter().filter(|m| m.is_static).count()
    }

    /// Register a new type definition
    pub fn register_type(
        &mut self,
        name_id: NameId,
        kind: TypeDefKind,
        module: ModuleId,
    ) -> TypeDefId {
        let id = TypeDefId::new(self.type_defs.len() as u32);
        self.type_defs.push(TypeDef {
            id,
            name_id,
            kind,
            module,
            methods: Vec::new(),
            fields: Vec::new(),
            extends: Vec::new(),
            type_params: Vec::new(),
            static_methods: Vec::new(),
            aliased_type: None,
            generic_info: None,
            error_info: None,
            implements: Vec::new(),
            base_type_id: None,
        });
        self.type_by_name.insert(name_id, id);
        self.methods_by_type.insert(id, FxHashMap::default());
        self.fields_by_type.insert(id, FxHashMap::default());
        self.static_methods_by_type.insert(id, FxHashMap::default());
        *self.short_name_cache.borrow_mut() = None; // Invalidate short name cache
        id
    }

    /// Register all primitive types from the NameTable
    pub fn register_primitives(&mut self, name_table: &vole_identity::NameTable) {
        let Some(builtin_module) = name_table.builtin_module_id() else {
            return; // No builtin module yet - primitives can't be registered
        };

        // Register each primitive type using the iterator from Primitives
        for name_id in name_table.primitives.iter() {
            self.register_type(name_id, TypeDefKind::Primitive, builtin_module);
        }
    }

    /// Get a type definition by ID
    pub fn get_type(&self, id: TypeDefId) -> &TypeDef {
        &self.type_defs[id.index() as usize]
    }

    /// Get a mutable type definition by ID
    pub fn get_type_mut(&mut self, id: TypeDefId) -> &mut TypeDef {
        &mut self.type_defs[id.index() as usize]
    }

    /// Get the NameId for a type definition
    pub fn name_id(&self, id: TypeDefId) -> NameId {
        self.get_type(id).name_id
    }

    /// Set the base_type_id for a class type.
    /// This stores the TypeId for the type with empty type args (e.g., `Foo` for `class Foo<T>`).
    pub fn set_base_type_id(
        &mut self,
        type_def_id: TypeDefId,
        base_type_id: crate::type_arena::TypeId,
    ) {
        self.get_type_mut(type_def_id).base_type_id = Some(base_type_id);
    }

    /// Look up a type by its NameId
    #[must_use]
    pub fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        self.type_by_name.get(&name_id).copied()
    }

    /// Ensure the short name cache is populated. Called lazily on first lookup.
    fn ensure_short_name_cache(&self, name_table: &vole_identity::NameTable) {
        let mut cache_ref = self.short_name_cache.borrow_mut();
        if cache_ref.is_some() {
            return;
        }
        let mut cache = FxHashMap::default();
        for type_def in &self.type_defs {
            if let Some(last_segment) = name_table.last_segment_str(type_def.name_id) {
                cache
                    .entry(last_segment.to_string())
                    .or_insert_with(Vec::new)
                    .push(type_def.id);
            }
        }
        *cache_ref = Some(cache);
    }

    /// Look up the first TypeDefId matching a short name and kind filter from the cache.
    fn lookup_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
        kind_filter: Option<TypeDefKind>,
    ) -> Option<TypeDefId> {
        self.ensure_short_name_cache(name_table);
        let cache_ref = self.short_name_cache.borrow();
        let cache = cache_ref.as_ref()?;
        let ids = cache.get(short_name)?;
        match kind_filter {
            Some(kind) => ids
                .iter()
                .find(|&&id| self.type_defs[id.index() as usize].kind == kind)
                .copied(),
            None => ids.first().copied(),
        }
    }

    /// Look up an interface by its short name (string-based, cross-module).
    /// Uses a cached short name index for O(1) lookups after initial build.
    pub fn interface_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        self.lookup_short_name(short_name, name_table, Some(TypeDefKind::Interface))
    }

    /// Look up a class by its short name (string-based, cross-module).
    /// Uses a cached short name index for O(1) lookups after initial build.
    /// Used for prelude classes like Map and Set.
    pub fn class_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        tracing::trace!(short_name, "class_by_short_name searching");
        let result = self.lookup_short_name(short_name, name_table, Some(TypeDefKind::Class));
        tracing::trace!(?result, "class_by_short_name result");
        result
    }

    /// Look up a sentinel type by its short name (string-based, cross-module).
    /// Uses a cached short name index for O(1) lookups after initial build.
    /// Used to resolve well-known sentinel types (nil, Done) from any module.
    pub fn sentinel_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        self.lookup_short_name(short_name, name_table, Some(TypeDefKind::Sentinel))
    }

    /// Look up any type by its short name (string-based, cross-module).
    /// Uses a cached short name index for O(1) lookups after initial build.
    /// Useful for resolving error types and other types by name.
    pub fn type_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        self.lookup_short_name(short_name, name_table, None)
    }
}

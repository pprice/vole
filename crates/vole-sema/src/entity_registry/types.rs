//! Type registration and lookup for EntityRegistry.

use crate::entity_defs::{TypeDef, TypeDefKind};
use std::collections::HashMap;
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
        self.methods_by_type.insert(id, HashMap::new());
        self.fields_by_type.insert(id, HashMap::new());
        self.static_methods_by_type.insert(id, HashMap::new());
        id
    }

    /// Register all primitive types from the NameTable
    pub fn register_primitives(&mut self, name_table: &vole_identity::NameTable) {
        let primitives = &name_table.primitives;
        let Some(builtin_module) = name_table.builtin_module_id() else {
            return; // No builtin module yet - primitives can't be registered
        };

        // Register each primitive type
        self.register_type(primitives.i8, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.i16, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.i32, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.i64, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.i128, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.u8, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.u16, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.u32, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.u64, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.f32, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.f64, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.bool, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.string, TypeDefKind::Primitive, builtin_module);
        self.register_type(primitives.nil, TypeDefKind::Primitive, builtin_module);
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

    /// Set the base_type_id for a class/record type.
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

    /// Look up an interface by its short name (string-based, cross-module)
    /// This searches through all registered types to find one matching the short name
    /// and of kind Interface
    pub fn interface_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        for type_def in &self.type_defs {
            if type_def.kind == TypeDefKind::Interface
                && name_table
                    .last_segment_str(type_def.name_id)
                    .is_some_and(|last_segment| last_segment == short_name)
            {
                return Some(type_def.id);
            }
        }
        None
    }

    /// Look up a class by its short name (string-based, cross-module)
    /// This searches through all registered types to find one matching the short name
    /// and of kind Class. Used for prelude classes like Map and Set.
    pub fn class_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        tracing::trace!(short_name, "class_by_short_name searching");
        for type_def in &self.type_defs {
            if type_def.kind == TypeDefKind::Class {
                let last_seg = name_table.last_segment_str(type_def.name_id);
                tracing::trace!(?type_def.name_id, ?last_seg, "checking class");
                if last_seg.is_some_and(|last_segment| last_segment == short_name) {
                    tracing::trace!(?type_def.id, "found class by short name");
                    return Some(type_def.id);
                }
            }
        }
        tracing::trace!("class not found by short name");
        None
    }

    /// Look up any type by its short name (string-based, cross-module)
    /// This searches through all registered types to find one matching the short name,
    /// regardless of kind. Useful for resolving error types and other types by name.
    pub fn type_by_short_name(
        &self,
        short_name: &str,
        name_table: &vole_identity::NameTable,
    ) -> Option<TypeDefId> {
        for type_def in &self.type_defs {
            if name_table
                .last_segment_str(type_def.name_id)
                .is_some_and(|last_segment| last_segment == short_name)
            {
                return Some(type_def.id);
            }
        }
        None
    }
}

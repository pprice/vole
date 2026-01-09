//! Central registry for all language entities.
//!
//! EntityRegistry stores type definitions, methods, fields, and functions,
//! providing type-safe lookups by ID and name.

use std::collections::HashMap;

use crate::identity::{FieldId, FunctionId, MethodId, ModuleId, NameId, TypeDefId};
use crate::sema::entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
use crate::sema::FunctionType;

/// Central registry for all language entities
#[derive(Debug, Clone)]
pub struct EntityRegistry {
    // Storage - IDs are indices into these vectors
    pub(crate) type_defs: Vec<TypeDef>,
    pub(crate) method_defs: Vec<MethodDef>,
    pub(crate) field_defs: Vec<FieldDef>,
    pub(crate) function_defs: Vec<FunctionDef>,

    // Primary lookups by NameId
    pub(crate) type_by_name: HashMap<NameId, TypeDefId>,
    pub(crate) method_by_full_name: HashMap<NameId, MethodId>,
    pub(crate) field_by_full_name: HashMap<NameId, FieldId>,
    pub(crate) function_by_name: HashMap<NameId, FunctionId>,

    // Scoped lookups: (type, method_name) -> MethodId
    pub(crate) methods_by_type: HashMap<TypeDefId, HashMap<NameId, MethodId>>,
    pub(crate) fields_by_type: HashMap<TypeDefId, HashMap<NameId, FieldId>>,
}

impl EntityRegistry {
    pub fn new() -> Self {
        Self {
            type_defs: Vec::new(),
            method_defs: Vec::new(),
            field_defs: Vec::new(),
            function_defs: Vec::new(),
            type_by_name: HashMap::new(),
            method_by_full_name: HashMap::new(),
            field_by_full_name: HashMap::new(),
            function_by_name: HashMap::new(),
            methods_by_type: HashMap::new(),
            fields_by_type: HashMap::new(),
        }
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
        });
        self.type_by_name.insert(name_id, id);
        self.methods_by_type.insert(id, HashMap::new());
        self.fields_by_type.insert(id, HashMap::new());
        id
    }

    /// Get a type definition by ID
    pub fn get_type(&self, id: TypeDefId) -> &TypeDef {
        &self.type_defs[id.index() as usize]
    }

    /// Get a mutable type definition by ID
    pub fn get_type_mut(&mut self, id: TypeDefId) -> &mut TypeDef {
        &mut self.type_defs[id.index() as usize]
    }

    /// Look up a type by its NameId
    pub fn type_by_name(&self, name_id: NameId) -> Option<TypeDefId> {
        self.type_by_name.get(&name_id).copied()
    }

    /// Register a new method on a type
    pub fn register_method(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature: FunctionType,
        has_default: bool,
    ) -> MethodId {
        let id = MethodId::new(self.method_defs.len() as u32);
        self.method_defs.push(MethodDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            signature,
            has_default,
        });
        self.method_by_full_name.insert(full_name_id, id);
        self.methods_by_type
            .get_mut(&defining_type)
            .expect("type must be registered before adding methods")
            .insert(name_id, id);
        self.type_defs[defining_type.index() as usize].methods.push(id);
        id
    }

    /// Get a method definition by ID
    pub fn get_method(&self, id: MethodId) -> &MethodDef {
        &self.method_defs[id.index() as usize]
    }

    /// Get all methods defined directly on a type (not inherited)
    pub fn methods_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = MethodId> + '_ {
        self.type_defs[type_id.index() as usize].methods.iter().copied()
    }

    /// Find a method on a type by its short name (not inherited)
    pub fn find_method_on_type(&self, type_id: TypeDefId, name_id: NameId) -> Option<MethodId> {
        self.methods_by_type
            .get(&type_id)
            .and_then(|methods| methods.get(&name_id).copied())
    }
}

impl Default for EntityRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::identity::NameTable;
    use crate::sema::Type;

    #[test]
    fn register_and_lookup_type() {
        let mut names = NameTable::new();
        let name_id = names.intern_raw(names.main_module(), &["TestType"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(name_id, TypeDefKind::Record, names.main_module());

        assert_eq!(registry.type_by_name(name_id), Some(type_id));
        assert_eq!(registry.get_type(type_id).name_id, name_id);
        assert_eq!(registry.get_type(type_id).kind, TypeDefKind::Record);
    }

    #[test]
    fn register_and_lookup_method() {
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["Iterator"]);
        let method_name = names.intern_raw(builtin_mod, &["next"]);
        let full_method_name = names.intern_raw(main_mod, &["Iterator", "next"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(type_name, TypeDefKind::Interface, main_mod);

        let signature = FunctionType {
            params: vec![],
            return_type: Box::new(Type::I32),
            is_closure: false,
        };

        let method_id = registry.register_method(
            type_id,
            method_name,
            full_method_name,
            signature,
            false,
        );

        assert_eq!(registry.find_method_on_type(type_id, method_name), Some(method_id));
        assert_eq!(registry.get_method(method_id).defining_type, type_id);
        assert_eq!(registry.methods_on_type(type_id).collect::<Vec<_>>(), vec![method_id]);
    }
}

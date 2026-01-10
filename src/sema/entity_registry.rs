//! Central registry for all language entities.
//!
//! EntityRegistry stores type definitions, methods, fields, and functions,
//! providing type-safe lookups by ID and name.

use std::collections::{HashMap, HashSet};

use crate::identity::{FieldId, FunctionId, MethodId, ModuleId, NameId, TypeDefId};
use crate::sema::entity_defs::{FieldDef, FunctionDef, MethodDef, TypeDef, TypeDefKind};
use crate::sema::implement_registry::ExternalMethodInfo;
use crate::sema::{FunctionType, Type};

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
            type_params: Vec::new(),
            type_params_symbols: Vec::new(),
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

    /// Look up an interface by its short name (string-based, cross-module)
    /// This searches through all registered types to find one matching the short name
    /// and of kind Interface
    pub fn interface_by_short_name(
        &self,
        short_name: &str,
        name_table: &crate::identity::NameTable,
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

    /// Register a new method on a type
    pub fn register_method(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature: FunctionType,
        has_default: bool,
    ) -> MethodId {
        self.register_method_with_binding(
            defining_type,
            name_id,
            full_name_id,
            signature,
            has_default,
            None,
        )
    }

    /// Register a new method on a type with optional external binding
    pub fn register_method_with_binding(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature: FunctionType,
        has_default: bool,
        external_binding: Option<ExternalMethodInfo>,
    ) -> MethodId {
        let id = MethodId::new(self.method_defs.len() as u32);
        self.method_defs.push(MethodDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            signature,
            has_default,
            external_binding,
        });
        self.method_by_full_name.insert(full_name_id, id);
        self.methods_by_type
            .get_mut(&defining_type)
            .expect("type must be registered before adding methods")
            .insert(name_id, id);
        self.type_defs[defining_type.index() as usize]
            .methods
            .push(id);
        id
    }

    /// Get a method definition by ID
    pub fn get_method(&self, id: MethodId) -> &MethodDef {
        &self.method_defs[id.index() as usize]
    }

    /// Get all methods defined directly on a type (not inherited)
    pub fn methods_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = MethodId> + '_ {
        self.type_defs[type_id.index() as usize]
            .methods
            .iter()
            .copied()
    }

    /// Find a method on a type by its short name (not inherited)
    pub fn find_method_on_type(&self, type_id: TypeDefId, name_id: NameId) -> Option<MethodId> {
        self.methods_by_type
            .get(&type_id)
            .and_then(|methods| methods.get(&name_id).copied())
    }

    /// Register a new field on a type
    pub fn register_field(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        ty: Type,
        slot: usize,
    ) -> FieldId {
        let id = FieldId::new(self.field_defs.len() as u32);
        self.field_defs.push(FieldDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            ty,
            slot,
        });
        self.field_by_full_name.insert(full_name_id, id);
        self.fields_by_type
            .get_mut(&defining_type)
            .expect("type must be registered before adding fields")
            .insert(name_id, id);
        self.type_defs[defining_type.index() as usize]
            .fields
            .push(id);
        id
    }

    /// Get a field definition by ID
    pub fn get_field(&self, id: FieldId) -> &FieldDef {
        &self.field_defs[id.index() as usize]
    }

    /// Get all fields defined directly on a type
    pub fn fields_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = FieldId> + '_ {
        self.type_defs[type_id.index() as usize]
            .fields
            .iter()
            .copied()
    }

    /// Find a field on a type by its short name
    pub fn find_field_on_type(&self, type_id: TypeDefId, name_id: NameId) -> Option<FieldId> {
        self.fields_by_type
            .get(&type_id)
            .and_then(|fields| fields.get(&name_id).copied())
    }

    /// Register a new free function
    pub fn register_function(
        &mut self,
        name_id: NameId,
        full_name_id: NameId,
        module: ModuleId,
        signature: FunctionType,
    ) -> FunctionId {
        let id = FunctionId::new(self.function_defs.len() as u32);
        self.function_defs.push(FunctionDef {
            id,
            name_id,
            full_name_id,
            module,
            signature,
        });
        self.function_by_name.insert(full_name_id, id);
        id
    }

    /// Get a function definition by ID
    pub fn get_function(&self, id: FunctionId) -> &FunctionDef {
        &self.function_defs[id.index() as usize]
    }

    /// Look up a function by its full NameId
    pub fn function_by_name(&self, full_name_id: NameId) -> Option<FunctionId> {
        self.function_by_name.get(&full_name_id).copied()
    }

    /// Add an extends relationship (derived extends base)
    pub fn add_extends(&mut self, derived: TypeDefId, base: TypeDefId) {
        self.type_defs[derived.index() as usize].extends.push(base);
    }

    /// Set type parameters for a generic type
    pub fn set_type_params(
        &mut self,
        type_id: TypeDefId,
        type_params: Vec<NameId>,
        type_params_symbols: Vec<crate::frontend::Symbol>,
    ) {
        self.type_defs[type_id.index() as usize].type_params = type_params;
        self.type_defs[type_id.index() as usize].type_params_symbols = type_params_symbols;
    }

    /// Check if derived extends base (transitive)
    pub fn type_extends(&self, derived: TypeDefId, base: TypeDefId) -> bool {
        if derived == base {
            return true;
        }
        let mut stack = vec![derived];
        let mut seen = HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            for parent in &self.type_defs[current.index() as usize].extends {
                if *parent == base {
                    return true;
                }
                stack.push(*parent);
            }
        }
        false
    }

    /// Resolve a method on a type, checking inherited methods too
    pub fn resolve_method(&self, type_id: TypeDefId, method_name: NameId) -> Option<MethodId> {
        // Check direct methods first
        if let Some(method_id) = self.find_method_on_type(type_id, method_name) {
            return Some(method_id);
        }
        // Check parent types
        for parent in &self.type_defs[type_id.index() as usize].extends.clone() {
            if let Some(method_id) = self.resolve_method(*parent, method_name) {
                return Some(method_id);
            }
        }
        None
    }

    /// Get all methods on a type including inherited
    pub fn all_methods(&self, type_id: TypeDefId) -> Vec<MethodId> {
        let mut result = Vec::new();
        let mut seen_names = HashSet::new();
        self.collect_all_methods(type_id, &mut result, &mut seen_names);
        result
    }

    fn collect_all_methods(
        &self,
        type_id: TypeDefId,
        result: &mut Vec<MethodId>,
        seen_names: &mut HashSet<NameId>,
    ) {
        // Add direct methods first (they override inherited)
        for method_id in &self.type_defs[type_id.index() as usize].methods {
            let method = self.get_method(*method_id);
            if seen_names.insert(method.name_id) {
                result.push(*method_id);
            }
        }
        // Then check parents
        for parent in self.type_defs[type_id.index() as usize].extends.clone() {
            self.collect_all_methods(parent, result, seen_names);
        }
    }

    /// Check if a type is a functional interface (single abstract method, no fields).
    /// Returns the single abstract method's ID if it's a functional interface.
    pub fn is_functional(&self, type_id: TypeDefId) -> Option<MethodId> {
        let type_def = self.get_type(type_id);

        // Must have no fields
        if !type_def.fields.is_empty() {
            return None;
        }

        // Count abstract methods (no default)
        let abstract_methods: Vec<MethodId> = type_def
            .methods
            .iter()
            .copied()
            .filter(|&method_id| !self.get_method(method_id).has_default)
            .collect();

        // Exactly one abstract method = functional interface
        if abstract_methods.len() == 1 {
            Some(abstract_methods[0])
        } else {
            None
        }
    }

    /// Get the external binding for a method (if any)
    pub fn get_external_binding(&self, method_id: MethodId) -> Option<&ExternalMethodInfo> {
        self.get_method(method_id).external_binding.as_ref()
    }

    /// Check if all methods on a type have external bindings
    pub fn is_external_only(&self, type_id: TypeDefId) -> bool {
        let type_def = self.get_type(type_id);
        if type_def.methods.is_empty() {
            return false;
        }
        type_def.methods.iter().all(|&method_id| {
            let method = self.get_method(method_id);
            method.external_binding.is_some() && !method.has_default
        })
    }

    /// Merge another registry into this one.
    /// This is used when merging prelude definitions into the main analyzer.
    pub fn merge(&mut self, other: &EntityRegistry) {
        // Build a mapping from other's IDs to our new IDs
        let mut type_id_map: HashMap<TypeDefId, TypeDefId> = HashMap::new();

        // First pass: register all types (without methods/fields to avoid ID confusion)
        for other_type in &other.type_defs {
            // Check if we already have a type with this name
            if self.type_by_name.contains_key(&other_type.name_id) {
                // Type already exists, map to existing ID
                let existing_id = self.type_by_name[&other_type.name_id];
                type_id_map.insert(other_type.id, existing_id);
            } else {
                // New type - add it
                let new_id = TypeDefId::new(self.type_defs.len() as u32);
                let mut new_type = other_type.clone();
                new_type.id = new_id;
                new_type.methods = Vec::new(); // Will be filled in later
                new_type.fields = Vec::new();
                new_type.extends = Vec::new(); // Will be remapped
                self.type_defs.push(new_type);
                self.type_by_name.insert(other_type.name_id, new_id);
                self.methods_by_type.insert(new_id, HashMap::new());
                self.fields_by_type.insert(new_id, HashMap::new());
                type_id_map.insert(other_type.id, new_id);
            }
        }

        // Second pass: register all methods
        for other_method in &other.method_defs {
            let new_defining_type = type_id_map[&other_method.defining_type];
            let new_id = MethodId::new(self.method_defs.len() as u32);
            let mut new_method = other_method.clone();
            new_method.id = new_id;
            new_method.defining_type = new_defining_type;
            self.method_defs.push(new_method);
            self.type_defs[new_defining_type.index() as usize]
                .methods
                .push(new_id);
            self.method_by_full_name
                .insert(other_method.full_name_id, new_id);
            self.methods_by_type
                .entry(new_defining_type)
                .or_default()
                .insert(other_method.name_id, new_id);
        }

        // Third pass: register all fields
        for other_field in &other.field_defs {
            let new_defining_type = type_id_map[&other_field.defining_type];
            let new_id = FieldId::new(self.field_defs.len() as u32);
            let mut new_field = other_field.clone();
            new_field.id = new_id;
            new_field.defining_type = new_defining_type;
            self.field_defs.push(new_field);
            self.type_defs[new_defining_type.index() as usize]
                .fields
                .push(new_id);
            self.field_by_full_name
                .insert(other_field.full_name_id, new_id);
            self.fields_by_type
                .entry(new_defining_type)
                .or_default()
                .insert(other_field.name_id, new_id);
        }

        // Fourth pass: fix extends relationships
        for other_type in &other.type_defs {
            let new_id = type_id_map[&other_type.id];
            let extends: Vec<TypeDefId> = other_type
                .extends
                .iter()
                .map(|&parent_id| type_id_map[&parent_id])
                .collect();
            self.type_defs[new_id.index() as usize].extends = extends;
        }

        // Merge functions
        for (name_id, func_id) in &other.function_by_name {
            if !self.function_by_name.contains_key(name_id) {
                let other_func = &other.function_defs[func_id.index() as usize];
                let new_id = FunctionId::new(self.function_defs.len() as u32);
                let mut new_func = other_func.clone();
                new_func.id = new_id;
                self.function_defs.push(new_func);
                self.function_by_name.insert(*name_id, new_id);
            }
        }
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

        let method_id =
            registry.register_method(type_id, method_name, full_method_name, signature, false);

        assert_eq!(
            registry.find_method_on_type(type_id, method_name),
            Some(method_id)
        );
        assert_eq!(registry.get_method(method_id).defining_type, type_id);
        assert_eq!(
            registry.methods_on_type(type_id).collect::<Vec<_>>(),
            vec![method_id]
        );
    }

    #[test]
    fn register_and_lookup_field() {
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();
        let type_name = names.intern_raw(main_mod, &["Point"]);
        let field_name = names.intern_raw(builtin_mod, &["x"]);
        let full_field_name = names.intern_raw(main_mod, &["Point", "x"]);

        let mut registry = EntityRegistry::new();
        let type_id = registry.register_type(type_name, TypeDefKind::Record, main_mod);

        let field_id = registry.register_field(type_id, field_name, full_field_name, Type::I32, 0);

        assert_eq!(
            registry.find_field_on_type(type_id, field_name),
            Some(field_id)
        );
        assert_eq!(registry.get_field(field_id).defining_type, type_id);
        assert_eq!(registry.get_field(field_id).slot, 0);
        assert_eq!(
            registry.fields_on_type(type_id).collect::<Vec<_>>(),
            vec![field_id]
        );
    }

    #[test]
    fn register_and_lookup_function() {
        let mut names = NameTable::new();
        let math_mod = names.module_id("math");
        let func_name = names.intern_raw(math_mod, &["sin"]);

        let mut registry = EntityRegistry::new();

        let signature = FunctionType {
            params: vec![Type::F64],
            return_type: Box::new(Type::F64),
            is_closure: false,
        };

        let func_id = registry.register_function(
            func_name, func_name, // For simple functions, name_id == full_name_id
            math_mod, signature,
        );

        assert_eq!(registry.function_by_name(func_name), Some(func_id));
        assert_eq!(registry.get_function(func_id).module, math_mod);
    }

    #[test]
    fn hierarchy_extends() {
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let base_name = names.intern_raw(main_mod, &["Base"]);
        let derived_name = names.intern_raw(main_mod, &["Derived"]);

        let mut registry = EntityRegistry::new();
        let base_id = registry.register_type(base_name, TypeDefKind::Interface, main_mod);
        let derived_id = registry.register_type(derived_name, TypeDefKind::Interface, main_mod);

        registry.add_extends(derived_id, base_id);

        assert!(registry.type_extends(derived_id, base_id));
        assert!(registry.type_extends(derived_id, derived_id)); // reflexive
        assert!(!registry.type_extends(base_id, derived_id)); // not reverse
    }

    #[test]
    fn resolve_inherited_method() {
        let mut names = NameTable::new();
        let main_mod = names.main_module();
        let builtin_mod = names.builtin_module();

        let base_name = names.intern_raw(main_mod, &["Base"]);
        let derived_name = names.intern_raw(main_mod, &["Derived"]);
        let method_name = names.intern_raw(builtin_mod, &["foo"]);
        let full_method_name = names.intern_raw(main_mod, &["Base", "foo"]);

        let mut registry = EntityRegistry::new();
        let base_id = registry.register_type(base_name, TypeDefKind::Interface, main_mod);
        let derived_id = registry.register_type(derived_name, TypeDefKind::Interface, main_mod);

        let signature = FunctionType {
            params: vec![],
            return_type: Box::new(Type::Void),
            is_closure: false,
        };

        let method_id =
            registry.register_method(base_id, method_name, full_method_name, signature, false);
        registry.add_extends(derived_id, base_id);

        // Method should be found on base directly
        assert_eq!(
            registry.find_method_on_type(base_id, method_name),
            Some(method_id)
        );
        // Method should NOT be found directly on derived
        assert_eq!(registry.find_method_on_type(derived_id, method_name), None);
        // But resolve_method should find it via inheritance
        assert_eq!(
            registry.resolve_method(derived_id, method_name),
            Some(method_id)
        );
        // all_methods should include inherited
        assert_eq!(registry.all_methods(derived_id), vec![method_id]);
    }
}

//! Method registration and lookup for EntityRegistry.

use crate::entity_defs::MethodDef;
use crate::generic::TypeParamInfo;
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::{TypeArena, TypeId};
use std::collections::HashSet;
use vole_frontend::Expr;
use vole_identity::{MethodId, NameId, TypeDefId};

use super::EntityRegistry;

impl EntityRegistry {
    /// Register a new method on a type
    pub fn register_method(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
    ) -> MethodId {
        self.register_method_with_binding(
            defining_type,
            name_id,
            full_name_id,
            signature_id,
            has_default,
            None,
        )
    }

    /// Register a new method on a type with optional external binding
    #[allow(clippy::too_many_arguments)]
    pub fn register_method_with_binding(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
        external_binding: Option<ExternalMethodInfo>,
    ) -> MethodId {
        let id = MethodId::new(self.method_defs.len() as u32);
        self.method_defs.push(MethodDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            signature_id,
            has_default,
            is_static: false,
            external_binding,
            method_type_params: Vec::new(),
            required_params: 0, // Will be updated if defaults are present
            param_defaults: Vec::new(),
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

    /// Register a new static method on a type
    #[allow(clippy::too_many_arguments)]
    pub fn register_static_method(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
        method_type_params: Vec<TypeParamInfo>,
    ) -> MethodId {
        self.register_static_method_with_defaults(
            defining_type,
            name_id,
            full_name_id,
            signature_id,
            has_default,
            None,
            method_type_params,
            0,
            Vec::new(),
        )
    }

    /// Register a new static method on a type with required_params and param_defaults
    #[allow(clippy::too_many_arguments)]
    pub fn register_static_method_with_defaults(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
        external_binding: Option<ExternalMethodInfo>,
        method_type_params: Vec<TypeParamInfo>,
        required_params: usize,
        param_defaults: Vec<Option<Box<Expr>>>,
    ) -> MethodId {
        let id = MethodId::new(self.method_defs.len() as u32);
        self.method_defs.push(MethodDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            signature_id,
            has_default,
            is_static: true,
            external_binding,
            method_type_params,
            required_params,
            param_defaults,
        });
        self.method_by_full_name.insert(full_name_id, id);
        self.static_methods_by_type
            .get_mut(&defining_type)
            .expect("type must be registered before adding static methods")
            .insert(name_id, id);
        self.type_defs[defining_type.index() as usize]
            .static_methods
            .push(id);
        id
    }

    /// Register a new static method on a type with optional external binding
    #[allow(clippy::too_many_arguments)]
    pub fn register_static_method_with_binding(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
        external_binding: Option<ExternalMethodInfo>,
        method_type_params: Vec<TypeParamInfo>,
    ) -> MethodId {
        self.register_static_method_with_defaults(
            defining_type,
            name_id,
            full_name_id,
            signature_id,
            has_default,
            external_binding,
            method_type_params,
            0,
            Vec::new(),
        )
    }

    /// Register a new instance method on a type with required_params and param_defaults
    #[allow(clippy::too_many_arguments)]
    pub fn register_method_with_defaults(
        &mut self,
        defining_type: TypeDefId,
        name_id: NameId,
        full_name_id: NameId,
        signature_id: TypeId,
        has_default: bool,
        external_binding: Option<ExternalMethodInfo>,
        required_params: usize,
        param_defaults: Vec<Option<Box<Expr>>>,
    ) -> MethodId {
        let id = MethodId::new(self.method_defs.len() as u32);
        self.method_defs.push(MethodDef {
            id,
            name_id,
            full_name_id,
            defining_type,
            signature_id,
            has_default,
            is_static: false,
            external_binding,
            method_type_params: Vec::new(),
            required_params,
            param_defaults,
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

    /// Get all static methods defined directly on a type
    pub fn static_methods_on_type(
        &self,
        type_id: TypeDefId,
    ) -> impl Iterator<Item = MethodId> + '_ {
        self.type_defs[type_id.index() as usize]
            .static_methods
            .iter()
            .copied()
    }

    /// Find a static method on a type by its short name
    pub fn find_static_method_on_type(
        &self,
        type_id: TypeDefId,
        name_id: NameId,
    ) -> Option<MethodId> {
        self.static_methods_by_type
            .get(&type_id)
            .and_then(|methods| methods.get(&name_id).copied())
    }

    /// Get a method definition by ID
    pub fn get_method(&self, id: MethodId) -> &MethodDef {
        &self.method_defs[id.index() as usize]
    }

    /// Update the return type of a method (used for return type inference).
    /// Creates a new function type in the arena with the updated return type.
    pub fn update_method_return_type(
        &mut self,
        method_id: MethodId,
        return_type: TypeId,
        arena: &mut TypeArena,
    ) {
        let method = &self.method_defs[method_id.index() as usize];
        let old_sig_id = method.signature_id;

        // Get the old function's params and is_closure from arena
        let (params, _old_ret, is_closure) = arena
            .unwrap_function(old_sig_id)
            .expect("method signature must be a function type");
        let params = params.clone();

        // Create new function type with updated return type
        let new_sig_id = arena.function(params, return_type, is_closure);

        // Update the method's signature_id
        self.method_defs[method_id.index() as usize].signature_id = new_sig_id;
    }

    /// Get all methods defined directly on a type (not inherited)
    pub fn methods_on_type(&self, type_id: TypeDefId) -> impl Iterator<Item = MethodId> + '_ {
        self.type_defs[type_id.index() as usize]
            .methods
            .iter()
            .copied()
    }

    /// Find a method on a type by its short name (not inherited)
    #[must_use]
    pub fn find_method_on_type(&self, type_id: TypeDefId, name_id: NameId) -> Option<MethodId> {
        self.methods_by_type
            .get(&type_id)
            .and_then(|methods| methods.get(&name_id).copied())
    }

    /// Resolve a method on a type, checking inherited methods too
    #[must_use]
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
    #[must_use]
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
    #[must_use]
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
}

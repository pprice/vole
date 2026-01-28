//! Method registration and lookup for EntityRegistry.

use crate::entity_defs::MethodDef;
use crate::generic::TypeParamInfo;
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::{TypeArena, TypeId};
use std::collections::HashSet;
use vole_frontend::Expr;
use vole_identity::{MethodId, NameId, NameTable, TypeDefId};

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
        // If signature is invalid (unknown type), don't update - error already reported
        let Some((params, _old_ret, is_closure)) = arena.unwrap_function(old_sig_id) else {
            return;
        };
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

    /// Register interface default methods on an implementing type.
    ///
    /// When a type implements an interface, the interface's default methods
    /// should be accessible via `find_method_on_type` on the implementing type.
    /// Creates new MethodDef entries with the implementing type's qualified name
    /// (e.g., `MyRecord::greaterThan` instead of `Comparable::greaterThan`).
    pub fn register_interface_default_methods_on_implementing_type(
        &mut self,
        implementing_type_id: TypeDefId,
        interface_type_id: TypeDefId,
        names: &mut NameTable,
    ) {
        // Collect interface default methods (methods with has_default=true)
        // that the implementing type doesn't already override.
        let implementing_has_method = |name_id: NameId| -> bool {
            self.methods_by_type
                .get(&implementing_type_id)
                .is_some_and(|methods| methods.contains_key(&name_id))
        };

        let interface_methods: Vec<MethodDef> = self.type_defs[interface_type_id.index() as usize]
            .methods
            .iter()
            .filter_map(|&method_id| {
                let method = &self.method_defs[method_id.index() as usize];
                if method.has_default && !implementing_has_method(method.name_id) {
                    Some(method.clone())
                } else {
                    None
                }
            })
            .collect();

        // Build the implementing type's name segments for constructing full_name_ids
        let impl_type_name_id = self.type_defs[implementing_type_id.index() as usize].name_id;

        // Register new MethodDefs with the implementing type's qualified name
        for interface_method in interface_methods {
            // Build full_name_id: e.g., MyRecord::greaterThan
            let method_short_name = names
                .last_segment_str(interface_method.name_id)
                .expect("method name must have at least one segment");
            let impl_name = names.name(impl_type_name_id);
            let module = impl_name.module();
            let mut segments: Vec<String> = impl_name.segments().to_vec();
            segments.push(method_short_name);
            let segment_refs: Vec<&str> = segments.iter().map(|s| s.as_str()).collect();
            let full_name_id = names.intern_raw(module, &segment_refs);

            let new_id = MethodId::new(self.method_defs.len() as u32);
            self.method_defs.push(MethodDef {
                id: new_id,
                name_id: interface_method.name_id,
                full_name_id,
                defining_type: implementing_type_id,
                signature_id: interface_method.signature_id,
                has_default: interface_method.has_default,
                is_static: interface_method.is_static,
                external_binding: interface_method.external_binding,
                method_type_params: interface_method.method_type_params.clone(),
                required_params: interface_method.required_params,
                param_defaults: interface_method.param_defaults.clone(),
            });
            self.method_by_full_name.insert(full_name_id, new_id);
            self.methods_by_type
                .get_mut(&implementing_type_id)
                .expect("implementing type must be registered")
                .insert(interface_method.name_id, new_id);
            self.type_defs[implementing_type_id.index() as usize]
                .methods
                .push(new_id);
        }
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

    /// Get the vtable slot index for an interface method.
    ///
    /// Returns the 0-based index of the method in the vtable ordering.
    /// Parent interface methods come first, then the interface's own methods.
    /// This ordering must match the vtable layout in codegen.
    pub fn interface_method_slot(
        &self,
        interface_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<u32> {
        let methods = self.collect_interface_methods_ordered(interface_id);
        methods
            .iter()
            .position(|&mid| self.get_method(mid).name_id == method_name_id)
            .map(|i| i as u32)
    }

    /// Get all methods from an interface and its parents in vtable order.
    ///
    /// Parent interface methods come first, then the interface's own methods.
    /// This ordering must match the vtable layout in codegen.
    pub fn interface_methods_ordered(&self, interface_id: TypeDefId) -> Vec<MethodId> {
        self.collect_interface_methods_ordered(interface_id)
    }

    /// Collect all methods from an interface and its parents in vtable order.
    fn collect_interface_methods_ordered(&self, interface_id: TypeDefId) -> Vec<MethodId> {
        let mut methods = Vec::new();
        let mut seen_interfaces = HashSet::new();
        let mut seen_methods = HashSet::new();
        self.collect_interface_methods_inner(
            interface_id,
            &mut methods,
            &mut seen_interfaces,
            &mut seen_methods,
        );
        methods
    }

    fn collect_interface_methods_inner(
        &self,
        interface_id: TypeDefId,
        methods: &mut Vec<MethodId>,
        seen_interfaces: &mut HashSet<TypeDefId>,
        seen_methods: &mut HashSet<NameId>,
    ) {
        if !seen_interfaces.insert(interface_id) {
            return;
        }

        let interface = self.get_type(interface_id);

        // Process parent interfaces first (to match vtable order)
        for parent_id in interface.extends.clone() {
            self.collect_interface_methods_inner(parent_id, methods, seen_interfaces, seen_methods);
        }

        // Add this interface's methods
        for method_id in &interface.methods {
            let method = self.get_method(*method_id);
            if seen_methods.insert(method.name_id) {
                methods.push(*method_id);
            }
        }
    }
}

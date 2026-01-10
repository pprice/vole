use super::super::*;
use crate::identity::{MethodId, TypeDefId};
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::substitute_type;
use std::collections::{HashMap, HashSet};

impl Analyzer {
    /// Resolve a method on a type using EntityRegistry (TypeDefId-based)
    ///
    /// This is the EntityRegistry-based version of method resolution.
    /// Returns the MethodId if found on the type or its parent interfaces.
    pub fn find_method_via_entity_registry(
        &self,
        type_def_id: TypeDefId,
        method_name_id: NameId,
    ) -> Option<MethodId> {
        // Use EntityRegistry's resolve_method which handles inheritance
        self.entity_registry
            .resolve_method(type_def_id, method_name_id)
    }

    /// Resolve a method call using EntityRegistry when possible
    ///
    /// This method attempts to use EntityRegistry for method resolution,
    /// falling back to the traditional approach when EntityRegistry
    /// doesn't have the type registered.
    pub fn resolve_method_via_entity_registry(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // Try to get TypeDefId from the object type
        let type_def_id = self.get_type_def_id_for_type(object_type);

        if let Some(type_def_id) = type_def_id {
            // Get the method name_id
            let method_name_id = self.method_name_id(method_name, interner);

            // Try to find the method via EntityRegistry
            if let Some(method_id) =
                self.find_method_via_entity_registry(type_def_id, method_name_id)
            {
                let method_def = self.entity_registry.get_method(method_id);
                let defining_type = self.entity_registry.get_type(method_def.defining_type);

                // Build substitutions for generic interface types
                let substitutions = self.build_interface_substitutions(object_type);
                let func_type = self.apply_substitutions(&method_def.signature, &substitutions);

                // Determine the resolution type based on the defining type's kind
                match defining_type.kind {
                    TypeDefKind::Interface => {
                        // This is an interface method - check if it has a default
                        if method_def.has_default {
                            // Get the implementing type's symbol for default method resolution
                            if let Some(type_name_id) = self.get_type_name_id(object_type) {
                                let type_sym =
                                    self.get_type_symbol_by_name_id(type_name_id, interner);
                                let interface_sym = self
                                    .get_type_symbol_by_name_id(defining_type.name_id, interner);
                                if let (Some(type_sym), Some(interface_sym)) =
                                    (type_sym, interface_sym)
                                {
                                    return Some(ResolvedMethod::DefaultMethod {
                                        interface_name: interface_sym,
                                        type_name: type_sym,
                                        method_name,
                                        func_type,
                                    });
                                }
                            }
                        }
                        // For non-default interface methods, use vtable dispatch
                        let interface_sym =
                            self.get_type_symbol_by_name_id(defining_type.name_id, interner);
                        if let Some(interface_sym) = interface_sym {
                            return Some(ResolvedMethod::InterfaceMethod {
                                interface_name: interface_sym,
                                method_name,
                                func_type,
                            });
                        }
                    }
                    TypeDefKind::Class | TypeDefKind::Record => {
                        // Direct method on class/record
                        return Some(ResolvedMethod::Direct { func_type });
                    }
                    _ => {}
                }
            }
        }

        // Fall back to traditional resolution
        self.resolve_method(object_type, method_name, interner)
    }

    /// Build substitution map for generic interface types
    fn build_interface_substitutions(&self, object_type: &Type) -> HashMap<NameId, Type> {
        let mut substitutions = HashMap::new();

        // Extract type_args from the object type
        let (name_id, type_args) = match object_type {
            Type::Interface(iface) => (Some(iface.name_id), iface.type_args.as_slice()),
            Type::GenericInstance { def, args } => (Some(*def), args.as_slice()),
            _ => (None, &[] as &[Type]),
        };

        // Build substitutions from interface's type params to type args
        if let Some(name_id) = name_id
            && let Some(type_def_id) = self.entity_registry.type_by_name(name_id)
        {
            let type_def = self.entity_registry.get_type(type_def_id);
            for (param_name_id, arg) in type_def.type_params.iter().zip(type_args.iter()) {
                substitutions.insert(*param_name_id, arg.clone());
            }
        }

        substitutions
    }

    /// Apply substitutions to a function type
    fn apply_substitutions(
        &self,
        func_type: &FunctionType,
        substitutions: &HashMap<NameId, Type>,
    ) -> FunctionType {
        if substitutions.is_empty() {
            return func_type.clone();
        }

        FunctionType {
            params: func_type
                .params
                .iter()
                .map(|t| substitute_type(t, substitutions))
                .collect(),
            return_type: Box::new(substitute_type(&func_type.return_type, substitutions)),
            is_closure: func_type.is_closure,
        }
    }

    /// Get TypeDefId for a Type if it's registered in EntityRegistry
    fn get_type_def_id_for_type(&self, ty: &Type) -> Option<TypeDefId> {
        let name_id = match ty {
            Type::Class(c) => Some(c.name_id),
            Type::Record(r) => Some(r.name_id),
            Type::Interface(i) => Some(i.name_id),
            Type::GenericInstance { def, .. } => Some(*def),
            _ => None,
        }?;

        self.entity_registry.type_by_name(name_id)
    }

    /// Get the name_id for a type
    fn get_type_name_id(&self, ty: &Type) -> Option<NameId> {
        match ty {
            Type::Class(class_type) => Some(class_type.name_id),
            Type::Record(record_type) => Some(record_type.name_id),
            _ => None,
        }
    }

    /// Get the Symbol for a type by its NameId
    fn get_type_symbol_by_name_id(&self, name_id: NameId, interner: &Interner) -> Option<Symbol> {
        // Get the name string from name_table and look up Symbol via interner
        if let Some(name_str) = self.name_table.last_segment_str(name_id) {
            interner.lookup(&name_str)
        } else {
            None
        }
    }

    /// Resolve a method call to a normalized resolution for later validation/codegen.
    pub(crate) fn resolve_method(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // 1. Check implement registry (works for all types)
        let method_id = self.method_name_id(method_name, interner);
        if let Some(type_id) = TypeId::from_type(object_type, &self.type_table)
            && let Some(impl_) = self.implement_registry.get_method(&type_id, method_id)
        {
            return Some(ResolvedMethod::Implemented {
                trait_name: impl_.trait_name,
                func_type: impl_.func_type.clone(),
                is_builtin: impl_.is_builtin,
                external_info: impl_.external_info.clone(),
            });
        }

        // 2. Interface methods (vtable dispatch)
        // Handle both Type::Interface and Type::GenericInstance (for self-referential interface types)
        let (interface_name_id, type_args) = match object_type {
            Type::Interface(iface) => (Some(iface.name_id), iface.type_args.as_slice()),
            Type::GenericInstance { def, args } => (Some(*def), args.as_slice()),
            _ => (None, &[] as &[Type]),
        };
        if let Some(name_id) = interface_name_id
            && let Some(type_def_id) = self.entity_registry.type_by_name(name_id)
        {
            let interface_def = self.entity_registry.get_type(type_def_id);

            // Build substitution map from type params to type args
            let mut substitutions = HashMap::new();
            for (param_name_id, arg) in interface_def.type_params.iter().zip(type_args.iter()) {
                substitutions.insert(*param_name_id, arg.clone());
            }

            // Get interface Symbol by looking up from type_implements or by name
            let interface_sym = self
                .type_implements
                .values()
                .flat_map(|syms| syms.iter())
                .find(|&&sym| {
                    let sym_str = interner.resolve(sym);
                    self.name_table
                        .last_segment_str(name_id)
                        .is_some_and(|n| n == sym_str)
                })
                .copied()
                .or_else(|| {
                    self.name_table
                        .last_segment_str(name_id)
                        .and_then(|name_str| interner.lookup(&name_str))
                });

            // Traverse interface hierarchy via EntityRegistry
            let mut stack = vec![type_def_id];
            let mut seen = HashSet::new();
            while let Some(current_id) = stack.pop() {
                if !seen.insert(current_id) {
                    continue;
                }
                let def = self.entity_registry.get_type(current_id);

                // Resolve method name to string for cross-interner comparison
                let method_name_str = interner.resolve(method_name);
                for &method_id in &def.methods {
                    let method = self.entity_registry.get_method(method_id);
                    let method_name_from_id = self
                        .name_table
                        .last_segment_str(method.name_id)
                        .unwrap_or_default();

                    // Compare by string since interface was registered with different interner
                    if method_name_from_id == method_name_str {
                        let func_type = FunctionType {
                            params: method
                                .signature
                                .params
                                .iter()
                                .map(|t| substitute_type(t, &substitutions))
                                .collect(),
                            return_type: Box::new(substitute_type(
                                &method.signature.return_type,
                                &substitutions,
                            )),
                            is_closure: false,
                        };
                        // Check for external binding
                        if let Some(external_info) = self
                            .entity_registry
                            .get_external_binding(method_id)
                            .cloned()
                        {
                            return Some(ResolvedMethod::Implemented {
                                trait_name: interface_sym,
                                func_type,
                                is_builtin: false,
                                external_info: Some(external_info),
                            });
                        }
                        if let Some(interface_sym) = interface_sym {
                            return Some(ResolvedMethod::InterfaceMethod {
                                interface_name: interface_sym,
                                method_name,
                                func_type,
                            });
                        }
                    }
                }
                // Add parent interfaces to stack
                for &parent_id in &def.extends {
                    stack.push(parent_id);
                }
            }
        }

        // 3. Direct methods on class/record via EntityRegistry
        let (type_name_id, record_type_args) = match object_type {
            Type::Class(c) => (Some(c.name_id), None),
            Type::Record(r) => (
                Some(r.name_id),
                if r.type_args.is_empty() {
                    None
                } else {
                    Some(r.type_args.as_slice())
                },
            ),
            _ => (None, None),
        };
        if let Some(type_name_id) = type_name_id
            && let Some(type_def_id) = self.entity_registry.type_by_name(type_name_id)
        {
            let method_name_id = self.method_name_id(method_name, interner);
            // Look up method via EntityRegistry
            if let Some(method_id) = self
                .entity_registry
                .find_method_on_type(type_def_id, method_name_id)
            {
                let method_def = self.entity_registry.get_method(method_id);
                let func_type = method_def.signature.clone();

                // For generic records, substitute type args in the method signature
                // Find the generic record def by matching name_id
                let generic_def = self
                    .generic_records
                    .values()
                    .find(|def| def.name_id == type_name_id);
                if let (Some(type_args), Some(generic_def)) = (record_type_args, generic_def) {
                    let mut substitutions = HashMap::new();
                    for (param, arg) in generic_def.type_params.iter().zip(type_args.iter()) {
                        substitutions.insert(param.name_id, arg.clone());
                    }
                    let substituted_func_type = FunctionType {
                        params: func_type
                            .params
                            .iter()
                            .map(|t| substitute_type(t, &substitutions))
                            .collect(),
                        return_type: Box::new(substitute_type(
                            &func_type.return_type,
                            &substitutions,
                        )),
                        is_closure: func_type.is_closure,
                    };
                    return Some(ResolvedMethod::Direct {
                        func_type: substituted_func_type,
                    });
                }
                return Some(ResolvedMethod::Direct { func_type });
            }
        }

        // 4. Default methods from implemented interfaces
        // Find the type symbol by matching name_id via EntityRegistry
        let type_sym = match object_type {
            Type::Class(class_type) => {
                self.get_type_symbol_by_name_id(class_type.name_id, interner)
            }
            Type::Record(record_type) => {
                self.get_type_symbol_by_name_id(record_type.name_id, interner)
            }
            _ => None,
        };
        if let Some(type_sym) = type_sym
            && let Some(interfaces) = self.type_implements.get(&type_sym).cloned()
        {
            let method_name_str = interner.resolve(method_name);
            for interface_name in &interfaces {
                // Look up interface via Resolver with interface fallback
                let type_def_id = self
                    .resolver(interner)
                    .resolve_type_or_interface(*interface_name, &self.entity_registry);

                if let Some(type_def_id) = type_def_id {
                    let interface_def = self.entity_registry.get_type(type_def_id);
                    for &method_id in &interface_def.methods {
                        let method = self.entity_registry.get_method(method_id);
                        let def_method_name = self
                            .name_table
                            .last_segment_str(method.name_id)
                            .unwrap_or_default();
                        if def_method_name == method_name_str && method.has_default {
                            return Some(ResolvedMethod::DefaultMethod {
                                interface_name: *interface_name,
                                type_name: type_sym,
                                method_name,
                                func_type: method.signature.clone(),
                            });
                        }
                    }
                }
            }
        }

        None
    }

    /// Get the function type for a functional interface by NameId (cross-interner safe)
    pub(crate) fn get_functional_interface_type_by_name_id(
        &self,
        interface_name_id: NameId,
    ) -> Option<FunctionType> {
        let type_def_id = self.entity_registry.type_by_name(interface_name_id)?;
        let method_id = self.entity_registry.is_functional(type_def_id)?;
        let method = self.entity_registry.get_method(method_id);
        Some(FunctionType {
            params: method.signature.params.clone(),
            return_type: method.signature.return_type.clone(),
            is_closure: true,
        })
    }
}

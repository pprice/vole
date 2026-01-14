use super::super::*;
use crate::identity::{MethodId, TypeDefId};
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::substitute_type;
use crate::sema::types::NominalType;
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
    #[tracing::instrument(skip(self, interner), fields(method = %interner.resolve(method_name)))]
    pub fn resolve_method_via_entity_registry(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // Handle Type::TypeParam by looking up constraint interfaces
        if let Type::TypeParam(param_name_id) = object_type {
            return self.resolve_method_on_type_param(*param_name_id, method_name, interner);
        }

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
                        // For interface types, we MUST use vtable dispatch because we don't know
                        // the concrete type. Generators implement Iterator with their own next()
                        // method, so calling external functions directly would crash.
                        let is_interface_type =
                            matches!(object_type, Type::Nominal(NominalType::Interface(_)));

                        // For external default methods on CONCRETE types (not interface types),
                        // we can call the external directly
                        if method_def.has_default
                            && method_def.external_binding.is_some()
                            && !is_interface_type
                            && let Some(type_name_id) = self.get_type_name_id(object_type)
                        {
                            let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner);
                            let interface_sym =
                                self.get_type_symbol_by_name_id(defining_type.name_id, interner);
                            if let (Some(type_sym), Some(interface_sym)) = (type_sym, interface_sym)
                            {
                                return Some(ResolvedMethod::DefaultMethod {
                                    interface_name: interface_sym,
                                    type_name: type_sym,
                                    method_name,
                                    func_type,
                                    external_info: method_def.external_binding.clone(),
                                });
                            }
                        }

                        // For non-external default methods on concrete types (Class/Record),
                        // we can compile and call the default directly
                        if method_def.has_default
                            && matches!(
                                object_type,
                                Type::Nominal(NominalType::Class(_))
                                    | Type::Nominal(NominalType::Record(_))
                            )
                            && let Some(type_name_id) = self.get_type_name_id(object_type)
                        {
                            let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner);
                            let interface_sym =
                                self.get_type_symbol_by_name_id(defining_type.name_id, interner);
                            if let (Some(type_sym), Some(interface_sym)) = (type_sym, interface_sym)
                            {
                                return Some(ResolvedMethod::DefaultMethod {
                                    interface_name: interface_sym,
                                    type_name: type_sym,
                                    method_name,
                                    func_type,
                                    external_info: None,
                                });
                            }
                        }

                        // For interface types and non-default methods, use vtable dispatch
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
        // Extract type_def_id and type_args from nominal types
        if let Type::Nominal(n) = object_type {
            self.entity_registry
                .substitution_map(n.type_def_id(), n.type_args())
        } else {
            HashMap::new()
        }
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
        match ty {
            Type::Nominal(NominalType::Class(c)) => Some(c.type_def_id),
            Type::Nominal(NominalType::Record(r)) => Some(r.type_def_id),
            Type::Nominal(NominalType::Interface(i)) => Some(i.type_def_id),
            _ => None,
        }
    }

    /// Get the name_id for a type
    fn get_type_name_id(&self, ty: &Type) -> Option<NameId> {
        match ty {
            Type::Nominal(NominalType::Class(c)) => {
                Some(self.entity_registry.get_type(c.type_def_id).name_id)
            }
            Type::Nominal(NominalType::Record(r)) => {
                Some(self.entity_registry.get_type(r.type_def_id).name_id)
            }
            Type::Nominal(NominalType::Interface(interface_type)) => {
                Some(self.entity_registry.name_id(interface_type.type_def_id))
            }
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

    /// Resolve a method on a type parameter by looking up its constraint interfaces.
    /// Returns an InterfaceMethod resolution since the actual concrete type will be
    /// substituted at monomorphization time.
    fn resolve_method_on_type_param(
        &mut self,
        param_name_id: NameId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let method_name_str = interner.resolve(method_name);
        tracing::trace!(
            ?param_name_id,
            method = %method_name_str,
            "resolve_method_on_type_param: starting"
        );

        // Look up the type parameter in current_type_param_scope
        let type_param_scope = self.current_type_param_scope.as_ref()?;

        // Find the type parameter by name_id
        let type_param = type_param_scope
            .params()
            .iter()
            .find(|tp| tp.name_id == param_name_id);

        let type_param = match type_param {
            Some(tp) => tp,
            None => {
                tracing::trace!(?param_name_id, "type param not found in scope");
                return None;
            }
        };

        // Get the constraint (must be an interface constraint for method calls)
        let constraint = match type_param.constraint.as_ref() {
            Some(c) => c,
            None => {
                tracing::trace!(?param_name_id, "type param has no constraint");
                return None;
            }
        };

        let constraint_interfaces = match constraint {
            crate::sema::generic::TypeConstraint::Interface(symbols) => symbols,
            other => {
                tracing::trace!(?param_name_id, constraint = ?other, "constraint is not interface-based");
                return None; // Union/Structural constraints don't support method calls this way
            }
        };

        tracing::trace!(
            num_constraints = constraint_interfaces.len(),
            "searching constraint interfaces"
        );

        // Try to find the method in one of the constraint interfaces
        for interface_sym in constraint_interfaces {
            let interface_name = interner.resolve(*interface_sym);
            tracing::trace!(%interface_name, "checking interface");

            // Use resolve_type_or_interface to handle prelude interfaces like Hashable
            if let Some(interface_type_id) = self
                .resolver(interner)
                .resolve_type_or_interface(*interface_sym, &self.entity_registry)
            {
                let interface_def = self.entity_registry.get_type(interface_type_id);
                tracing::trace!(
                    ?interface_type_id,
                    num_methods = interface_def.methods.len(),
                    "found interface def"
                );

                // Search for the method in this interface
                for &method_id in &interface_def.methods {
                    let method_def = self.entity_registry.get_method(method_id);
                    let method_def_name = self
                        .name_table
                        .last_segment_str(method_def.name_id)
                        .unwrap_or_default();

                    tracing::trace!(
                        ?method_id,
                        found_method = %method_def_name,
                        looking_for = %method_name_str,
                        "checking method"
                    );

                    if method_def_name == method_name_str {
                        tracing::trace!(
                            ?method_id,
                            %interface_name,
                            "found method on constraint interface"
                        );
                        // Found the method - return InterfaceMethod resolution
                        // The actual dispatch will happen at runtime via vtable
                        return Some(ResolvedMethod::InterfaceMethod {
                            interface_name: *interface_sym,
                            method_name,
                            func_type: method_def.signature.clone(),
                        });
                    }
                }
            } else {
                tracing::trace!(%interface_name, "could not resolve interface");
            }
        }

        tracing::trace!(
            method = %method_name_str,
            ?param_name_id,
            "method not found on any constraint interface"
        );
        None
    }

    /// Resolve a method call to a normalized resolution for later validation/codegen.
    pub(crate) fn resolve_method(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        // 1. Check implement registry (works for all types)
        let method_name_id = self.method_name_id(method_name, interner);
        // Try EntityRegistry first for method bindings
        let type_def_id = object_type.type_def_id().or_else(|| {
            self.name_table
                .primitives
                .name_id_for_type(object_type)
                .and_then(|name_id| self.entity_registry.type_by_name(name_id))
        });
        if let Some(type_def_id) = type_def_id
            && let Some((interface_id, binding)) = self
                .entity_registry
                .find_method_binding_with_interface(type_def_id, method_name_id)
        {
            // Get trait name Symbol from interface_id
            let trait_name = self
                .name_table
                .last_segment_str(self.entity_registry.get_type(interface_id).name_id)
                .and_then(|s| interner.lookup(&s));
            return Some(ResolvedMethod::Implemented {
                trait_name,
                func_type: binding.func_type.clone(),
                is_builtin: binding.is_builtin,
                external_info: binding.external_info.clone(),
            });
        }
        // Fall back to old implement_registry for backward compatibility
        if let Some(type_id) = TypeId::from_type(
            object_type,
            &self.entity_registry.type_table,
            &self.entity_registry,
        ) && let Some(impl_) = self.implement_registry.get_method(&type_id, method_name_id)
        {
            return Some(ResolvedMethod::Implemented {
                trait_name: impl_.trait_name,
                func_type: impl_.func_type.clone(),
                is_builtin: impl_.is_builtin,
                external_info: impl_.external_info.clone(),
            });
        }

        // 2. Interface methods (vtable dispatch)
        let (interface_type_def_id, type_args): (Option<TypeDefId>, &[Type]) = match object_type {
            Type::Nominal(NominalType::Interface(iface)) => {
                (Some(iface.type_def_id), iface.type_args.as_slice())
            }
            _ => (None, &[]),
        };
        if let Some(type_def_id) = interface_type_def_id {
            let interface_def = self.entity_registry.get_type(type_def_id);
            let name_id = interface_def.name_id;

            // Build substitution map from type params to type args
            let substitutions = self
                .entity_registry
                .substitution_map(type_def_id, type_args);

            // Get interface Symbol by looking up from name_id
            let interface_sym = self
                .name_table
                .last_segment_str(name_id)
                .and_then(|name_str| interner.lookup(&name_str));

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
        let (type_def_id_opt, record_type_args) = match object_type {
            Type::Nominal(NominalType::Class(c)) => (Some(c.type_def_id), None),
            Type::Nominal(NominalType::Record(r)) => (
                Some(r.type_def_id),
                if r.type_args.is_empty() {
                    None
                } else {
                    Some(r.type_args.as_slice())
                },
            ),
            _ => (None, None),
        };
        if let Some(type_def_id) = type_def_id_opt {
            let method_name_id = self.method_name_id(method_name, interner);
            // Look up method via EntityRegistry
            if let Some(method_id) = self
                .entity_registry
                .find_method_on_type(type_def_id, method_name_id)
            {
                let method_def = self.entity_registry.get_method(method_id);
                let func_type = method_def.signature.clone();

                // For generic records, substitute type args in the method signature
                if let Some(type_args) = record_type_args {
                    let substitutions = self
                        .entity_registry
                        .substitution_map(type_def_id, type_args);
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
        // Get type_def_id from the object type (reusing earlier logic or via name_id)
        let type_def_id_opt = match object_type {
            Type::Nominal(NominalType::Class(c)) => Some(c.type_def_id),
            Type::Nominal(NominalType::Record(r)) => Some(r.type_def_id),
            _ => None,
        };
        if let Some(type_def_id) = type_def_id_opt {
            let type_name_id = self.entity_registry.get_type(type_def_id).name_id;
            let type_sym = self.get_type_symbol_by_name_id(type_name_id, interner);
            let method_name_str = interner.resolve(method_name);
            // Use EntityRegistry's implemented interfaces
            for interface_id in self.entity_registry.get_implemented_interfaces(type_def_id) {
                let interface_def = self.entity_registry.get_type(interface_id);
                for &method_id in &interface_def.methods {
                    let method = self.entity_registry.get_method(method_id);
                    let def_method_name = self
                        .name_table
                        .last_segment_str(method.name_id)
                        .unwrap_or_default();
                    if def_method_name == method_name_str && method.has_default {
                        // Get interface name Symbol
                        let interface_name = self
                            .name_table
                            .last_segment_str(interface_def.name_id)
                            .and_then(|s| interner.lookup(&s))
                            .unwrap_or(Symbol(0));
                        return Some(ResolvedMethod::DefaultMethod {
                            interface_name,
                            type_name: type_sym?, // Extract from Option
                            method_name,
                            func_type: method.signature.clone(),
                            external_info: method.external_binding.clone(),
                        });
                    }
                }
            }
        }

        None
    }

    /// Get the function type for a functional interface by TypeDefId
    pub(crate) fn get_functional_interface_type_by_type_def_id(
        &self,
        type_def_id: TypeDefId,
    ) -> Option<FunctionType> {
        let method_id = self.entity_registry.is_functional(type_def_id)?;
        let method = self.entity_registry.get_method(method_id);
        Some(FunctionType {
            params: method.signature.params.clone(),
            return_type: method.signature.return_type.clone(),
            is_closure: true,
        })
    }
}

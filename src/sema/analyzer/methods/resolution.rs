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

                // Determine the resolution type based on the defining type's kind
                match defining_type.kind {
                    TypeDefKind::Interface => {
                        // This is an interface method - check if it has a default
                        if method_def.has_default {
                            // Get the implementing type's symbol for default method resolution
                            let type_sym = self.get_type_symbol(object_type);
                            if let Some(type_sym) = type_sym {
                                let interface_sym =
                                    self.get_type_symbol_by_name_id(defining_type.name_id);
                                if let Some(interface_sym) = interface_sym {
                                    return Some(ResolvedMethod::DefaultMethod {
                                        interface_name: interface_sym,
                                        type_name: type_sym,
                                        method_name,
                                        func_type: method_def.signature.clone(),
                                    });
                                }
                            }
                        }
                        // For non-default interface methods, use vtable dispatch
                        let interface_sym = self.get_type_symbol_by_name_id(defining_type.name_id);
                        if let Some(interface_sym) = interface_sym {
                            return Some(ResolvedMethod::InterfaceMethod {
                                interface_name: interface_sym,
                                method_name,
                                func_type: method_def.signature.clone(),
                            });
                        }
                    }
                    TypeDefKind::Class | TypeDefKind::Record => {
                        // Direct method on class/record
                        return Some(ResolvedMethod::Direct {
                            func_type: method_def.signature.clone(),
                        });
                    }
                    _ => {}
                }
            }
        }

        // Fall back to traditional resolution
        self.resolve_method(object_type, method_name, interner)
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

    /// Get the Symbol for a type (for compatibility with existing code)
    fn get_type_symbol(&self, ty: &Type) -> Option<Symbol> {
        match ty {
            Type::Class(class_type) => self
                .classes
                .iter()
                .find(|(_, c)| c.name_id == class_type.name_id)
                .map(|(sym, _)| *sym),
            Type::Record(record_type) => self
                .records
                .iter()
                .find(|(_, r)| r.name_id == record_type.name_id)
                .map(|(sym, _)| *sym),
            _ => None,
        }
    }

    /// Get the Symbol for a type by its NameId
    fn get_type_symbol_by_name_id(&self, name_id: NameId) -> Option<Symbol> {
        // Check classes
        for (sym, class) in &self.classes {
            if class.name_id == name_id {
                return Some(*sym);
            }
        }
        // Check records
        for (sym, record) in &self.records {
            if record.name_id == name_id {
                return Some(*sym);
            }
        }
        // For interfaces, we need to look up the Symbol another way
        // The Symbol is stored in the type_implements map values
        // or we can get the name string from the name_table
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
            for (param_sym, arg) in interface_def
                .type_params_symbols
                .iter()
                .zip(type_args.iter())
            {
                substitutions.insert(*param_sym, arg.clone());
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

        // 3. Direct methods on class/record
        let (type_id, record_type_args) = match object_type {
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
        if let Some(type_id) = type_id {
            let method_id = self.method_name_id(method_name, interner);
            if let Some(func_type) = self.methods.get(&(type_id, method_id)).cloned() {
                // For generic records, substitute type args in the method signature
                // Find the generic record def by matching name_id
                let generic_def = self
                    .generic_records
                    .values()
                    .find(|def| def.name_id == type_id);
                if let (Some(type_args), Some(generic_def)) = (record_type_args, generic_def) {
                    let mut substitutions = HashMap::new();
                    for (param, arg) in generic_def.type_params.iter().zip(type_args.iter()) {
                        substitutions.insert(param.name, arg.clone());
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
        // Find the type symbol by matching name_id (classes/records are keyed by Symbol)
        let type_sym = match object_type {
            Type::Class(class_type) => self
                .classes
                .iter()
                .find(|(_, c)| c.name_id == class_type.name_id)
                .map(|(sym, _)| *sym),
            Type::Record(record_type) => self
                .records
                .iter()
                .find(|(_, r)| r.name_id == record_type.name_id)
                .map(|(sym, _)| *sym),
            _ => None,
        };
        if let Some(type_sym) = type_sym
            && let Some(interfaces) = self.type_implements.get(&type_sym).cloned()
        {
            let method_name_str = interner.resolve(method_name);
            for interface_name in &interfaces {
                // Look up interface via EntityRegistry
                let interface_str = interner.resolve(*interface_name);
                let type_def_id = self
                    .name_table
                    .name_id_raw(self.current_module, &[interface_str])
                    .and_then(|name_id| self.entity_registry.type_by_name(name_id))
                    .or_else(|| {
                        self.entity_registry
                            .interface_by_short_name(interface_str, &self.name_table)
                    });

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

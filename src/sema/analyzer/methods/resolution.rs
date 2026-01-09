use super::super::*;
use crate::sema::generic::substitute_type;
use std::collections::{HashMap, HashSet};

impl Analyzer {
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
            && let Some(interface_def) = self.interface_registry.get_by_name_id(name_id)
        {
            let mut substitutions = HashMap::new();
            for (param, arg) in interface_def.type_params.iter().zip(type_args.iter()) {
                substitutions.insert(*param, arg.clone());
            }

            let mut stack = vec![interface_def];
            let mut seen = HashSet::new();
            while let Some(def) = stack.pop() {
                if !seen.insert(def.name) {
                    continue;
                }
                // Resolve method name to string for cross-interner comparison
                let method_name_str = interner.resolve(method_name);
                for method_def in &def.methods {
                    // Compare by string since interface was registered with different interner
                    if method_def.name_str == method_name_str {
                        let func_type = FunctionType {
                            params: method_def
                                .params
                                .iter()
                                .map(|t| substitute_type(t, &substitutions))
                                .collect(),
                            return_type: Box::new(substitute_type(
                                &method_def.return_type,
                                &substitutions,
                            )),
                            is_closure: false,
                        };
                        if let Some(external_info) =
                            def.external_methods.get(method_name_str).cloned()
                        {
                            return Some(ResolvedMethod::Implemented {
                                trait_name: Some(def.name),
                                func_type,
                                is_builtin: false,
                                external_info: Some(external_info),
                            });
                        }
                        return Some(ResolvedMethod::InterfaceMethod {
                            interface_name: interface_def.name,
                            method_name,
                            func_type,
                        });
                    }
                }
                for parent in &def.extends {
                    if let Some(parent_def) = self.interface_registry.get(*parent, interner) {
                        stack.push(parent_def);
                    }
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
            for interface_name in &interfaces {
                if let Some(interface_def) = self.interface_registry.get(*interface_name, interner)
                {
                    for method_def in &interface_def.methods {
                        if method_def.name == method_name && method_def.has_default {
                            return Some(ResolvedMethod::DefaultMethod {
                                interface_name: *interface_name,
                                type_name: type_sym,
                                method_name,
                                func_type: FunctionType {
                                    params: method_def.params.clone(),
                                    return_type: Box::new(method_def.return_type.clone()),
                                    is_closure: false,
                                },
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
        let method = self
            .interface_registry
            .is_functional_by_name_id(interface_name_id)?;
        Some(FunctionType {
            params: method.params.clone(),
            return_type: Box::new(method.return_type.clone()),
            is_closure: true,
        })
    }
}

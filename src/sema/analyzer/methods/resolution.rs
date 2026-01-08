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
        if let Type::Interface(iface) = object_type
            && let Some(interface_def) = self.interface_registry.get(iface.name, interner)
        {
            let mut substitutions = HashMap::new();
            for (param, arg) in interface_def.type_params.iter().zip(iface.type_args.iter()) {
                substitutions.insert(*param, arg.clone());
            }

            let mut stack = vec![interface_def];
            let mut seen = HashSet::new();
            while let Some(def) = stack.pop() {
                if !seen.insert(def.name) {
                    continue;
                }
                for method_def in &def.methods {
                    if method_def.name == method_name {
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
                        if let Some(external_info) = def.external_methods.get(&method_name).cloned()
                        {
                            return Some(ResolvedMethod::Implemented {
                                trait_name: Some(def.name),
                                func_type,
                                is_builtin: false,
                                external_info: Some(external_info),
                            });
                        }
                        return Some(ResolvedMethod::InterfaceMethod {
                            interface_name: iface.name,
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
        let type_id = match object_type {
            Type::Class(c) => Some(c.name_id),
            Type::Record(r) => Some(r.name_id),
            _ => None,
        };
        if let Some(type_id) = type_id {
            let method_id = self.method_name_id(method_name, interner);
            if let Some(func_type) = self.methods.get(&(type_id, method_id)).cloned() {
                return Some(ResolvedMethod::Direct { func_type });
            }
        }

        // 4. Default methods from implemented interfaces
        let type_sym = match object_type {
            Type::Class(class_type) => Some(class_type.name),
            Type::Record(record_type) => Some(record_type.name),
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

    /// Get the function type for a functional interface (single abstract method, no fields)
    pub(crate) fn get_functional_interface_type(
        &self,
        interface_name: Symbol,
        interner: &Interner,
    ) -> Option<FunctionType> {
        let method = self
            .interface_registry
            .is_functional(interface_name, interner)?;
        Some(FunctionType {
            params: method.params.clone(),
            return_type: Box::new(method.return_type.clone()),
            is_closure: true,
        })
    }
}

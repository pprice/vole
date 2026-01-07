use super::super::*;

#[allow(dead_code)]
impl Analyzer {
    /// Resolve a method call and record the resolution for codegen
    pub(crate) fn resolve_method_call(
        &mut self,
        object_type: &Type,
        method_name: Symbol,
        call_node_id: NodeId,
        interner: &Interner,
    ) -> Option<ResolvedMethod> {
        let method_str = interner.resolve(method_name);

        // 1. Check built-in methods (array/string.length)
        if let Some(return_type) = self.check_builtin_method_for_resolution(object_type, method_str)
        {
            let resolved = ResolvedMethod::Implemented {
                trait_name: None, // Will be Sized eventually
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(return_type),
                    is_closure: false,
                },
                is_builtin: true,
                external_info: None,
            };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
        }

        // 2. Check direct methods on type (classes/records)
        let type_id = match object_type {
            Type::Class(c) => Some(c.name_id),
            Type::Record(r) => Some(r.name_id),
            _ => None,
        };
        if let Some(type_id) = type_id {
            let method_id = self.method_name_id(method_name, interner);
            if let Some(func_type) = self.methods.get(&(type_id, method_id)).cloned() {
                let resolved = ResolvedMethod::Direct { func_type };
                self.method_resolutions
                    .insert(call_node_id, resolved.clone());
                return Some(resolved);
            }
        }

        // 3. Check implement registry
        let method_id = self.method_name_id(method_name, interner);
        if let Some(type_id) = TypeId::from_type(object_type, &self.type_table)
            && let Some(impl_) = self.implement_registry.get_method(&type_id, method_id)
        {
            let resolved = ResolvedMethod::Implemented {
                trait_name: impl_.trait_name,
                func_type: impl_.func_type.clone(),
                is_builtin: impl_.is_builtin,
                external_info: impl_.external_info.clone(),
            };
            self.method_resolutions
                .insert(call_node_id, resolved.clone());
            return Some(resolved);
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

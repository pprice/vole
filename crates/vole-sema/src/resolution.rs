// src/sema/resolution.rs

use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId;
use std::collections::HashMap;
use vole_frontend::{NodeId, Symbol};
use vole_identity::{MethodId, TypeDefId};

/// Resolved method information - sema populates, codegen consumes
/// Use arena.unwrap_function(func_type_id) to get params/return type
#[derive(Debug, Clone)]
pub enum ResolvedMethod {
    /// Direct method on class/record
    Direct {
        func_type_id: TypeId,
        method_id: Option<MethodId>,
    },

    /// Method from implement registry
    Implemented {
        trait_name: Option<Symbol>,
        func_type_id: TypeId,
        is_builtin: bool,
        external_info: Option<ExternalMethodInfo>,
    },

    /// Functional interface - call the underlying lambda
    FunctionalInterface { func_type_id: TypeId },

    /// Default method from interface (monomorphized for concrete type)
    /// The method is compiled as TypeName_methodName
    DefaultMethod {
        interface_name: Symbol,
        type_name: Symbol,
        method_name: Symbol,
        func_type_id: TypeId,
        external_info: Option<ExternalMethodInfo>,
    },

    /// Method called through a non-functional interface value (vtable dispatch)
    InterfaceMethod {
        interface_name: Symbol,
        method_name: Symbol,
        func_type_id: TypeId,
    },

    /// Static method on a type (called via TypeName.method())
    Static {
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: TypeId,
    },
}

impl ResolvedMethod {
    /// Get the interned function type ID (pre-computed by sema)
    /// Use arena.unwrap_function(id) to get (params, ret, is_closure)
    pub fn func_type_id(&self) -> TypeId {
        match self {
            ResolvedMethod::Direct { func_type_id, .. } => *func_type_id,
            ResolvedMethod::Implemented { func_type_id, .. } => *func_type_id,
            ResolvedMethod::FunctionalInterface { func_type_id } => *func_type_id,
            ResolvedMethod::DefaultMethod { func_type_id, .. } => *func_type_id,
            ResolvedMethod::InterfaceMethod { func_type_id, .. } => *func_type_id,
            ResolvedMethod::Static { func_type_id, .. } => *func_type_id,
        }
    }

    /// Check if this is a builtin method
    pub fn is_builtin(&self) -> bool {
        matches!(
            self,
            ResolvedMethod::Implemented {
                is_builtin: true,
                ..
            }
        )
    }

    /// Get external info if this is an external method
    pub fn external_info(&self) -> Option<&ExternalMethodInfo> {
        match self {
            ResolvedMethod::Implemented { external_info, .. } => external_info.as_ref(),
            ResolvedMethod::DefaultMethod { external_info, .. } => external_info.as_ref(),
            _ => None,
        }
    }

    /// Get method_id if available (for Direct and Static variants)
    pub fn method_id(&self) -> Option<MethodId> {
        match self {
            ResolvedMethod::Direct { method_id, .. } => *method_id,
            ResolvedMethod::Static { method_id, .. } => Some(*method_id),
            _ => None,
        }
    }
}

/// Storage for all method resolutions in a program
#[derive(Debug, Default, Clone)]
pub struct MethodResolutions {
    resolutions: HashMap<NodeId, ResolvedMethod>,
}

impl MethodResolutions {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a method resolution
    pub fn insert(&mut self, node_id: NodeId, resolved: ResolvedMethod) {
        self.resolutions.insert(node_id, resolved);
    }

    /// Look up a method resolution
    pub fn get(&self, node_id: NodeId) -> Option<&ResolvedMethod> {
        self.resolutions.get(&node_id)
    }

    /// Consume and return the inner HashMap
    pub fn into_inner(self) -> HashMap<NodeId, ResolvedMethod> {
        self.resolutions
    }

    /// Clone the inner HashMap without consuming self
    pub fn clone_inner(&self) -> HashMap<NodeId, ResolvedMethod> {
        self.resolutions.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeArena;
    use crate::types::FunctionType;

    #[test]
    fn resolved_method_func_type_id() {
        let mut arena = TypeArena::new();
        let ft = FunctionType::from_ids(&[arena.i32()], arena.bool(), false);
        let ft_id = ft.intern(&mut arena);

        let direct = ResolvedMethod::Direct {
            func_type_id: ft_id,
            method_id: None,
        };
        assert_eq!(direct.func_type_id(), ft_id);
        // Verify we can get params from arena
        let (params, ret, _) = arena.unwrap_function(ft_id).unwrap();
        assert_eq!(params.len(), 1);
        assert_eq!(ret, arena.bool());

        let implemented = ResolvedMethod::Implemented {
            trait_name: None,
            func_type_id: ft_id,
            is_builtin: true,
            external_info: None,
        };
        assert!(implemented.is_builtin());
    }

    #[test]
    fn method_resolutions_storage() {
        let mut arena = TypeArena::new();
        let mut resolutions = MethodResolutions::new();
        let node_id = NodeId(42);

        let ft = FunctionType::from_ids(&[], arena.void(), false);
        let ft_id = ft.intern(&mut arena);
        resolutions.insert(
            node_id,
            ResolvedMethod::Direct {
                func_type_id: ft_id,
                method_id: None,
            },
        );

        assert!(resolutions.get(node_id).is_some());
        assert!(resolutions.get(NodeId(999)).is_none());
    }
}

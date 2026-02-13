// src/sema/resolution.rs

use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId;
use rustc_hash::FxHashMap;
use vole_frontend::{NodeId, Symbol};
use vole_identity::{MethodId, NameId, TypeDefId};

/// Resolved method information - sema populates, codegen consumes
/// The `return_type_id` field provides direct access to the return type,
/// eliminating the need for `arena.unwrap_function(func_type_id)` in codegen.
#[derive(Debug, Clone)]
pub enum ResolvedMethod {
    /// Direct method on class
    Direct {
        type_def_id: Option<TypeDefId>,
        method_name_id: NameId,
        func_type_id: TypeId,
        return_type_id: TypeId,
        method_id: Option<MethodId>,
    },

    /// Method from implement registry
    Implemented {
        type_def_id: Option<TypeDefId>,
        method_name_id: NameId,
        trait_name: Option<Symbol>,
        func_type_id: TypeId,
        return_type_id: TypeId,
        is_builtin: bool,
        external_info: Option<ExternalMethodInfo>,
        /// Concrete runtime type hint for codegen. For builtin iterators
        /// (array.iter(), string.iter(), range.iter()), this is the RuntimeIterator(T)
        /// type. Codegen can use this instead of creating the type itself.
        concrete_return_hint: Option<TypeId>,
    },

    /// Functional interface - call the underlying lambda
    FunctionalInterface {
        method_name_id: NameId,
        func_type_id: TypeId,
        return_type_id: TypeId,
    },

    /// Default method from interface (monomorphized for concrete type)
    /// The method is compiled as TypeName_methodName
    DefaultMethod {
        type_def_id: Option<TypeDefId>,
        method_name_id: NameId,
        interface_name: Symbol,
        type_name: Symbol,
        method_name: Symbol,
        func_type_id: TypeId,
        return_type_id: TypeId,
        external_info: Option<ExternalMethodInfo>,
    },

    /// Method called through a non-functional interface value (vtable dispatch)
    InterfaceMethod {
        method_name_id: NameId,
        interface_name: Symbol,
        method_name: Symbol,
        func_type_id: TypeId,
        return_type_id: TypeId,
        /// The interface's TypeDefId (for vtable lookup)
        interface_type_def_id: TypeDefId,
        /// The vtable slot index (pre-computed by sema)
        method_index: u32,
    },

    /// Static method on a type (called via TypeName.method())
    Static {
        method_name_id: NameId,
        type_def_id: TypeDefId,
        method_id: MethodId,
        func_type_id: TypeId,
        return_type_id: TypeId,
    },
}

impl ResolvedMethod {
    /// Get the interned function type ID (pre-computed by sema)
    /// Use arena.unwrap_function(id) to get (params, ret, is_closure)
    pub fn func_type_id(&self) -> TypeId {
        match self {
            ResolvedMethod::Direct { func_type_id, .. } => *func_type_id,
            ResolvedMethod::Implemented { func_type_id, .. } => *func_type_id,
            ResolvedMethod::FunctionalInterface { func_type_id, .. } => *func_type_id,
            ResolvedMethod::DefaultMethod { func_type_id, .. } => *func_type_id,
            ResolvedMethod::InterfaceMethod { func_type_id, .. } => *func_type_id,
            ResolvedMethod::Static { func_type_id, .. } => *func_type_id,
        }
    }

    /// Get the return type ID (pre-computed by sema)
    /// This eliminates the need for arena.unwrap_function() in codegen.
    pub fn return_type_id(&self) -> TypeId {
        match self {
            ResolvedMethod::Direct { return_type_id, .. } => *return_type_id,
            ResolvedMethod::Implemented { return_type_id, .. } => *return_type_id,
            ResolvedMethod::FunctionalInterface { return_type_id, .. } => *return_type_id,
            ResolvedMethod::DefaultMethod { return_type_id, .. } => *return_type_id,
            ResolvedMethod::InterfaceMethod { return_type_id, .. } => *return_type_id,
            ResolvedMethod::Static { return_type_id, .. } => *return_type_id,
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
            ResolvedMethod::Direct { .. }
            | ResolvedMethod::FunctionalInterface { .. }
            | ResolvedMethod::InterfaceMethod { .. }
            | ResolvedMethod::Static { .. } => None,
        }
    }

    /// Get method_id if available (for Direct and Static variants)
    pub fn method_id(&self) -> Option<MethodId> {
        match self {
            ResolvedMethod::Direct { method_id, .. } => *method_id,
            ResolvedMethod::Static { method_id, .. } => Some(*method_id),
            ResolvedMethod::Implemented { .. }
            | ResolvedMethod::FunctionalInterface { .. }
            | ResolvedMethod::DefaultMethod { .. }
            | ResolvedMethod::InterfaceMethod { .. } => None,
        }
    }

    /// Get the type_def_id if available (for Direct, Implemented, DefaultMethod, and Static variants)
    pub fn type_def_id(&self) -> Option<TypeDefId> {
        match self {
            ResolvedMethod::Direct { type_def_id, .. } => *type_def_id,
            ResolvedMethod::Implemented { type_def_id, .. } => *type_def_id,
            ResolvedMethod::DefaultMethod { type_def_id, .. } => *type_def_id,
            ResolvedMethod::Static { type_def_id, .. } => Some(*type_def_id),
            ResolvedMethod::FunctionalInterface { .. } => None,
            ResolvedMethod::InterfaceMethod {
                interface_type_def_id,
                ..
            } => Some(*interface_type_def_id),
        }
    }

    /// Get the method_name_id (available for all variants)
    pub fn method_name_id(&self) -> NameId {
        match self {
            ResolvedMethod::Direct { method_name_id, .. } => *method_name_id,
            ResolvedMethod::Implemented { method_name_id, .. } => *method_name_id,
            ResolvedMethod::FunctionalInterface { method_name_id, .. } => *method_name_id,
            ResolvedMethod::DefaultMethod { method_name_id, .. } => *method_name_id,
            ResolvedMethod::InterfaceMethod { method_name_id, .. } => *method_name_id,
            ResolvedMethod::Static { method_name_id, .. } => *method_name_id,
        }
    }

    /// Get the method_index for InterfaceMethod (vtable slot)
    pub fn method_index(&self) -> Option<u32> {
        match self {
            ResolvedMethod::InterfaceMethod { method_index, .. } => Some(*method_index),
            ResolvedMethod::Direct { .. }
            | ResolvedMethod::Implemented { .. }
            | ResolvedMethod::FunctionalInterface { .. }
            | ResolvedMethod::DefaultMethod { .. }
            | ResolvedMethod::Static { .. } => None,
        }
    }

    /// Get the concrete_return_hint for Implemented methods.
    /// This provides the actual runtime type when it differs from the declared return type.
    /// For builtin iterators (array.iter(), string.iter(), range.iter()), this is RuntimeIterator(T).
    pub fn concrete_return_hint(&self) -> Option<TypeId> {
        match self {
            ResolvedMethod::Implemented {
                concrete_return_hint,
                ..
            } => *concrete_return_hint,
            ResolvedMethod::Direct { .. }
            | ResolvedMethod::FunctionalInterface { .. }
            | ResolvedMethod::DefaultMethod { .. }
            | ResolvedMethod::InterfaceMethod { .. }
            | ResolvedMethod::Static { .. } => None,
        }
    }
}

/// Storage for all method resolutions in a program
#[derive(Debug, Default, Clone)]
pub struct MethodResolutions {
    resolutions: FxHashMap<NodeId, ResolvedMethod>,
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

    /// Consume and return the inner FxHashMap
    pub fn into_inner(self) -> FxHashMap<NodeId, ResolvedMethod> {
        self.resolutions
    }

    /// Clone the inner FxHashMap without consuming self
    pub fn clone_inner(&self) -> FxHashMap<NodeId, ResolvedMethod> {
        self.resolutions.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeArena;
    use crate::types::FunctionType;

    // Create a test NameId for use in tests
    fn test_method_name_id() -> NameId {
        NameId::new_for_test(1)
    }

    #[test]
    fn resolved_method_func_type_id() {
        let mut arena = TypeArena::new();
        let ret_type = arena.bool();
        let ft = FunctionType::unary(arena.i32(), ret_type);
        let ft_id = ft.intern(&mut arena);
        let method_name_id = test_method_name_id();

        let direct = ResolvedMethod::Direct {
            type_def_id: None,
            method_name_id,
            func_type_id: ft_id,
            return_type_id: ret_type,
            method_id: None,
        };
        assert_eq!(direct.func_type_id(), ft_id);
        assert_eq!(direct.return_type_id(), ret_type);
        assert_eq!(direct.method_name_id(), method_name_id);
        assert!(direct.type_def_id().is_none());
        // Verify we can get params from arena
        let (params, ret, _) = arena.unwrap_function(ft_id).unwrap();
        assert_eq!(params.len(), 1);
        assert_eq!(ret, arena.bool());

        let implemented = ResolvedMethod::Implemented {
            type_def_id: None,
            method_name_id,
            trait_name: None,
            func_type_id: ft_id,
            return_type_id: ret_type,
            is_builtin: true,
            external_info: None,
            concrete_return_hint: None,
        };
        assert!(implemented.is_builtin());
        assert_eq!(implemented.return_type_id(), ret_type);
        assert_eq!(implemented.method_name_id(), method_name_id);
        assert!(implemented.concrete_return_hint().is_none());

        // Test with concrete_return_hint set
        let iter_elem = arena.i64();
        let runtime_iter = arena.runtime_iterator(iter_elem);
        let with_hint = ResolvedMethod::Implemented {
            type_def_id: None,
            method_name_id,
            trait_name: None,
            func_type_id: ft_id,
            return_type_id: ret_type,
            is_builtin: true,
            external_info: None,
            concrete_return_hint: Some(runtime_iter),
        };
        assert_eq!(with_hint.concrete_return_hint(), Some(runtime_iter));
        // Verify the hint is a RuntimeIterator
        assert!(arena.is_runtime_iterator(runtime_iter));
        assert_eq!(arena.unwrap_runtime_iterator(runtime_iter), Some(iter_elem));
    }

    #[test]
    fn method_resolutions_storage() {
        let mut arena = TypeArena::new();
        let mut resolutions = MethodResolutions::new();
        let node_id = NodeId(42);
        let method_name_id = test_method_name_id();

        let ft = FunctionType::void(&arena);
        let ft_id = ft.intern(&mut arena);
        let ret_type = arena.void();
        resolutions.insert(
            node_id,
            ResolvedMethod::Direct {
                type_def_id: None,
                method_name_id,
                func_type_id: ft_id,
                return_type_id: ret_type,
                method_id: None,
            },
        );

        assert!(resolutions.get(node_id).is_some());
        assert!(resolutions.get(NodeId(999)).is_none());
    }
}

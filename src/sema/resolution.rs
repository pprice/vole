// src/sema/resolution.rs

use crate::frontend::{NodeId, Symbol};
use crate::sema::types::FunctionType;
use std::collections::HashMap;

/// Resolved method information - sema populates, codegen consumes
#[derive(Debug, Clone)]
pub enum ResolvedMethod {
    /// Direct method on class/record
    Direct { func_type: FunctionType },

    /// Method from implement registry
    Implemented {
        trait_name: Option<Symbol>,
        func_type: FunctionType,
        is_builtin: bool,
    },

    /// Functional interface - call the underlying lambda
    FunctionalInterface { func_type: FunctionType },
}

impl ResolvedMethod {
    /// Get the function type regardless of resolution kind
    pub fn func_type(&self) -> &FunctionType {
        match self {
            ResolvedMethod::Direct { func_type } => func_type,
            ResolvedMethod::Implemented { func_type, .. } => func_type,
            ResolvedMethod::FunctionalInterface { func_type } => func_type,
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::types::Type;

    #[test]
    fn resolved_method_func_type() {
        let ft = FunctionType {
            params: vec![Type::I32],
            return_type: Box::new(Type::Bool),
            is_closure: false,
        };

        let direct = ResolvedMethod::Direct {
            func_type: ft.clone(),
        };
        assert_eq!(direct.func_type().params.len(), 1);

        let implemented = ResolvedMethod::Implemented {
            trait_name: None,
            func_type: ft.clone(),
            is_builtin: true,
        };
        assert!(implemented.is_builtin());
    }

    #[test]
    fn method_resolutions_storage() {
        let mut resolutions = MethodResolutions::new();
        let node_id = NodeId(42);

        resolutions.insert(
            node_id,
            ResolvedMethod::Direct {
                func_type: FunctionType {
                    params: vec![],
                    return_type: Box::new(Type::Void),
                    is_closure: false,
                },
            },
        );

        assert!(resolutions.get(node_id).is_some());
        assert!(resolutions.get(NodeId(999)).is_none());
    }
}

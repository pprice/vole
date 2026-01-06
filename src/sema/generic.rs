// src/sema/generic.rs
//
// Generic type parameter handling for Vole.
// This module provides structures for tracking type parameters in scope
// and will later support monomorphization.

use crate::frontend::Symbol;
use crate::sema::types::Type;

/// Information about a type parameter in scope
#[derive(Debug, Clone)]
pub struct TypeParamInfo {
    /// The name of the type parameter (e.g., T, U)
    pub name: Symbol,
    /// Optional constraint on the type parameter
    pub constraint: Option<TypeConstraint>,
}

/// Resolved constraint for type parameter checking
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Interface constraint: T: Stringable
    Interface(Symbol),
    /// Union constraint: T: i32 | i64
    Union(Vec<Type>),
}

/// Tracks type parameters currently in scope during type checking.
/// Used when analyzing generic functions, records, classes, etc.
#[derive(Debug, Default)]
pub struct TypeParamScope {
    /// Type parameters in the current scope
    params: Vec<TypeParamInfo>,
}

impl TypeParamScope {
    /// Create a new empty scope
    pub fn new() -> Self {
        Self { params: Vec::new() }
    }

    /// Add a type parameter to the scope
    pub fn add(&mut self, param: TypeParamInfo) {
        self.params.push(param);
    }

    /// Look up a type parameter by name
    pub fn get(&self, name: Symbol) -> Option<&TypeParamInfo> {
        self.params.iter().find(|p| p.name == name)
    }

    /// Check if a symbol refers to a type parameter in scope
    pub fn is_type_param(&self, name: Symbol) -> bool {
        self.params.iter().any(|p| p.name == name)
    }

    /// Get all type parameters in scope
    pub fn params(&self) -> &[TypeParamInfo] {
        &self.params
    }

    /// Clear all type parameters (when exiting generic context)
    pub fn clear(&mut self) {
        self.params.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_param_scope() {
        let mut scope = TypeParamScope::new();

        // Symbol(0) for testing - in real code these come from interner
        let t = Symbol(0);
        scope.add(TypeParamInfo {
            name: t,
            constraint: None,
        });

        assert!(scope.is_type_param(t));
        assert!(scope.get(t).is_some());

        // Different symbol should not be found
        let u = Symbol(1);
        assert!(!scope.is_type_param(u));
        assert!(scope.get(u).is_none());
    }
}

// src/sema/generic.rs
//
// Generic type parameter handling for Vole.
// This module provides structures for tracking type parameters in scope
// and supports monomorphization of generic functions.

use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId};
use vole_frontend::Symbol;
use vole_identity::{NameId, TypeParamId};

// Re-export monomorphization types from vole-identity for backward compatibility.
pub use vole_identity::{
    ClassMethodMonomorphCache, ClassMethodMonomorphInstance, ClassMethodMonomorphKey,
    ExternalMethodInfo, MonomorphCache, MonomorphCacheBase, MonomorphInstance,
    MonomorphInstanceTrait, MonomorphKey, StaticMethodMonomorphCache,
    StaticMethodMonomorphInstance, StaticMethodMonomorphKey,
};

// ============================================================================
// Type Parameter Handling
// ============================================================================

/// Variance of a type parameter.
///
/// Variance describes how a type parameter relates to subtyping:
/// - Covariant: if T is a subtype of U, then F<T> is a subtype of F<U>
/// - Contravariant: if T is a subtype of U, then F<U> is a subtype of F<T>
/// - Invariant: F<T> and F<U> are unrelated unless T = U
/// - Bivariant: F<T> is both a subtype and supertype of F<U> (rare, usually error)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[expect(dead_code)]
pub(crate) enum TypeParamVariance {
    /// Type can vary in the same direction as its container.
    /// Used for return types, read-only fields, iterators.
    #[default]
    Covariant,
    /// Type varies in the opposite direction of its container.
    /// Used for function parameter types.
    Contravariant,
    /// Type cannot vary at all.
    /// Used when type appears in both input and output positions.
    Invariant,
    /// Type can vary in any direction.
    /// Rarely useful, indicates the type param is unused.
    Bivariant,
}

impl TypeParamVariance {
    /// Combine two variance positions.
    /// Used when a type param appears in multiple positions.
    #[expect(dead_code)]
    pub fn combine(self, other: TypeParamVariance) -> TypeParamVariance {
        use TypeParamVariance::*;
        match (self, other) {
            // Same variance is preserved
            (Covariant, Covariant) => Covariant,
            (Contravariant, Contravariant) => Contravariant,
            (Invariant, _) | (_, Invariant) => Invariant,
            (Bivariant, v) | (v, Bivariant) => v,
            // Different non-bi variances become invariant
            (Covariant, Contravariant) | (Contravariant, Covariant) => Invariant,
        }
    }

    /// Flip variance (used when entering contravariant position like function params).
    #[expect(dead_code)]
    pub fn flip(self) -> TypeParamVariance {
        use TypeParamVariance::*;
        match self {
            Covariant => Contravariant,
            Contravariant => Covariant,
            Invariant => Invariant,
            Bivariant => Bivariant,
        }
    }
}

/// Information about a type parameter in scope
#[derive(Debug, Clone)]
pub struct TypeParamInfo {
    /// The name of the type parameter as Symbol (for parsing/resolution stage)
    pub name: Symbol,
    /// The name of the type parameter as NameId (for type substitution)
    pub name_id: NameId,
    /// Optional constraint on the type parameter
    pub constraint: Option<TypeConstraint>,
    /// Unique identifier for this type parameter.
    /// This provides a stable identity that can be used to distinguish
    /// between different type parameters that might have the same NameId.
    pub type_param_id: Option<TypeParamId>,
    /// Variance of this type parameter (computed from usage positions).
    /// Defaults to Covariant for simple cases.
    #[expect(dead_code)]
    pub(crate) variance: TypeParamVariance,
}

/// Registry for allocating and looking up TypeParamIds.
#[derive(Debug, Default)]
pub struct TypeParamRegistry {
    /// Maps TypeParamId -> (NameId, Symbol) for lookups
    params: Vec<(NameId, Symbol)>,
}

impl TypeParamRegistry {
    pub fn new() -> Self {
        Self { params: Vec::new() }
    }

    /// Allocate a new TypeParamId for a type parameter.
    pub fn allocate(&mut self, name_id: NameId, name: Symbol) -> TypeParamId {
        let id = TypeParamId::new(self.params.len() as u32);
        self.params.push((name_id, name));
        id
    }

    /// Look up the NameId for a TypeParamId (for substitution).
    pub fn get_name_id(&self, id: TypeParamId) -> Option<NameId> {
        self.params
            .get(id.index() as usize)
            .map(|(name_id, _)| *name_id)
    }

    /// Look up the Symbol for a TypeParamId (for display).
    pub fn get_symbol(&self, id: TypeParamId) -> Option<Symbol> {
        self.params.get(id.index() as usize).map(|(_, sym)| *sym)
    }
}

impl Clone for TypeParamRegistry {
    fn clone(&self) -> Self {
        Self {
            params: self.params.clone(),
        }
    }
}

/// Merge two type parameter lists into one.
/// This is useful for combining class type params with method type params.
pub(crate) fn merge_type_params(
    base: &[TypeParamInfo],
    additional: &[TypeParamInfo],
) -> Vec<TypeParamInfo> {
    base.iter().chain(additional.iter()).cloned().collect()
}

/// A resolved interface constraint item, with optional type arguments.
/// E.g., `Stringable` (no type args) or `Producer<T>` (with type arg T as ArenaTypeId).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintInterfaceItem {
    /// Interface name (cross-interner safe)
    pub name: String,
    /// Resolved type argument TypeIds (empty for non-parameterized interfaces)
    pub type_args: Vec<ArenaTypeId>,
}

/// Resolved constraint for type parameter checking
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Interface constraints: T: Stringable or T: Hashable + Eq or T: Producer<U>
    /// Stored as String names (not Symbol) for cross-interner safety.
    Interface(Vec<ConstraintInterfaceItem>),
    /// Union constraint: T: i32 | i64 (TypeId version)
    UnionId(Vec<ArenaTypeId>),
    /// Structural constraint: T: { name: string, func get() -> i32 }
    Structural(InternedStructural),
    /// Built-in Sendable constraint: T: Sendable
    /// Checked by walking the type tree, not by interface satisfaction.
    Sendable,
}

/// Tracks type parameters currently in scope during type checking.
/// Used when analyzing generic functions, records, classes, etc.
#[derive(Debug, Default, Clone)]
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

    /// Look up a type parameter by NameId
    pub fn get_by_name_id(&self, name_id: NameId) -> Option<&TypeParamInfo> {
        self.params.iter().find(|p| p.name_id == name_id)
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

    /// Check if the scope is empty
    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    /// Get the number of type parameters in scope
    pub fn len(&self) -> usize {
        self.params.len()
    }

    /// Create a new scope that combines this scope's params with additional params.
    /// This is useful for method type checking where class type params need
    /// to be merged with method-specific type params.
    pub fn merge_with(&self, additional: &[TypeParamInfo]) -> TypeParamScope {
        let mut merged = self.clone();
        merged.extend(additional);
        merged
    }

    /// Extend this scope with additional type parameters (cloning from slice).
    pub fn extend(&mut self, params: &[TypeParamInfo]) {
        self.params.extend(params.iter().cloned());
    }

    /// Extend this scope with owned type parameters (no cloning).
    pub fn extend_owned(&mut self, params: impl IntoIterator<Item = TypeParamInfo>) {
        self.params.extend(params);
    }

    /// Create a scope from a Vec of TypeParamInfo (takes ownership).
    pub fn from_params(params: Vec<TypeParamInfo>) -> Self {
        Self { params }
    }

    /// Consume the scope and return the owned params (avoids cloning).
    pub fn into_params(self) -> Vec<TypeParamInfo> {
        self.params
    }

    /// Clone params into a new Vec (explicit cloning when needed).
    pub fn to_params(&self) -> Vec<TypeParamInfo> {
        self.params.clone()
    }
}

/// Stack of type parameter scopes for nested generic contexts.
/// Provides push/pop semantics for entering/exiting generic functions,
/// methods, classes, records, and lambdas.
#[derive(Debug, Default, Clone)]
pub struct TypeParamScopeStack {
    /// Stack of scopes, with the innermost (current) scope at the end
    scopes: Vec<TypeParamScope>,
}

impl TypeParamScopeStack {
    /// Create a new empty stack
    pub fn new() -> Self {
        Self { scopes: Vec::new() }
    }

    /// Push a new scope onto the stack with the given type parameters
    pub fn push(&mut self, params: Vec<TypeParamInfo>) {
        let mut scope = TypeParamScope::new();
        for param in params {
            scope.add(param);
        }
        self.scopes.push(scope);
    }

    /// Push an existing scope onto the stack
    pub fn push_scope(&mut self, scope: TypeParamScope) {
        self.scopes.push(scope);
    }

    /// Pop the current scope from the stack
    pub fn pop(&mut self) -> Option<TypeParamScope> {
        self.scopes.pop()
    }

    /// Get the current (innermost) scope, if any
    pub fn current(&self) -> Option<&TypeParamScope> {
        self.scopes.last()
    }

    /// Get the current (innermost) scope mutably, if any
    pub fn current_mut(&mut self) -> Option<&mut TypeParamScope> {
        self.scopes.last_mut()
    }

    /// Look up a type parameter by Symbol in any scope (innermost first)
    pub fn get(&self, name: Symbol) -> Option<&TypeParamInfo> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name))
    }

    /// Look up a type parameter by NameId in any scope (innermost first)
    pub fn get_by_name_id(&self, name_id: NameId) -> Option<&TypeParamInfo> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get_by_name_id(name_id))
    }

    /// Look up a type parameter by TypeParamId in any scope (innermost first)
    pub fn get_by_type_param_id(&self, type_param_id: TypeParamId) -> Option<&TypeParamInfo> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.params())
            .find(|param| param.type_param_id == Some(type_param_id))
    }

    /// Check if a symbol refers to a type parameter in any scope
    pub fn is_type_param(&self, name: Symbol) -> bool {
        self.get(name).is_some()
    }

    /// Check if there are any scopes on the stack
    pub fn is_empty(&self) -> bool {
        self.scopes.is_empty()
    }

    /// Get the depth of the stack (number of nested scopes)
    pub fn depth(&self) -> usize {
        self.scopes.len()
    }

    /// Get all type parameters from all scopes (for merging contexts)
    pub fn all_params(&self) -> Vec<TypeParamInfo> {
        self.scopes
            .iter()
            .flat_map(|s| s.params().iter().cloned())
            .collect()
    }

    /// Create a merged scope containing all type parameters from all scopes
    pub fn merged_scope(&self) -> TypeParamScope {
        let mut merged = TypeParamScope::new();
        for scope in &self.scopes {
            for param in scope.params() {
                merged.add(param.clone());
            }
        }
        merged
    }

    /// Push a merged scope that combines the current scope with additional params.
    /// This is useful for methods in generic classes where we need both
    /// the class's type params and the method's type params.
    pub fn push_merged(&mut self, additional_params: Vec<TypeParamInfo>) {
        let mut merged = self.merged_scope();
        for param in additional_params {
            merged.add(param);
        }
        self.scopes.push(merged);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeArena;
    use rustc_hash::FxHashMap;

    #[test]
    fn test_type_param_scope() {
        let mut names = vole_identity::NameTable::new();
        let mut scope = TypeParamScope::new();

        // Symbol for testing - in real code these come from interner
        let t = Symbol::new_for_test(0);
        let t_name_id = names.intern_raw(names.main_module(), &["T"]);
        scope.add(TypeParamInfo {
            name: t,
            name_id: t_name_id,
            constraint: None,
            type_param_id: None,
            variance: TypeParamVariance::default(),
        });

        assert!(scope.is_type_param(t));
        assert!(scope.get(t).is_some());

        // Different symbol should not be found
        let u = Symbol::new_for_test(1);
        assert!(!scope.is_type_param(u));
        assert!(scope.get(u).is_none());
    }

    #[test]
    fn test_monomorph_cache() {
        let arena = TypeArena::new();
        let mut cache = MonomorphCache::new();
        let mut names = vole_identity::NameTable::new();
        let mut interner = vole_frontend::Interner::new();
        let func_sym = interner.intern("foo");
        let func_name = names.intern(names.main_module(), &[func_sym], &interner);

        // Use ArenaTypeId directly (TypeKey is no longer needed)
        let key1 = MonomorphKey::new(func_name, vec![arena.i64()]);
        let key2 = MonomorphKey::new(func_name, vec![arena.string()]);
        let key1_dup = MonomorphKey::new(func_name, vec![arena.i64()]);

        assert!(!cache.contains(&key1));

        cache.insert(
            key1.clone(),
            MonomorphInstance {
                original_name: func_name,
                mangled_name: names.intern_raw(names.main_module(), &["foo__mono_0"]),
                instance_id: 0,
                func_type: vole_identity::FunctionType::unary(arena.i64(), arena.i64()),
                substitutions: FxHashMap::default(),
            },
        );

        assert!(cache.contains(&key1));
        assert!(cache.contains(&key1_dup)); // Same types = same key
        assert!(!cache.contains(&key2)); // Different types = different key
    }
}

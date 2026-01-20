// src/sema/generic.rs
//
// Generic type parameter handling for Vole.
// This module provides structures for tracking type parameters in scope
// and supports monomorphization of generic functions.

use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::{InternedStructural, TypeId as ArenaTypeId};
use crate::types::FunctionType;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};
use vole_frontend::Symbol;
use vole_identity::{NameId, TypeParamId};

// ============================================================================
// Generic Monomorphization Cache
// ============================================================================

/// Generic cache for monomorphized instances.
///
/// This provides the common caching infrastructure used by:
/// - `MonomorphCache` (free functions)
/// - `ClassMethodMonomorphCache` (class instance methods)
/// - `StaticMethodMonomorphCache` (class static methods)
///
/// All caches share the same structure: a HashMap from keys to instances,
/// plus a counter for generating unique mangled names.
///
/// Also tracks cache hit/miss statistics for debugging monomorphization performance.
#[derive(Debug)]
pub struct MonomorphCacheBase<K, V> {
    instances: HashMap<K, V>,
    next_id: u32,
    /// Number of cache hits (successful lookups). Uses AtomicU32 for thread-safe interior mutability.
    hits: AtomicU32,
    /// Number of cache misses (failed lookups). Uses AtomicU32 for thread-safe interior mutability.
    misses: AtomicU32,
}

impl<K: Clone, V: Clone> Clone for MonomorphCacheBase<K, V> {
    fn clone(&self) -> Self {
        Self {
            instances: self.instances.clone(),
            next_id: self.next_id,
            hits: AtomicU32::new(self.hits.load(Ordering::Relaxed)),
            misses: AtomicU32::new(self.misses.load(Ordering::Relaxed)),
        }
    }
}

impl<K: Hash + Eq, V> Default for MonomorphCacheBase<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Hash + Eq, V> MonomorphCacheBase<K, V> {
    /// Create a new empty cache
    pub fn new() -> Self {
        Self {
            instances: HashMap::new(),
            next_id: 0,
            hits: AtomicU32::new(0),
            misses: AtomicU32::new(0),
        }
    }

    /// Look up an existing monomorphized instance.
    /// Tracks hit/miss statistics for performance debugging.
    pub fn get(&self, key: &K) -> Option<&V> {
        let result = self.instances.get(key);
        if result.is_some() {
            self.hits.fetch_add(1, Ordering::Relaxed);
        } else {
            self.misses.fetch_add(1, Ordering::Relaxed);
        }
        result
    }

    /// Insert a new monomorphized instance
    pub fn insert(&mut self, key: K, instance: V) {
        self.instances.insert(key, instance);
    }

    /// Check if an instance exists
    pub fn contains(&self, key: &K) -> bool {
        self.instances.contains_key(key)
    }

    /// Generate the next unique ID for mangled names
    pub fn next_unique_id(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Get all cached instances (for codegen)
    pub fn instances(&self) -> impl Iterator<Item = (&K, &V)> {
        self.instances.iter()
    }

    /// Collect all instances as owned values (for codegen iteration)
    /// This avoids cloning keys when only values are needed.
    pub fn collect_instances(&self) -> Vec<V>
    where
        V: Clone,
    {
        self.instances.values().cloned().collect()
    }

    // ========================================================================
    // Cache Metrics
    // ========================================================================

    /// Get the number of cache hits
    pub fn hit_count(&self) -> u32 {
        self.hits.load(Ordering::Relaxed)
    }

    /// Get the number of cache misses
    pub fn miss_count(&self) -> u32 {
        self.misses.load(Ordering::Relaxed)
    }

    /// Get the cache hit rate as a percentage (0.0 - 100.0).
    /// Returns 0.0 if no lookups have been performed.
    pub fn hit_rate(&self) -> f64 {
        let hits = self.hits.load(Ordering::Relaxed);
        let misses = self.misses.load(Ordering::Relaxed);
        let total = hits + misses;
        if total == 0 {
            0.0
        } else {
            (hits as f64 / total as f64) * 100.0
        }
    }

    /// Reset cache metrics to zero
    pub fn clear_metrics(&self) {
        self.hits.store(0, Ordering::Relaxed);
        self.misses.store(0, Ordering::Relaxed);
    }

    /// Print cache statistics for debugging
    pub fn print_stats(&self, cache_name: &str) {
        let hits = self.hits.load(Ordering::Relaxed);
        let misses = self.misses.load(Ordering::Relaxed);
        let total = hits + misses;
        let entries = self.instances.len();
        eprintln!(
            "[{}] entries: {}, lookups: {} (hits: {}, misses: {}, hit_rate: {:.1}%)",
            cache_name,
            entries,
            total,
            hits,
            misses,
            self.hit_rate()
        );
    }
}

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
pub enum TypeParamVariance {
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
    pub variance: TypeParamVariance,
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
/// This is useful for combining class/record type params with method type params.
pub fn merge_type_params(
    base: &[TypeParamInfo],
    additional: &[TypeParamInfo],
) -> Vec<TypeParamInfo> {
    base.iter().chain(additional.iter()).cloned().collect()
}

/// Resolved constraint for type parameter checking
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Interface constraints: T: Stringable or T: Hashable + Eq
    Interface(Vec<Symbol>),
    /// Union constraint: T: i32 | i64 (TypeId version)
    UnionId(Vec<ArenaTypeId>),
    /// Structural constraint: T: { name: string, func get() -> i32 }
    Structural(InternedStructural),
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
    /// This is useful for method type checking where class/record type params need
    /// to be merged with method-specific type params.
    pub fn merge_with(&self, additional: &[TypeParamInfo]) -> TypeParamScope {
        let mut merged = self.clone();
        merged.extend(additional);
        merged
    }

    /// Extend this scope with additional type parameters.
    pub fn extend(&mut self, params: &[TypeParamInfo]) {
        self.params.extend(params.iter().cloned());
    }

    /// Create a scope from a slice of TypeParamInfo.
    pub fn from_params(params: Vec<TypeParamInfo>) -> Self {
        Self { params }
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
        for scope in self.scopes.iter().rev() {
            if let Some(info) = scope.get(name) {
                return Some(info);
            }
        }
        None
    }

    /// Look up a type parameter by NameId in any scope (innermost first)
    pub fn get_by_name_id(&self, name_id: NameId) -> Option<&TypeParamInfo> {
        for scope in self.scopes.iter().rev() {
            if let Some(info) = scope.get_by_name_id(name_id) {
                return Some(info);
            }
        }
        None
    }

    /// Look up a type parameter by TypeParamId in any scope (innermost first)
    pub fn get_by_type_param_id(&self, type_param_id: TypeParamId) -> Option<&TypeParamInfo> {
        for scope in self.scopes.iter().rev() {
            for param in scope.params() {
                if param.type_param_id == Some(type_param_id) {
                    return Some(param);
                }
            }
        }
        None
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

/// Key for looking up monomorphized function instances.
/// Uses a string representation for hashability since Type doesn't implement Hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphKey {
    /// Original generic function name
    pub func_name: NameId,
    /// Opaque type keys for concrete types
    pub type_keys: Vec<ArenaTypeId>,
}

impl MonomorphKey {
    /// Create a key from function name and concrete type arguments
    pub fn new(func_name: NameId, type_keys: Vec<ArenaTypeId>) -> Self {
        Self {
            func_name,
            type_keys,
        }
    }
}

/// Common interface for all monomorphized instance types.
/// Provides access to shared fields needed during codegen.
pub trait MonomorphInstanceTrait {
    /// Get the mangled name for this instance
    fn mangled_name(&self) -> NameId;
    /// Get the unique instance ID
    fn instance_id(&self) -> u32;
    /// Get the concrete function type after substitution
    fn func_type(&self) -> &FunctionType;
    /// Get the type parameter substitutions (as TypeId handles)
    fn substitutions(&self) -> &HashMap<NameId, ArenaTypeId>;
}

/// A monomorphized function instance
#[derive(Debug, Clone)]
pub struct MonomorphInstance {
    /// Original generic function name
    pub original_name: NameId,
    /// Mangled name for this instance
    pub mangled_name: NameId,
    /// Unique ID for this instance (used to generate mangled name)
    pub instance_id: u32,
    /// The concrete function type after substitution
    pub func_type: FunctionType,
    /// Map from type param NameId to concrete type (as TypeId handles)
    pub substitutions: HashMap<NameId, ArenaTypeId>,
}

impl MonomorphInstanceTrait for MonomorphInstance {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &HashMap<NameId, ArenaTypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized function instances.
/// Maps (func_name, concrete_types) -> monomorphized function info.
pub type MonomorphCache = MonomorphCacheBase<MonomorphKey, MonomorphInstance>;

/// Key for looking up monomorphized class method instances.
/// Identifies a specific instantiation of a generic class method.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassMethodMonomorphKey {
    /// The class's NameId
    pub class_name: NameId,
    /// The method's NameId
    pub method_name: NameId,
    /// Opaque type keys for the class's concrete type arguments
    pub type_keys: Vec<ArenaTypeId>,
}

impl ClassMethodMonomorphKey {
    /// Create a new key for a class method monomorphization
    pub fn new(class_name: NameId, method_name: NameId, type_keys: Vec<ArenaTypeId>) -> Self {
        Self {
            class_name,
            method_name,
            type_keys,
        }
    }
}

/// A monomorphized class method instance
#[derive(Debug, Clone)]
pub struct ClassMethodMonomorphInstance {
    /// The class's NameId
    pub class_name: NameId,
    /// Original method name
    pub method_name: NameId,
    /// Mangled name for this instance (e.g., "Container_i64__compute_hash")
    pub mangled_name: NameId,
    /// Unique ID for this instance
    pub instance_id: u32,
    /// The concrete method type after substitution
    pub func_type: FunctionType,
    /// Map from type param NameId to concrete type (as TypeId handles)
    pub substitutions: HashMap<NameId, ArenaTypeId>,
    /// External method info (if this is an external method, call the runtime function)
    pub external_info: Option<ExternalMethodInfo>,
}

impl MonomorphInstanceTrait for ClassMethodMonomorphInstance {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &HashMap<NameId, ArenaTypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized class method instances.
pub type ClassMethodMonomorphCache =
    MonomorphCacheBase<ClassMethodMonomorphKey, ClassMethodMonomorphInstance>;

/// Key for looking up monomorphized static method instances on generic classes.
/// Identifies a specific instantiation of a generic class's static method.
/// Supports both class-level and method-level type parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StaticMethodMonomorphKey {
    /// The class's NameId
    pub class_name: NameId,
    /// The method's NameId
    pub method_name: NameId,
    /// Opaque type keys for the class's concrete type arguments (e.g., T in Box<T>)
    pub class_type_keys: Vec<ArenaTypeId>,
    /// Opaque type keys for the method's concrete type arguments (e.g., U in func convert<U>)
    pub method_type_keys: Vec<ArenaTypeId>,
}

impl StaticMethodMonomorphKey {
    /// Create a new key for a static method monomorphization
    pub fn new(
        class_name: NameId,
        method_name: NameId,
        class_type_keys: Vec<ArenaTypeId>,
        method_type_keys: Vec<ArenaTypeId>,
    ) -> Self {
        Self {
            class_name,
            method_name,
            class_type_keys,
            method_type_keys,
        }
    }
}

/// A monomorphized static method instance
#[derive(Debug, Clone)]
pub struct StaticMethodMonomorphInstance {
    /// The class's NameId
    pub class_name: NameId,
    /// Original method name
    pub method_name: NameId,
    /// Mangled name for this instance (e.g., "Box__static_create__mono_0")
    pub mangled_name: NameId,
    /// Unique ID for this instance
    pub instance_id: u32,
    /// The concrete method type after substitution
    pub func_type: FunctionType,
    /// Map from type param NameId to concrete type (as TypeId handles)
    pub substitutions: HashMap<NameId, ArenaTypeId>,
}

impl MonomorphInstanceTrait for StaticMethodMonomorphInstance {
    fn mangled_name(&self) -> NameId {
        self.mangled_name
    }
    fn instance_id(&self) -> u32 {
        self.instance_id
    }
    fn func_type(&self) -> &FunctionType {
        &self.func_type
    }
    fn substitutions(&self) -> &HashMap<NameId, ArenaTypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized static method instances.
pub type StaticMethodMonomorphCache =
    MonomorphCacheBase<StaticMethodMonomorphKey, StaticMethodMonomorphInstance>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeArena;

    #[test]
    fn test_type_param_scope() {
        let mut names = vole_identity::NameTable::new();
        let mut scope = TypeParamScope::new();

        // Symbol(0) for testing - in real code these come from interner
        let t = Symbol(0);
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
        let u = Symbol(1);
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
                func_type: FunctionType::from_ids(&[arena.i64()], arena.i64(), false),
                substitutions: HashMap::new(),
            },
        );

        assert!(cache.contains(&key1));
        assert!(cache.contains(&key1_dup)); // Same types = same key
        assert!(!cache.contains(&key2)); // Different types = different key
    }
}

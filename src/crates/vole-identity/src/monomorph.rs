// monomorph.rs
//
// Monomorphization key, instance, and cache types.
//
// These are pure data types that hold identity-level information (NameId, TypeId,
// FunctionType) with no sema dependencies. They live here so that both vole-sema
// and vole-codegen can use them without codegen reaching back into sema.

use crate::NameId;
use crate::function_type::FunctionType;
use crate::type_id::TypeId;
use rustc_hash::FxHashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicU32, Ordering};

// ============================================================================
// ExternalMethodInfo
// ============================================================================

/// Info for external (native) methods.
/// Both fields are interned as single-segment NameIds for cheap Copy.
/// Use name_table.last_segment_str(field) to get the string value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExternalMethodInfo {
    pub module_path: NameId,
    pub native_name: NameId,
}

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
    instances: FxHashMap<K, V>,
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
            instances: FxHashMap::default(),
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

    /// Collect all instances as owned (key, value) pairs.
    ///
    /// Used by VIR lowering to populate monomorph info maps that are
    /// keyed by the same key type as the sema cache.
    pub fn collect_keyed_instances(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.instances
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
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

    /// Retain only instances whose keys satisfy the predicate.
    ///
    /// Entries for which `f` returns `false` are removed.
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.instances.retain(f);
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
// MonomorphKey + Instance + Cache (free functions)
// ============================================================================

/// Key for looking up monomorphized function instances.
/// Uses a string representation for hashability since Type doesn't implement Hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphKey {
    /// Original generic function name
    pub func_name: NameId,
    /// Opaque type keys for concrete types
    pub type_keys: Vec<TypeId>,
}

impl MonomorphKey {
    /// Create a key from function name and concrete type arguments
    pub fn new(func_name: NameId, type_keys: Vec<TypeId>) -> Self {
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
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId>;
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
    pub substitutions: FxHashMap<NameId, TypeId>,
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
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized function instances.
/// Maps (func_name, concrete_types) -> monomorphized function info.
pub type MonomorphCache = MonomorphCacheBase<MonomorphKey, MonomorphInstance>;

// ============================================================================
// ClassMethodMonomorphKey + Instance + Cache
// ============================================================================

/// Key for looking up monomorphized class method instances.
/// Identifies a specific instantiation of a generic class method.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassMethodMonomorphKey {
    /// The class's NameId
    pub class_name: NameId,
    /// The method's NameId
    pub method_name: NameId,
    /// Opaque type keys for the class's concrete type arguments
    pub type_keys: Vec<TypeId>,
}

impl ClassMethodMonomorphKey {
    /// Create a new key for a class method monomorphization
    pub fn new(class_name: NameId, method_name: NameId, type_keys: Vec<TypeId>) -> Self {
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
    pub substitutions: FxHashMap<NameId, TypeId>,
    /// External method info (if this is an external method, call the runtime function)
    pub external_info: Option<ExternalMethodInfo>,
    /// Pre-computed self type (e.g., Foo<String> for a method on Foo<String>)
    pub self_type: TypeId,
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
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized class method instances.
pub type ClassMethodMonomorphCache =
    MonomorphCacheBase<ClassMethodMonomorphKey, ClassMethodMonomorphInstance>;

// ============================================================================
// StaticMethodMonomorphKey + Instance + Cache
// ============================================================================

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
    pub class_type_keys: Vec<TypeId>,
    /// Opaque type keys for the method's concrete type arguments (e.g., U in func convert<U>)
    pub method_type_keys: Vec<TypeId>,
}

impl StaticMethodMonomorphKey {
    /// Create a new key for a static method monomorphization
    pub fn new(
        class_name: NameId,
        method_name: NameId,
        class_type_keys: Vec<TypeId>,
        method_type_keys: Vec<TypeId>,
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
    pub substitutions: FxHashMap<NameId, TypeId>,
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
    fn substitutions(&self) -> &FxHashMap<NameId, TypeId> {
        &self.substitutions
    }
}

/// Cache of monomorphized static method instances.
pub type StaticMethodMonomorphCache =
    MonomorphCacheBase<StaticMethodMonomorphKey, StaticMethodMonomorphInstance>;

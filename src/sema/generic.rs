// src/sema/generic.rs
//
// Generic type parameter handling for Vole.
// This module provides structures for tracking type parameters in scope
// and supports monomorphization of generic functions.

use crate::frontend::Symbol;
use crate::identity::NameId;
use crate::sema::TypeKey;
use crate::sema::implement_registry::ExternalMethodInfo;
use crate::sema::types::{FunctionType, StructuralType, Type};
use std::collections::HashMap;
use std::hash::Hash;

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
#[derive(Debug, Clone)]
pub struct MonomorphCacheBase<K, V> {
    instances: HashMap<K, V>,
    next_id: u32,
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
        }
    }

    /// Look up an existing monomorphized instance
    pub fn get(&self, key: &K) -> Option<&V> {
        self.instances.get(key)
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
}

// ============================================================================
// Type Parameter Handling
// ============================================================================

/// Information about a type parameter in scope
#[derive(Debug, Clone)]
pub struct TypeParamInfo {
    /// The name of the type parameter as Symbol (for parsing/resolution stage)
    pub name: Symbol,
    /// The name of the type parameter as NameId (for type substitution)
    pub name_id: NameId,
    /// Optional constraint on the type parameter
    pub constraint: Option<TypeConstraint>,
}

/// Resolved constraint for type parameter checking
#[derive(Debug, Clone)]
pub enum TypeConstraint {
    /// Interface constraints: T: Stringable or T: Hashable + Eq
    Interface(Vec<Symbol>),
    /// Union constraint: T: i32 | i64
    Union(Vec<Type>),
    /// Structural constraint: T: { name: string, func get() -> i32 }
    Structural(StructuralType),
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
}

/// Information about a generic function definition
#[derive(Debug, Clone)]
pub struct GenericFuncDef {
    /// The function's type parameters (e.g., T, U)
    pub type_params: Vec<TypeParamInfo>,
    /// Parameter types with TypeParam placeholders (e.g., [TypeParam(T), i64])
    pub param_types: Vec<Type>,
    /// Return type with TypeParam placeholders
    pub return_type: Type,
}

/// Information about a generic record definition
#[derive(Debug, Clone)]
pub struct GenericRecordDef {
    /// The record's NameId for cross-interner lookups
    pub name_id: NameId,
    /// The record's type parameters (e.g., T, K, V)
    pub type_params: Vec<TypeParamInfo>,
    /// Field names
    pub field_names: Vec<Symbol>,
    /// Field types with TypeParam placeholders (e.g., [TypeParam(T), i64])
    pub field_types: Vec<Type>,
}

/// Information about a generic class definition
#[derive(Debug, Clone)]
pub struct GenericClassDef {
    /// The class's NameId for cross-interner lookups
    pub name_id: NameId,
    /// The class's type parameters (e.g., T, K, V)
    pub type_params: Vec<TypeParamInfo>,
    /// Field names
    pub field_names: Vec<Symbol>,
    /// Field types with TypeParam placeholders (e.g., [TypeParam(T), i64])
    pub field_types: Vec<Type>,
}

/// Key for looking up monomorphized function instances.
/// Uses a string representation for hashability since Type doesn't implement Hash.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphKey {
    /// Original generic function name
    pub func_name: NameId,
    /// Opaque type keys for concrete types
    pub type_keys: Vec<TypeKey>,
}

impl MonomorphKey {
    /// Create a key from function name and concrete type arguments
    pub fn new(func_name: NameId, type_keys: Vec<TypeKey>) -> Self {
        Self {
            func_name,
            type_keys,
        }
    }
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
    /// Map from type param NameId to concrete type
    pub substitutions: HashMap<NameId, Type>,
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
    pub type_keys: Vec<TypeKey>,
}

impl ClassMethodMonomorphKey {
    /// Create a new key for a class method monomorphization
    pub fn new(class_name: NameId, method_name: NameId, type_keys: Vec<TypeKey>) -> Self {
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
    /// Map from type param NameId to concrete type
    pub substitutions: HashMap<NameId, Type>,
    /// External method info (if this is an external method, call the runtime function)
    pub external_info: Option<ExternalMethodInfo>,
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
    pub class_type_keys: Vec<TypeKey>,
    /// Opaque type keys for the method's concrete type arguments (e.g., U in func convert<U>)
    pub method_type_keys: Vec<TypeKey>,
}

impl StaticMethodMonomorphKey {
    /// Create a new key for a static method monomorphization
    pub fn new(
        class_name: NameId,
        method_name: NameId,
        class_type_keys: Vec<TypeKey>,
        method_type_keys: Vec<TypeKey>,
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
    /// Map from type param NameId to concrete type
    pub substitutions: HashMap<NameId, Type>,
}

/// Cache of monomorphized static method instances.
pub type StaticMethodMonomorphCache =
    MonomorphCacheBase<StaticMethodMonomorphKey, StaticMethodMonomorphInstance>;

/// Substitute concrete types for type parameters in a type.
///
/// This is a convenience wrapper around `Type::substitute`. Prefer calling
/// `ty.substitute(substitutions)` directly in new code.
pub fn substitute_type(ty: &Type, substitutions: &HashMap<NameId, Type>) -> Type {
    ty.substitute(substitutions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::types::PrimitiveType;

    #[test]
    fn test_type_param_scope() {
        let mut names = crate::identity::NameTable::new();
        let mut scope = TypeParamScope::new();

        // Symbol(0) for testing - in real code these come from interner
        let t = Symbol(0);
        let t_name_id = names.intern_raw(names.main_module(), &["T"]);
        scope.add(TypeParamInfo {
            name: t,
            name_id: t_name_id,
            constraint: None,
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
        let mut cache = MonomorphCache::new();
        let mut names = crate::identity::NameTable::new();
        let mut interner = crate::frontend::Interner::new();
        let func_sym = interner.intern("foo");
        let func_name = names.intern(names.main_module(), &[func_sym], &interner);
        let mut table = crate::sema::TypeTable::new();

        let key1 = MonomorphKey::new(
            func_name,
            vec![table.key_for_type(&Type::Primitive(PrimitiveType::I64))],
        );
        let key2 = MonomorphKey::new(
            func_name,
            vec![table.key_for_type(&Type::Primitive(PrimitiveType::String))],
        );
        let key1_dup = MonomorphKey::new(
            func_name,
            vec![table.key_for_type(&Type::Primitive(PrimitiveType::I64))],
        );

        assert!(!cache.contains(&key1));

        cache.insert(
            key1.clone(),
            MonomorphInstance {
                original_name: func_name,
                mangled_name: names.intern_raw(names.main_module(), &["foo__mono_0"]),
                instance_id: 0,
                func_type: FunctionType {
                    params: vec![Type::Primitive(PrimitiveType::I64)],
                    return_type: Box::new(Type::Primitive(PrimitiveType::I64)),
                    is_closure: false,
                },
                substitutions: HashMap::new(),
            },
        );

        assert!(cache.contains(&key1));
        assert!(cache.contains(&key1_dup)); // Same types = same key
        assert!(!cache.contains(&key2)); // Different types = different key
    }

    #[test]
    fn test_substitute_type() {
        let mut names = crate::identity::NameTable::new();
        let t_name_id = names.intern_raw(names.main_module(), &["T"]);
        let mut subs = HashMap::new();
        subs.insert(t_name_id, Type::Primitive(PrimitiveType::I64));

        // Simple substitution
        let result = substitute_type(&Type::TypeParam(t_name_id), &subs);
        assert_eq!(result, Type::Primitive(PrimitiveType::I64));

        // Array of type param
        let arr = Type::Array(Box::new(Type::TypeParam(t_name_id)));
        let result = substitute_type(&arr, &subs);
        assert_eq!(
            result,
            Type::Array(Box::new(Type::Primitive(PrimitiveType::I64)))
        );

        // Non-param types unchanged
        let result = substitute_type(&Type::Primitive(PrimitiveType::Bool), &subs);
        assert_eq!(result, Type::Primitive(PrimitiveType::Bool));
    }
}

//! Definition structs for language entities.
//!
//! These structs hold the full information about types, methods, fields, and functions.
//! The corresponding ID types (TypeDefId, etc.) are indices into vectors of these.

use crate::FunctionType;
use crate::generic::TypeParamInfo;
use crate::implement_registry::ExternalMethodInfo;
use crate::type_arena::TypeId;
use vole_frontend::{Expr, NodeId};
use vole_identity::{FieldId, FunctionId, GlobalId, MethodId, ModuleId, NameId, TypeDefId};

/// What kind of type definition this is
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeDefKind {
    Interface,
    Class,
    Record,
    ErrorType,
    Primitive,
    /// Type alias (e.g., `type Numeric = i32 | i64`)
    Alias,
}

/// Generic type information for records and classes.
/// Stores the type parameters and field types needed for type inference
/// when instantiating generic types.
#[derive(Debug, Clone)]
pub struct GenericTypeInfo {
    /// The type parameters (e.g., T, K, V) with names and constraints
    pub type_params: Vec<TypeParamInfo>,
    /// Field names as stable NameIds (cross-module safe)
    pub field_names: Vec<NameId>,
    /// Field types with TypeParam placeholders (e.g., [TypeParam(T), i64])
    pub field_types: Vec<TypeId>,
    /// Whether each field has a default value (parallel to field_names)
    pub field_has_default: Vec<bool>,
}

/// A method binding within an implementation block.
/// Maps an interface method to a concrete implementation.
#[derive(Debug, Clone)]
pub struct MethodBinding {
    /// The method name
    pub method_name: NameId,
    /// The method signature
    pub func_type: FunctionType,
    /// Whether this is a builtin method (array.length(), etc.)
    pub is_builtin: bool,
    /// External (native) method info
    pub external_info: Option<ExternalMethodInfo>,
}

/// An implementation of an interface for a type.
/// Tracks which interface is implemented and how each method is bound.
#[derive(Debug, Clone)]
pub struct Implementation {
    /// The interface being implemented
    pub interface: TypeDefId,
    /// Type arguments for generic interfaces (e.g., [i64, i64] for MapLike<i64, i64>)
    pub type_args: Vec<TypeId>,
    /// Method bindings for this implementation
    pub method_bindings: Vec<MethodBinding>,
}

/// A type definition (interface, class, record, etc.)
#[derive(Debug, Clone)]
pub struct TypeDef {
    pub id: TypeDefId,
    pub name_id: NameId,
    pub kind: TypeDefKind,
    pub module: ModuleId,
    pub methods: Vec<MethodId>,
    pub fields: Vec<FieldId>,
    pub extends: Vec<TypeDefId>,
    /// Type parameters for generic types as NameIds (e.g., T in Iterator<T>)
    /// Used for both display and type substitution
    pub type_params: Vec<NameId>,
    /// Static methods (called on the type, not on instances)
    pub static_methods: Vec<MethodId>,
    /// For TypeDefKind::Alias - the type this alias resolves to
    pub aliased_type: Option<TypeId>,
    /// For generic records/classes - type parameter and field type info
    pub generic_info: Option<GenericTypeInfo>,
    /// For TypeDefKind::ErrorType - the error type info with fields
    pub error_info: Option<crate::ErrorTypeInfo>,
    /// Interface implementations for this type
    pub implements: Vec<Implementation>,
}

/// A method definition (always belongs to a type)
#[derive(Debug, Clone)]
pub struct MethodDef {
    pub id: MethodId,
    pub name_id: NameId,      // "next"
    pub full_name_id: NameId, // "Iterator::next"
    pub defining_type: TypeDefId,
    /// Interned TypeId for the signature. Use TypeArena::unwrap_function() to get params/return.
    pub signature_id: TypeId,
    pub has_default: bool,
    /// Whether this is a static method (called on type, not instance)
    pub is_static: bool,
    /// External binding for this method (if any)
    pub external_binding: Option<ExternalMethodInfo>,
    /// Method-level type parameters (e.g., `func convert<U>` has U as a method type param)
    /// Distinct from class type params which are stored on TypeDef
    pub method_type_params: Vec<TypeParamInfo>,
}

/// A field definition (always belongs to a type)
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub id: FieldId,
    pub name_id: NameId,      // "x"
    pub full_name_id: NameId, // "Point::x"
    pub defining_type: TypeDefId,
    pub ty: TypeId,
    pub slot: usize,
}

/// Generic function information.
/// Stores the type parameters and parameter/return types needed for monomorphization.
#[derive(Debug, Clone)]
pub struct GenericFuncInfo {
    /// The type parameters (e.g., T, U) with names and constraints
    pub type_params: Vec<TypeParamInfo>,
    /// Parameter types with TypeParam placeholders
    pub param_types: Vec<TypeId>,
    /// Return type with TypeParam placeholder
    pub return_type: TypeId,
}

/// A free function definition (belongs to a module)
#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub id: FunctionId,
    pub name_id: NameId,      // "sin"
    pub full_name_id: NameId, // "math::sin"
    pub module: ModuleId,
    pub signature: FunctionType,
    /// For generic functions - type parameter and signature info
    pub generic_info: Option<GenericFuncInfo>,
    /// Number of required parameters (without defaults).
    /// Parameters 0..required_params are required, rest have defaults.
    pub required_params: usize,
    /// Default expressions for parameters (cloned from AST).
    /// Index corresponds to parameter index.
    /// Required params have None, defaulted params have Some.
    pub param_defaults: Vec<Option<Box<Expr>>>,
}

/// A global variable definition (module-level let/var)
#[derive(Debug, Clone)]
pub struct GlobalDef {
    pub id: GlobalId,
    pub name_id: NameId,
    pub type_id: TypeId, // Analyzed type, NOT TypeExpr
    pub module_id: ModuleId,
    pub is_mutable: bool,     // let (false) vs var (true)
    pub init_node_id: NodeId, // NodeId of the initializer expression
}

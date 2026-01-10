//! Definition structs for language entities.
//!
//! These structs hold the full information about types, methods, fields, and functions.
//! The corresponding ID types (TypeDefId, etc.) are indices into vectors of these.

use crate::identity::{FieldId, FunctionId, MethodId, ModuleId, NameId, TypeDefId};
use crate::sema::implement_registry::ExternalMethodInfo;
use crate::sema::{FunctionType, Type};

/// What kind of type definition this is
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeDefKind {
    Interface,
    Class,
    Record,
    ErrorType,
    Primitive,
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
    pub type_params: Vec<NameId>,
    /// Type parameters as Symbols - needed for substitution in method signatures
    /// These are the Symbols used when the type was declared.
    pub type_params_symbols: Vec<crate::frontend::Symbol>,
}

/// A method definition (always belongs to a type)
#[derive(Debug, Clone)]
pub struct MethodDef {
    pub id: MethodId,
    pub name_id: NameId,      // "next"
    pub full_name_id: NameId, // "Iterator::next"
    pub defining_type: TypeDefId,
    pub signature: FunctionType,
    pub has_default: bool,
    /// External binding for this method (if any)
    pub external_binding: Option<ExternalMethodInfo>,
}

/// A field definition (always belongs to a type)
#[derive(Debug, Clone)]
pub struct FieldDef {
    pub id: FieldId,
    pub name_id: NameId,      // "x"
    pub full_name_id: NameId, // "Point::x"
    pub defining_type: TypeDefId,
    pub ty: Type,
    pub slot: usize,
}

/// A free function definition (belongs to a module)
#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub id: FunctionId,
    pub name_id: NameId,      // "sin"
    pub full_name_id: NameId, // "math::sin"
    pub module: ModuleId,
    pub signature: FunctionType,
}

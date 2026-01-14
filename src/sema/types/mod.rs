// src/sema/types/mod.rs
//
// Core type system module for Vole.
//
// This module is organized into submodules by type category:
// - `primitive` - PrimitiveType enum (i8-i128, u8-u64, f32, f64, bool, string)
// - `nominal` - NominalType enum (Class, Record, Interface, Error) with TypeDefIds
// - `special` - Supporting types for special Type variants (Placeholder, Invalid, etc.)

pub mod nominal;
pub mod primitive;
pub mod special;
pub use nominal::{
    ClassType, ErrorTypeInfo, ExtendsVec, InterfaceMethodType, InterfaceType, NominalType,
    RecordType,
};
pub use primitive::PrimitiveType;
pub use special::{AnalysisError, ConstantValue, FallibleType, ModuleType, PlaceholderKind};

use std::sync::Arc;

use crate::frontend::PrimitiveType as AstPrimitiveType;
use crate::frontend::Span;
use crate::identity::{NameId, TypeDefId, TypeParamId};

// AnalysisError, PlaceholderKind, FallibleType, ModuleType, ConstantValue
// are now defined in special.rs and re-exported above

/// Resolved types in the type system
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Primitive types (integers, floats, bool, string)
    Primitive(PrimitiveType),
    /// Void (no return value)
    Void,
    /// Nil type - the "absence of value" type for optionals
    /// Distinct from Void (which is only for function returns)
    Nil,
    /// Done type - sentinel for iterator termination
    /// Used in iterator next() returning T | Done
    Done,
    /// Union type - value can be any of the variant types
    /// Represented at runtime as tagged union (discriminant + payload)
    /// TODO: Consider nullable pointer optimization for pointer types (String, Array)
    Union(Arc<[Type]>),
    /// Range type (e.g., 0..10)
    Range,
    /// Array type (e.g., [i32], [string])
    Array(Box<Type>),
    /// Function type
    Function(FunctionType),
    /// Placeholder type - waiting for substitution or inference.
    /// Use PlaceholderKind to understand what type is being deferred.
    Placeholder(PlaceholderKind),
    /// Invalid type - analysis failed, carries error chain for debugging
    Invalid(AnalysisError),
    /// The metatype - the type of types themselves
    /// e.g., `i32` has type `Type`, `let MyInt = i32` assigns a type value
    Type,
    /// Nominal types (Class, Record, Interface, Error) - types with a TypeDefId
    Nominal(NominalType),
    /// Fallible return type: fallible(T, E)
    Fallible(FallibleType),
    /// Module type (from import expression)
    Module(ModuleType),
    /// Runtime iterator type - represents builtin iterators (array.iter(), range.iter(), etc.)
    /// These are raw pointers to UnifiedIterator and should call external functions directly
    /// without interface boxing. The inner type is the element type.
    RuntimeIterator(Box<Type>),
    /// Type parameter placeholder (e.g., T during inference)
    /// Only valid within generic context during type checking.
    /// Note: This is for inference placeholders. For resolved type parameter
    /// references, use TypeParamRef(TypeParamId) instead.
    TypeParam(NameId),
    /// Type parameter reference - a reference to a specific type parameter.
    /// Unlike TypeParam which is for inference, TypeParamRef identifies a
    /// concrete type parameter definition with a unique TypeParamId.
    TypeParamRef(TypeParamId),
    /// Tuple type - heterogeneous fixed-size collection
    /// e.g., [i32, string, bool] - different types per position
    Tuple(Arc<[Type]>),
    /// Fixed-size array - homogeneous fixed-size array
    /// e.g., [i32; 10] - single element type, compile-time known size
    FixedArray { element: Box<Type>, size: usize },
    /// Structural type - duck typing constraint
    /// e.g., { name: string, func greet() -> string }
    Structural(StructuralType),
}

/// Structural type - defines shape constraints for duck typing
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructuralType {
    pub fields: Vec<StructuralFieldType>,
    pub methods: Vec<StructuralMethodType>,
}

/// A field in a structural type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructuralFieldType {
    pub name: NameId,
    pub ty: Type,
}

/// A method in a structural type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructuralMethodType {
    pub name: NameId,
    pub params: Vec<Type>,
    pub return_type: Type,
}

#[derive(Debug, Clone, Eq)]
pub struct FunctionType {
    pub params: Arc<[Type]>,
    pub return_type: Box<Type>,
    /// If true, this function is a closure (has captures) and needs
    /// to be called with the closure pointer as the first argument.
    /// The closure pointer is passed implicitly and is not included in `params`.
    pub is_closure: bool,
}

/// Field information for a class/record
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub slot: usize, // Compile-time slot index
}

// ClassType, RecordType, InterfaceType, InterfaceMethodType, ErrorTypeInfo
// are now defined in nominal.rs and re-exported above
//
// FallibleType, ConstantValue, ModuleType, AnalysisError, PlaceholderKind
// are now defined in special.rs and re-exported above

impl PartialEq for FunctionType {
    fn eq(&self, other: &Self) -> bool {
        // is_closure is not part of type equality - a closure () -> i64 is
        // compatible with a function type () -> i64 for type checking purposes
        self.params == other.params && self.return_type == other.return_type
    }
}

// Manual Hash to match PartialEq semantics - ignore is_closure
impl std::hash::Hash for FunctionType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.params.hash(state);
        self.return_type.hash(state);
        // is_closure deliberately not hashed to match PartialEq
    }
}

impl FunctionType {
    /// Check if this function type is compatible with a functional interface signature.
    ///
    /// This is used when checking if a function/closure can be assigned to a functional
    /// interface type. Parameters must be compatible (with widening) and return types
    /// must be compatible.
    pub fn is_compatible_with_interface(&self, interface_fn: &FunctionType) -> bool {
        if self.params.len() != interface_fn.params.len() {
            return false;
        }

        // Import here to avoid circular dependency issues at module level
        use crate::sema::compatibility::TypeCompatibility;

        let params_match = self
            .params
            .iter()
            .zip(interface_fn.params.iter())
            .all(|(fp, ip)| fp.is_compatible(ip));

        let return_matches = self.return_type.is_compatible(&interface_fn.return_type);

        params_match && return_matches
    }
}

impl Type {
    /// Convert from AST PrimitiveType to Type
    pub fn from_primitive(p: AstPrimitiveType) -> Self {
        Type::Primitive(PrimitiveType::from_ast(p))
    }

    /// Get the primitive type if this is a primitive, None otherwise
    pub fn as_primitive(&self) -> Option<PrimitiveType> {
        match self {
            Type::Primitive(p) => Some(*p),
            _ => None,
        }
    }

    /// Get TypeDefId for nominal types (Class, Record, Interface, ErrorType).
    /// Returns None for primitives, functions, unions, etc.
    pub fn type_def_id(&self) -> Option<TypeDefId> {
        match self {
            Type::Nominal(n) => Some(n.type_def_id()),
            _ => None,
        }
    }

    /// Get type arguments for generic types.
    /// Returns empty slice for non-generic or primitive types.
    pub fn type_args(&self) -> &[Type] {
        match self {
            Type::Nominal(n) => n.type_args(),
            _ => &[],
        }
    }

    /// Check if this type is numeric (can do arithmetic)
    pub fn is_numeric(&self) -> bool {
        match self {
            Type::Primitive(p) => p.is_numeric(),
            _ => false,
        }
    }

    /// Check if this type is an integer
    pub fn is_integer(&self) -> bool {
        match self {
            Type::Primitive(p) => p.is_integer(),
            _ => false,
        }
    }

    /// Check if this is a signed integer type
    pub fn is_signed(&self) -> bool {
        match self {
            Type::Primitive(p) => p.is_signed(),
            _ => false,
        }
    }

    /// Check if this is an unsigned integer type
    pub fn is_unsigned(&self) -> bool {
        match self {
            Type::Primitive(p) => p.is_unsigned(),
            _ => false,
        }
    }

    /// Check if this is a floating point type
    pub fn is_float(&self) -> bool {
        match self {
            Type::Primitive(p) => p.is_float(),
            _ => false,
        }
    }

    /// Get the bit width of a numeric type
    pub fn bit_width(&self) -> Option<u8> {
        match self {
            Type::Primitive(p) => p.bit_width(),
            _ => None,
        }
    }

    /// Check if this type can be implicitly widened to target type
    pub fn can_widen_to(&self, target: &Type) -> bool {
        if self == target {
            return true;
        }
        match (self, target) {
            (Type::Primitive(from), Type::Primitive(to)) => from.can_widen_to(*to),
            _ => false,
        }
    }

    /// Get the type name for error messages
    pub fn name(&self) -> &'static str {
        match self {
            Type::Primitive(p) => p.name(),
            Type::Void => "void",
            Type::Nil => "nil",
            Type::Done => "Done",
            Type::Union(_) => "union", // Display impl handles full representation
            Type::Range => "range",
            Type::Array(_) => "array",
            Type::Function(_) => "function",
            Type::Placeholder(_) => "placeholder",
            Type::Invalid(_) => "<invalid>",
            Type::Type => "type",
            Type::Nominal(n) => n.name(),
            Type::Fallible(_) => "fallible",
            Type::Module(_) => "module",
            Type::TypeParam(_) | Type::TypeParamRef(_) => "type parameter",
            Type::RuntimeIterator(_) => "iterator",
            Type::Tuple(_) => "tuple",
            Type::FixedArray { .. } => "fixed array",
            Type::Structural(_) => "structural",
        }
    }

    /// Check if this is a union type containing Nil
    pub fn is_optional(&self) -> bool {
        matches!(self, Type::Union(types) if types.contains(&Type::Nil))
    }

    /// For an optional/union type, get the non-nil variants
    pub fn unwrap_optional(&self) -> Option<Type> {
        match self {
            Type::Union(types) => {
                let non_nil: Vec<_> = types.iter().filter(|t| **t != Type::Nil).cloned().collect();
                match non_nil.len() {
                    0 => None,
                    1 => Some(non_nil.into_iter().next().expect("len checked to be 1")),
                    _ => Some(Type::Union(non_nil.into())),
                }
            }
            _ => None,
        }
    }

    /// Create an optional type (T | nil)
    pub fn optional(inner: Type) -> Type {
        Type::Union(vec![inner, Type::Nil].into())
    }

    /// Create an invalid type with just a kind (for migration - prefer invalid_msg)
    pub fn invalid(kind: &'static str) -> Type {
        Type::Invalid(AnalysisError::simple(kind))
    }

    /// Create an invalid type with kind and descriptive message
    pub fn invalid_msg(kind: &'static str, message: impl Into<String>) -> Type {
        Type::Invalid(AnalysisError::new(kind, message))
    }

    /// Create an invalid type with kind, message, and location
    pub fn invalid_at(kind: &'static str, message: impl Into<String>, span: Span) -> Type {
        Type::Invalid(AnalysisError::at(kind, message, span))
    }

    /// Propagate an invalid type, chaining to the source error with context
    pub fn propagate_invalid(
        source: &Type,
        context: impl Into<String>,
        span: Option<Span>,
    ) -> Type {
        if let Type::Invalid(err) = source {
            Type::Invalid(AnalysisError::propagate(err, context, span))
        } else {
            // Shouldn't call this on non-invalid types
            Type::Invalid(AnalysisError::new(
                "internal",
                "propagate_invalid called on valid type",
            ))
        }
    }

    /// Check if this type is invalid (analysis failed)
    pub fn is_invalid(&self) -> bool {
        matches!(self, Type::Invalid(_))
    }

    /// Create an inference placeholder (for type inference during analysis)
    pub fn unknown() -> Type {
        Type::Placeholder(PlaceholderKind::Inference)
    }

    /// Create a type parameter placeholder (for generic type parameters like T)
    pub fn type_param_placeholder(name: impl Into<String>) -> Type {
        Type::Placeholder(PlaceholderKind::TypeParam(name.into()))
    }

    /// Create a Self type placeholder (for interface method signatures)
    pub fn self_placeholder() -> Type {
        Type::Placeholder(PlaceholderKind::SelfType)
    }

    /// Check if this is a placeholder type
    pub fn is_placeholder(&self) -> bool {
        matches!(self, Type::Placeholder(_))
    }

    /// Get the analysis error if this is an invalid type
    pub fn analysis_error(&self) -> Option<&AnalysisError> {
        match self {
            Type::Invalid(err) => Some(err),
            _ => None,
        }
    }

    /// Assert this type is valid (not Invalid). Panics with context if Invalid.
    /// Use in codegen where Invalid types indicate a compiler bug.
    #[track_caller]
    pub fn expect_valid(&self, context: &str) -> &Self {
        if let Type::Invalid(err) = self {
            panic!(
                "INTERNAL ERROR: Type::Invalid encountered in codegen\n\
                 Context: {}\n\
                 Error chain:\n  {}\n\
                 Location: {}",
                context,
                err.full_chain(),
                std::panic::Location::caller()
            );
        }
        self
    }

    /// Unwrap optional, panicking with context if it fails.
    /// Use in codegen where unwrap failure indicates a compiler bug.
    #[track_caller]
    pub fn unwrap_optional_or_panic(&self, context: &str) -> Type {
        self.unwrap_optional().unwrap_or_else(|| {
            panic!(
                "INTERNAL ERROR: unwrap_optional failed\n\
                 Context: {}\n\
                 Type: {:?}\n\
                 Location: {}",
                context,
                self,
                std::panic::Location::caller()
            )
        })
    }

    /// Normalize a union: flatten nested unions, sort, dedupe, unwrap single-element
    pub fn normalize_union(mut types: Vec<Type>) -> Type {
        // Flatten nested unions
        let mut flattened = Vec::new();
        for ty in types.drain(..) {
            match ty {
                Type::Union(inner) => flattened.extend(inner.iter().cloned()),
                other => flattened.push(other),
            }
        }

        // Sort for canonical representation (use debug string for now)
        flattened.sort_by_key(|t| format!("{:?}", t));

        // Dedupe
        flattened.dedup();

        // Unwrap single-element union
        if flattened.len() == 1 {
            flattened.into_iter().next().expect("len checked to be 1")
        } else {
            Type::Union(flattened.into())
        }
    }

    /// Promote two numeric types to their common supertype
    pub fn promote(left: &Type, right: &Type) -> Type {
        match (left, right) {
            (Type::Primitive(l), Type::Primitive(r)) => {
                if let Some(promoted) = PrimitiveType::promote(*l, *r) {
                    Type::Primitive(promoted)
                } else {
                    left.clone()
                }
            }
            _ => left.clone(),
        }
    }

    /// Substitute type parameters with concrete types.
    ///
    /// This is the core operation for generic type instantiation. Given a map
    /// from type parameter NameIds to concrete types, returns a new type with
    /// all type parameters replaced.
    ///
    /// # Example
    /// ```ignore
    /// // For a function `fn identity<T>(x: T) -> T` called with i64:
    /// let substitutions = HashMap::from([(t_name_id, Type::Primitive(PrimitiveType::I64))]);
    /// let param_type = Type::TypeParam(t_name_id);
    /// assert_eq!(param_type.substitute(&substitutions), Type::Primitive(PrimitiveType::I64));
    /// ```
    pub fn substitute(&self, substitutions: &std::collections::HashMap<NameId, Type>) -> Type {
        // Early exit if no substitutions - just clone (cheap for Arc-based types)
        if substitutions.is_empty() {
            return self.clone();
        }

        match self {
            // Direct substitution for type parameters
            Type::TypeParam(name_id) => substitutions
                .get(name_id)
                .cloned()
                .unwrap_or_else(|| self.clone()),

            // TypeParamRef doesn't substitute based on NameId - it's an opaque reference
            Type::TypeParamRef(_) => self.clone(),

            // Recursive substitution for compound types - reuse Arc if unchanged
            Type::Array(elem) => {
                let new_elem = elem.substitute(substitutions);
                if &new_elem == elem.as_ref() {
                    self.clone()
                } else {
                    Type::Array(Box::new(new_elem))
                }
            }

            Type::Union(types) => {
                let new_types = substitute_slice(types, substitutions);
                if let Some(reused) = new_types {
                    Type::Union(reused)
                } else {
                    self.clone()
                }
            }

            Type::Function(ft) => {
                let new_params = substitute_slice(&ft.params, substitutions);
                let new_return = ft.return_type.substitute(substitutions);
                let return_changed = &new_return != ft.return_type.as_ref();

                if new_params.is_none() && !return_changed {
                    self.clone()
                } else {
                    Type::Function(FunctionType {
                        params: new_params.unwrap_or_else(|| ft.params.clone()),
                        return_type: Box::new(new_return),
                        is_closure: ft.is_closure,
                    })
                }
            }

            Type::Tuple(elements) => {
                let new_elements = substitute_slice(elements, substitutions);
                if let Some(reused) = new_elements {
                    Type::Tuple(reused)
                } else {
                    self.clone()
                }
            }

            Type::Nominal(NominalType::Interface(interface_type)) => {
                let new_type_args = substitute_slice(&interface_type.type_args, substitutions);
                let new_methods =
                    substitute_interface_methods(&interface_type.methods, substitutions);

                if new_type_args.is_none() && new_methods.is_none() {
                    self.clone()
                } else {
                    Type::Nominal(NominalType::Interface(InterfaceType {
                        type_def_id: interface_type.type_def_id,
                        type_args: new_type_args
                            .unwrap_or_else(|| interface_type.type_args.clone()),
                        methods: new_methods.unwrap_or_else(|| interface_type.methods.clone()),
                        extends: interface_type.extends.clone(),
                    }))
                }
            }

            Type::Nominal(NominalType::Record(record_type)) => {
                let new_type_args = substitute_slice(&record_type.type_args, substitutions);
                if let Some(args) = new_type_args {
                    Type::Nominal(NominalType::Record(RecordType {
                        type_def_id: record_type.type_def_id,
                        type_args: args,
                    }))
                } else {
                    self.clone()
                }
            }

            Type::Nominal(NominalType::Class(class_type)) => {
                let new_type_args = substitute_slice(&class_type.type_args, substitutions);
                if let Some(args) = new_type_args {
                    Type::Nominal(NominalType::Class(ClassType {
                        type_def_id: class_type.type_def_id,
                        type_args: args,
                    }))
                } else {
                    self.clone()
                }
            }

            Type::RuntimeIterator(elem) => {
                let new_elem = elem.substitute(substitutions);
                if &new_elem == elem.as_ref() {
                    self.clone()
                } else {
                    Type::RuntimeIterator(Box::new(new_elem))
                }
            }

            Type::FixedArray { element, size } => {
                let new_elem = element.substitute(substitutions);
                if &new_elem == element.as_ref() {
                    self.clone()
                } else {
                    Type::FixedArray {
                        element: Box::new(new_elem),
                        size: *size,
                    }
                }
            }

            Type::Fallible(ft) => {
                let new_success = ft.success_type.substitute(substitutions);
                let new_error = ft.error_type.substitute(substitutions);
                let success_changed = &new_success != ft.success_type.as_ref();
                let error_changed = &new_error != ft.error_type.as_ref();

                if !success_changed && !error_changed {
                    self.clone()
                } else {
                    Type::Fallible(FallibleType {
                        success_type: Box::new(new_success),
                        error_type: Box::new(new_error),
                    })
                }
            }

            Type::Structural(st) => {
                let mut fields_changed = false;
                let new_fields: Vec<_> = st
                    .fields
                    .iter()
                    .map(|f| {
                        let new_ty = f.ty.substitute(substitutions);
                        if new_ty != f.ty {
                            fields_changed = true;
                        }
                        StructuralFieldType {
                            name: f.name,
                            ty: new_ty,
                        }
                    })
                    .collect();

                let mut methods_changed = false;
                let new_methods: Vec<_> = st
                    .methods
                    .iter()
                    .map(|m| {
                        let new_params: Vec<_> = m
                            .params
                            .iter()
                            .map(|p| p.substitute(substitutions))
                            .collect();
                        let new_return = m.return_type.substitute(substitutions);
                        if new_params.iter().zip(m.params.iter()).any(|(a, b)| a != b)
                            || new_return != m.return_type
                        {
                            methods_changed = true;
                        }
                        StructuralMethodType {
                            name: m.name,
                            params: new_params,
                            return_type: new_return,
                        }
                    })
                    .collect();

                if !fields_changed && !methods_changed {
                    self.clone()
                } else {
                    Type::Structural(StructuralType {
                        fields: new_fields,
                        methods: new_methods,
                    })
                }
            }

            // Types without nested type parameters - return unchanged
            Type::Primitive(_)
            | Type::Void
            | Type::Nil
            | Type::Done
            | Type::Range
            | Type::Type
            | Type::Placeholder(_)
            | Type::Invalid(_)
            | Type::Module(_)
            | Type::Nominal(NominalType::Error(_)) => self.clone(),
        }
    }
}

/// Helper: substitute types in a slice, returning Some(new_arc) only if any changed
fn substitute_slice(
    types: &Arc<[Type]>,
    substitutions: &std::collections::HashMap<NameId, Type>,
) -> Option<Arc<[Type]>> {
    let mut changed = false;
    let new_types: Vec<_> = types
        .iter()
        .map(|t| {
            let new_t = t.substitute(substitutions);
            if &new_t != t {
                changed = true;
            }
            new_t
        })
        .collect();

    if changed {
        Some(new_types.into())
    } else {
        None
    }
}

/// Helper: substitute types in interface methods, returning Some only if any changed
fn substitute_interface_methods(
    methods: &Arc<[InterfaceMethodType]>,
    substitutions: &std::collections::HashMap<NameId, Type>,
) -> Option<Arc<[InterfaceMethodType]>> {
    let mut changed = false;
    let new_methods: Vec<_> = methods
        .iter()
        .map(|method| {
            let new_params = substitute_slice(&method.params, substitutions);
            let new_return = method.return_type.substitute(substitutions);
            let return_changed = &new_return != method.return_type.as_ref();

            if new_params.is_some() || return_changed {
                changed = true;
                InterfaceMethodType {
                    name: method.name,
                    params: new_params.unwrap_or_else(|| method.params.clone()),
                    return_type: Box::new(new_return),
                    has_default: method.has_default,
                }
            } else {
                method.clone()
            }
        })
        .collect();

    if changed {
        Some(new_methods.into())
    } else {
        None
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Primitive(p) => write!(f, "{}", p),
            Type::Function(ft) => {
                write!(f, "(")?;
                for (i, param) in ft.params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ft.return_type)
            }
            Type::Union(types) => {
                let parts: Vec<String> = types.iter().map(|t| format!("{}", t)).collect();
                write!(f, "{}", parts.join(" | "))
            }
            Type::Array(elem) => write!(f, "[{}]", elem),
            Type::Nominal(n) => write!(f, "{}", n),
            Type::Fallible(ft) => {
                write!(f, "fallible({}, {})", ft.success_type, ft.error_type)
            }
            Type::Module(m) => write!(f, "module(id:{})", m.module_id.index()),
            Type::TypeParam(name_id) => write!(f, "{:?}", name_id), // NameId Debug shows the identity
            Type::TypeParamRef(id) => write!(f, "TypeParam#{}", id.index()),
            Type::Tuple(elements) => {
                write!(f, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "]")
            }
            Type::FixedArray { element, size } => {
                write!(f, "[{}; {}]", element, size)
            }
            _ => write!(f, "{}", self.name()),
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param)?;
        }
        write!(f, ") -> {}", self.return_type)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(p: PrimitiveType) -> Type {
        Type::Primitive(p)
    }

    #[test]
    fn type_is_numeric() {
        assert!(p(PrimitiveType::I8).is_numeric());
        assert!(p(PrimitiveType::I16).is_numeric());
        assert!(p(PrimitiveType::I32).is_numeric());
        assert!(p(PrimitiveType::I64).is_numeric());
        assert!(p(PrimitiveType::I128).is_numeric());
        assert!(p(PrimitiveType::U8).is_numeric());
        assert!(p(PrimitiveType::U16).is_numeric());
        assert!(p(PrimitiveType::U32).is_numeric());
        assert!(p(PrimitiveType::U64).is_numeric());
        assert!(p(PrimitiveType::F32).is_numeric());
        assert!(p(PrimitiveType::F64).is_numeric());
        assert!(!p(PrimitiveType::Bool).is_numeric());
        assert!(!p(PrimitiveType::String).is_numeric());
    }

    #[test]
    fn type_is_integer() {
        assert!(p(PrimitiveType::I32).is_integer());
        assert!(p(PrimitiveType::I64).is_integer());
        assert!(p(PrimitiveType::U32).is_integer());
        assert!(!p(PrimitiveType::F64).is_integer());
        assert!(!p(PrimitiveType::Bool).is_integer());
    }

    #[test]
    fn type_is_signed_unsigned() {
        assert!(p(PrimitiveType::I32).is_signed());
        assert!(p(PrimitiveType::I128).is_signed());
        assert!(!p(PrimitiveType::U32).is_signed());
        assert!(!p(PrimitiveType::F64).is_signed());

        assert!(p(PrimitiveType::U32).is_unsigned());
        assert!(p(PrimitiveType::U64).is_unsigned());
        assert!(!p(PrimitiveType::I32).is_unsigned());
    }

    #[test]
    fn type_widening() {
        // Signed widening
        assert!(p(PrimitiveType::I8).can_widen_to(&p(PrimitiveType::I16)));
        assert!(p(PrimitiveType::I8).can_widen_to(&p(PrimitiveType::I64)));
        assert!(!p(PrimitiveType::I64).can_widen_to(&p(PrimitiveType::I32)));

        // Unsigned widening
        assert!(p(PrimitiveType::U8).can_widen_to(&p(PrimitiveType::U16)));
        assert!(p(PrimitiveType::U16).can_widen_to(&p(PrimitiveType::U64)));

        // Unsigned to signed
        assert!(p(PrimitiveType::U8).can_widen_to(&p(PrimitiveType::I16)));
        assert!(p(PrimitiveType::U32).can_widen_to(&p(PrimitiveType::I64)));
        assert!(!p(PrimitiveType::U64).can_widen_to(&p(PrimitiveType::I64)));

        // Float widening
        assert!(p(PrimitiveType::F32).can_widen_to(&p(PrimitiveType::F64)));
        assert!(!p(PrimitiveType::F64).can_widen_to(&p(PrimitiveType::F32)));
    }

    #[test]
    fn type_from_primitive() {
        use crate::frontend::PrimitiveType as AstPrimitive;
        assert_eq!(
            Type::from_primitive(AstPrimitive::I32),
            p(PrimitiveType::I32)
        );
        assert_eq!(
            Type::from_primitive(AstPrimitive::U64),
            p(PrimitiveType::U64)
        );
        assert_eq!(
            Type::from_primitive(AstPrimitive::F32),
            p(PrimitiveType::F32)
        );
    }

    #[test]
    fn type_optional() {
        let opt = Type::optional(p(PrimitiveType::I32));
        assert!(opt.is_optional());
        assert_eq!(opt.unwrap_optional(), Some(p(PrimitiveType::I32)));
    }

    #[test]
    fn type_normalize_union() {
        // Nested unions flatten
        let normalized = Type::normalize_union(vec![
            p(PrimitiveType::I32),
            Type::Union(vec![p(PrimitiveType::String), Type::Nil].into()),
        ]);
        assert!(matches!(normalized, Type::Union(v) if v.len() == 3));

        // Single element unwraps
        let single = Type::normalize_union(vec![p(PrimitiveType::I32)]);
        assert_eq!(single, p(PrimitiveType::I32));
    }
}

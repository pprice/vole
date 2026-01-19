//! Legacy type system - being replaced by TypeId.
//!
//! This module contains the recursive LegacyType enum and related types.
//! During the migration to TypeId, this module isolates the legacy code
//! for easier tracking and eventual removal.

use std::sync::Arc;

use crate::frontend::PrimitiveType as AstPrimitiveType;
use crate::frontend::Span;
use crate::identity::{NameId, TypeDefId, TypeParamId};

use super::nominal::{InterfaceMethodType, InterfaceType, NominalType};
use super::special::{AnalysisError, FallibleType, ModuleType, PlaceholderKind};
use super::{FunctionType, PrimitiveType};

/// Legacy type enum - being replaced by Type(TypeId) newtype
///
/// During migration, LegacyType is the recursive structure and
/// Type will become an alias then a newtype over TypeId.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LegacyType {
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
    Union(Arc<[LegacyType]>),
    /// Range type (e.g., 0..10)
    Range,
    /// Array type (e.g., [i32], [string])
    Array(Box<LegacyType>),
    /// Function type
    Function(FunctionType),
    /// Placeholder type - waiting for substitution or inference.
    /// Use PlaceholderKind to understand what type is being deferred.
    Placeholder(PlaceholderKind),
    /// Invalid type - analysis failed, carries error chain for debugging
    Invalid(AnalysisError),
    /// The metatype - the type of types themselves
    /// e.g., `i32` has type `Type`, `let MyInt = i32` assigns a type value
    MetaType,
    /// Nominal types (Class, Record, Interface, Error) - types with a TypeDefId
    Nominal(NominalType),
    /// Fallible return type: fallible(T, E)
    Fallible(FallibleType),
    /// Module type (from import expression)
    Module(ModuleType),
    /// Runtime iterator type - represents builtin iterators (array.iter(), range.iter(), etc.)
    /// These are raw pointers to UnifiedIterator and should call external functions directly
    /// without interface boxing. The inner type is the element type.
    RuntimeIterator(Box<LegacyType>),
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
    Tuple(Arc<[LegacyType]>),
    /// Fixed-size array - homogeneous fixed-size array
    /// e.g., [i32; 10] - single element type, compile-time known size
    FixedArray {
        element: Box<LegacyType>,
        size: usize,
    },
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
    pub ty: LegacyType,
}

/// A method in a structural type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructuralMethodType {
    pub name: NameId,
    pub params: Vec<LegacyType>,
    pub return_type: LegacyType,
}

/// Field information for a class/record (LegacyType version - deprecated)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: String,
    pub ty: LegacyType,
    pub slot: usize, // Compile-time slot index
}

impl LegacyType {
    /// Convert from AST PrimitiveType to Type
    pub fn from_primitive(p: AstPrimitiveType) -> Self {
        LegacyType::Primitive(PrimitiveType::from_ast(p))
    }

    /// Get TypeDefId for nominal types (Class, Record, Interface, ErrorType).
    /// Returns None for primitives, functions, unions, etc.
    pub fn type_def_id(&self) -> Option<TypeDefId> {
        match self {
            LegacyType::Nominal(n) => Some(n.type_def_id()),
            _ => None,
        }
    }

    /// Check if this type is numeric (can do arithmetic)
    pub fn is_numeric(&self) -> bool {
        match self {
            LegacyType::Primitive(p) => p.is_numeric(),
            _ => false,
        }
    }

    /// Check if this type is an integer
    pub fn is_integer(&self) -> bool {
        match self {
            LegacyType::Primitive(p) => p.is_integer(),
            _ => false,
        }
    }

    /// Check if this is a signed integer type
    pub fn is_signed(&self) -> bool {
        match self {
            LegacyType::Primitive(p) => p.is_signed(),
            _ => false,
        }
    }

    /// Check if this is an unsigned integer type
    pub fn is_unsigned(&self) -> bool {
        match self {
            LegacyType::Primitive(p) => p.is_unsigned(),
            _ => false,
        }
    }

    /// Check if this is a floating point type
    pub fn is_float(&self) -> bool {
        match self {
            LegacyType::Primitive(p) => p.is_float(),
            _ => false,
        }
    }

    /// Get the bit width of a numeric type
    pub fn bit_width(&self) -> Option<u8> {
        match self {
            LegacyType::Primitive(p) => p.bit_width(),
            _ => None,
        }
    }

    /// Check if this type can be implicitly widened to target type
    pub fn can_widen_to(&self, target: &LegacyType) -> bool {
        if self == target {
            return true;
        }
        match (self, target) {
            (LegacyType::Primitive(from), LegacyType::Primitive(to)) => from.can_widen_to(*to),
            _ => false,
        }
    }

    /// Get the type name for error messages
    pub fn name(&self) -> &'static str {
        match self {
            LegacyType::Primitive(p) => p.name(),
            LegacyType::Void => "void",
            LegacyType::Nil => "nil",
            LegacyType::Done => "Done",
            LegacyType::Union(_) => "union", // Display impl handles full representation
            LegacyType::Range => "range",
            LegacyType::Array(_) => "array",
            LegacyType::Function(_) => "function",
            LegacyType::Placeholder(_) => "placeholder",
            LegacyType::Invalid(_) => "<invalid>",
            LegacyType::MetaType => "type",
            LegacyType::Nominal(n) => n.name(),
            LegacyType::Fallible(_) => "fallible",
            LegacyType::Module(_) => "module",
            LegacyType::TypeParam(_) | LegacyType::TypeParamRef(_) => "type parameter",
            LegacyType::RuntimeIterator(_) => "iterator",
            LegacyType::Tuple(_) => "tuple",
            LegacyType::FixedArray { .. } => "fixed array",
            LegacyType::Structural(_) => "structural",
        }
    }

    /// Check if this is a union type containing Nil
    pub fn is_optional(&self) -> bool {
        matches!(self, LegacyType::Union(types) if types.contains(&LegacyType::Nil))
    }

    /// For an optional/union type, get the non-nil variants
    pub fn unwrap_optional(&self) -> Option<LegacyType> {
        match self {
            LegacyType::Union(types) => {
                let non_nil: Vec<_> = types
                    .iter()
                    .filter(|t| **t != LegacyType::Nil)
                    .cloned()
                    .collect();
                match non_nil.len() {
                    0 => None,
                    1 => Some(non_nil.into_iter().next().expect("len checked to be 1")),
                    _ => Some(LegacyType::Union(non_nil.into())),
                }
            }
            _ => None,
        }
    }

    /// Create an optional type (T | nil)
    pub fn optional(inner: LegacyType) -> LegacyType {
        LegacyType::Union(vec![inner, LegacyType::Nil].into())
    }

    /// Create an invalid type with just a kind (for migration - prefer invalid_msg)
    pub fn invalid(kind: &'static str) -> LegacyType {
        LegacyType::Invalid(AnalysisError::simple(kind))
    }

    /// Create an invalid type with kind and descriptive message
    pub fn invalid_msg(kind: &'static str, message: impl Into<String>) -> LegacyType {
        LegacyType::Invalid(AnalysisError::new(kind, message))
    }

    /// Create an invalid type with kind, message, and location
    pub fn invalid_at(kind: &'static str, message: impl Into<String>, span: Span) -> LegacyType {
        LegacyType::Invalid(AnalysisError::at(kind, message, span))
    }

    /// Check if this type is invalid (analysis failed)
    pub fn is_invalid(&self) -> bool {
        matches!(self, LegacyType::Invalid(_))
    }

    /// Create an inference placeholder (for type inference during analysis)
    pub fn unknown() -> LegacyType {
        LegacyType::Placeholder(PlaceholderKind::Inference)
    }

    /// Check if this is a placeholder type
    pub fn is_placeholder(&self) -> bool {
        matches!(self, LegacyType::Placeholder(_))
    }

    /// Assert this type is valid (not Invalid). Panics with context if Invalid.
    /// Use in codegen where Invalid types indicate a compiler bug.
    #[track_caller]
    pub fn expect_valid(&self, context: &str) -> &Self {
        if let LegacyType::Invalid(err) = self {
            panic!(
                "INTERNAL ERROR: LegacyType::Invalid encountered in codegen\n\
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

    /// Normalize a union: flatten nested unions, sort descending, dedupe, unwrap single-element
    pub fn normalize_union(mut types: Vec<LegacyType>) -> LegacyType {
        // Flatten nested unions
        let mut flattened = Vec::new();
        for ty in types.drain(..) {
            match ty {
                LegacyType::Union(inner) => flattened.extend(inner.iter().cloned()),
                other => flattened.push(other),
            }
        }

        // Sort descending - puts value types before sentinels (Nil, Done)
        // e.g., "Primitive(I64)" > "Nil" > "Done"
        flattened.sort_by_key(|t| std::cmp::Reverse(format!("{:?}", t)));

        // Dedupe
        flattened.dedup();

        // Unwrap single-element union
        if flattened.len() == 1 {
            flattened.into_iter().next().expect("len checked to be 1")
        } else {
            LegacyType::Union(flattened.into())
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
    /// let substitutions = HashMap::from([(t_name_id, LegacyType::Primitive(PrimitiveType::I64))]);
    /// let param_type = LegacyType::TypeParam(t_name_id);
    /// assert_eq!(param_type.substitute(&substitutions), LegacyType::Primitive(PrimitiveType::I64));
    /// ```
    pub fn substitute(
        &self,
        substitutions: &std::collections::HashMap<NameId, LegacyType>,
    ) -> LegacyType {
        // Early exit if no substitutions - just clone (cheap for Arc-based types)
        if substitutions.is_empty() {
            return self.clone();
        }

        match self {
            // Direct substitution for type parameters
            LegacyType::TypeParam(name_id) => substitutions
                .get(name_id)
                .cloned()
                .unwrap_or_else(|| self.clone()),

            // TypeParamRef doesn't substitute based on NameId - it's an opaque reference
            LegacyType::TypeParamRef(_) => self.clone(),

            // Recursive substitution for compound types - reuse Arc if unchanged
            LegacyType::Array(elem) => {
                let new_elem = elem.substitute(substitutions);
                if &new_elem == elem.as_ref() {
                    self.clone()
                } else {
                    LegacyType::Array(Box::new(new_elem))
                }
            }

            LegacyType::Union(types) => {
                let new_types = substitute_slice(types, substitutions);
                if let Some(reused) = new_types {
                    LegacyType::Union(reused)
                } else {
                    self.clone()
                }
            }

            LegacyType::Function(ft) => {
                let new_params = substitute_slice(&ft.params, substitutions);
                let new_return = ft.return_type.substitute(substitutions);
                let return_changed = &new_return != ft.return_type.as_ref();

                if new_params.is_none() && !return_changed {
                    self.clone()
                } else {
                    LegacyType::Function(FunctionType {
                        params: new_params.unwrap_or_else(|| ft.params.clone()),
                        return_type: Box::new(new_return),
                        is_closure: ft.is_closure,
                        params_id: None,
                        return_type_id: None,
                    })
                }
            }

            LegacyType::Tuple(elements) => {
                let new_elements = substitute_slice(elements, substitutions);
                if let Some(reused) = new_elements {
                    LegacyType::Tuple(reused)
                } else {
                    self.clone()
                }
            }

            // Nominal types: type_args_id requires arena for substitution.
            // Use arena.substitute() for proper TypeId-based substitution.
            // Here we only substitute methods for interfaces.
            LegacyType::Nominal(NominalType::Interface(interface_type)) => {
                let new_methods =
                    substitute_interface_methods(&interface_type.methods, substitutions);
                if let Some(methods) = new_methods {
                    LegacyType::Nominal(NominalType::Interface(InterfaceType {
                        type_def_id: interface_type.type_def_id,
                        type_args_id: interface_type.type_args_id.clone(),
                        methods,
                        extends: interface_type.extends.clone(),
                    }))
                } else {
                    self.clone()
                }
            }

            LegacyType::Nominal(NominalType::Record(_))
            | LegacyType::Nominal(NominalType::Class(_)) => {
                // Class/Record type_args_id requires arena for substitution.
                // Use arena.substitute() for proper TypeId-based substitution.
                self.clone()
            }

            LegacyType::RuntimeIterator(elem) => {
                let new_elem = elem.substitute(substitutions);
                if &new_elem == elem.as_ref() {
                    self.clone()
                } else {
                    LegacyType::RuntimeIterator(Box::new(new_elem))
                }
            }

            LegacyType::FixedArray { element, size } => {
                let new_elem = element.substitute(substitutions);
                if &new_elem == element.as_ref() {
                    self.clone()
                } else {
                    LegacyType::FixedArray {
                        element: Box::new(new_elem),
                        size: *size,
                    }
                }
            }

            LegacyType::Fallible(ft) => {
                let new_success = ft.success_type.substitute(substitutions);
                let new_error = ft.error_type.substitute(substitutions);
                let success_changed = &new_success != ft.success_type.as_ref();
                let error_changed = &new_error != ft.error_type.as_ref();

                if !success_changed && !error_changed {
                    self.clone()
                } else {
                    LegacyType::Fallible(FallibleType {
                        success_type: Box::new(new_success),
                        error_type: Box::new(new_error),
                    })
                }
            }

            LegacyType::Structural(st) => {
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
                    LegacyType::Structural(StructuralType {
                        fields: new_fields,
                        methods: new_methods,
                    })
                }
            }

            // Types without nested type parameters - return unchanged
            LegacyType::Primitive(_)
            | LegacyType::Void
            | LegacyType::Nil
            | LegacyType::Done
            | LegacyType::Range
            | LegacyType::MetaType
            | LegacyType::Placeholder(_)
            | LegacyType::Invalid(_)
            | LegacyType::Module(_)
            | LegacyType::Nominal(NominalType::Error(_)) => self.clone(),
        }
    }
}

/// Helper: substitute types in a slice, returning Some(new_arc) only if any changed
fn substitute_slice(
    types: &Arc<[LegacyType]>,
    substitutions: &std::collections::HashMap<NameId, LegacyType>,
) -> Option<Arc<[LegacyType]>> {
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
    substitutions: &std::collections::HashMap<NameId, LegacyType>,
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
                    params_id: None, // LegacyType substitution doesn't track TypeIds
                    return_type_id: None,
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

impl std::fmt::Display for LegacyType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LegacyType::Primitive(p) => write!(f, "{}", p),
            LegacyType::Function(ft) => {
                write!(f, "(")?;
                for (i, param) in ft.params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ") -> {}", ft.return_type)
            }
            LegacyType::Union(types) => {
                let parts: Vec<String> = types.iter().map(|t| format!("{}", t)).collect();
                write!(f, "{}", parts.join(" | "))
            }
            LegacyType::Array(elem) => write!(f, "[{}]", elem),
            LegacyType::Nominal(n) => write!(f, "{}", n),
            LegacyType::Fallible(ft) => {
                write!(f, "fallible({}, {})", ft.success_type, ft.error_type)
            }
            LegacyType::Module(m) => write!(f, "module(id:{})", m.module_id.index()),
            LegacyType::TypeParam(name_id) => write!(f, "{:?}", name_id), // NameId Debug shows the identity
            LegacyType::TypeParamRef(id) => write!(f, "TypeParam#{}", id.index()),
            LegacyType::Tuple(elements) => {
                write!(f, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, "]")
            }
            LegacyType::FixedArray { element, size } => {
                write!(f, "[{}; {}]", element, size)
            }
            _ => write!(f, "{}", self.name()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(p: PrimitiveType) -> LegacyType {
        LegacyType::Primitive(p)
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
            LegacyType::from_primitive(AstPrimitive::I32),
            p(PrimitiveType::I32)
        );
        assert_eq!(
            LegacyType::from_primitive(AstPrimitive::U64),
            p(PrimitiveType::U64)
        );
        assert_eq!(
            LegacyType::from_primitive(AstPrimitive::F32),
            p(PrimitiveType::F32)
        );
    }

    #[test]
    fn type_optional() {
        let opt = LegacyType::optional(p(PrimitiveType::I32));
        assert!(opt.is_optional());
        assert_eq!(opt.unwrap_optional(), Some(p(PrimitiveType::I32)));
    }

    #[test]
    fn type_normalize_union() {
        // Nested unions flatten
        let normalized = LegacyType::normalize_union(vec![
            p(PrimitiveType::I32),
            LegacyType::Union(vec![p(PrimitiveType::String), LegacyType::Nil].into()),
        ]);
        assert!(matches!(normalized, LegacyType::Union(_)));

        // Single element unwraps
        let single = LegacyType::normalize_union(vec![p(PrimitiveType::I64)]);
        assert_eq!(single, p(PrimitiveType::I64));
    }
}

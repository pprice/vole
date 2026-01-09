// src/sema/types.rs

use crate::frontend::{PrimitiveType, Symbol};
use crate::identity::{ModuleId, NameId};

/// Resolved types in the type system
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// Signed integers
    I8,
    I16,
    I32,
    I64,
    I128,
    /// Unsigned integers
    U8,
    U16,
    U32,
    U64,
    /// Floating point
    F32,
    F64,
    /// Other primitives
    Bool,
    String,
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
    Union(Vec<Type>),
    /// Range type (e.g., 0..10)
    Range,
    /// Array type (e.g., [i32], [string])
    Array(Box<Type>),
    /// Function type
    Function(FunctionType),
    /// Unknown (for type inference)
    Unknown,
    /// Error type (for error recovery)
    Error,
    /// The metatype - the type of types themselves
    /// e.g., `i32` has type `Type`, `let MyInt = i32` assigns a type value
    Type,
    /// Class instance type
    Class(ClassType),
    /// Record instance type
    Record(RecordType),
    /// Interface type
    Interface(InterfaceType),
    /// Error type (e.g., DivByZero)
    ErrorType(ErrorTypeInfo),
    /// Fallible return type: fallible(T, E)
    Fallible(FallibleType),
    /// Module type (from import expression)
    Module(ModuleType),
    /// Runtime iterator type - represents builtin iterators (array.iter(), range.iter(), etc.)
    /// These are raw pointers to UnifiedIterator and should call external functions directly
    /// without interface boxing. The inner type is the element type.
    RuntimeIterator(Box<Type>),
    /// Type parameter (e.g., T in func identity<T>(x: T) -> T)
    /// Only valid within generic context during type checking
    TypeParam(Symbol),
    /// Generic type instance (e.g., Box<i64>, Result<string, i64>)
    GenericInstance {
        /// Name of the generic type definition
        def: NameId,
        /// Concrete type arguments
        args: Vec<Type>,
    },
    /// Tuple type - heterogeneous fixed-size collection
    /// e.g., [i32, string, bool] - different types per position
    Tuple(Vec<Type>),
    /// Fixed-size array - homogeneous fixed-size array
    /// e.g., [i32; 10] - single element type, compile-time known size
    FixedArray {
        element: Box<Type>,
        size: usize,
    },
}

#[derive(Debug, Clone, Eq)]
pub struct FunctionType {
    pub params: Vec<Type>,
    pub return_type: Box<Type>,
    /// If true, this function is a closure (has captures) and needs
    /// to be called with the closure pointer as the first argument.
    /// The closure pointer is passed implicitly and is not included in `params`.
    pub is_closure: bool,
}

/// Field information for a class/record
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
    pub slot: usize, // Compile-time slot index
}

/// Class type information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassType {
    pub name_id: NameId,
    pub fields: Vec<StructField>,
}

/// Record type information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordType {
    pub name_id: NameId,
    pub fields: Vec<StructField>,
    /// Type arguments for generic records (empty for non-generic records)
    pub type_args: Vec<Type>,
}

/// Interface type information
#[derive(Debug, Clone, Eq)]
pub struct InterfaceType {
    /// Canonical name ID for cross-interner lookups
    pub name_id: NameId,
    pub type_args: Vec<Type>,
    pub methods: Vec<InterfaceMethodType>,
    pub extends: Vec<Symbol>, // Parent interfaces
}

// Custom PartialEq to compare only name_id and type_args
// This is needed because Symbol is interner-specific and methods can differ
// when interfaces are loaded from different contexts
impl PartialEq for InterfaceType {
    fn eq(&self, other: &Self) -> bool {
        self.name_id == other.name_id && self.type_args == other.type_args
    }
}

/// Method signature in an interface
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceMethodType {
    pub name: Symbol,
    pub params: Vec<Type>,
    pub return_type: Box<Type>,
    pub has_default: bool, // True if interface provides default implementation
}

/// Error type definition (e.g., DivByZero, OutOfRange { value: i32 })
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ErrorTypeInfo {
    pub name: Symbol,
    pub name_id: NameId,
    pub fields: Vec<StructField>,
}

/// Fallible type: fallible(T, E)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FallibleType {
    pub success_type: Box<Type>,
    pub error_type: Box<Type>, // ErrorType or Union of ErrorTypes
}

/// A constant value that can be stored in a module
#[derive(Debug, Clone, PartialEq)]
pub enum ConstantValue {
    I64(i64),
    F64(f64),
    Bool(bool),
    String(String),
}

impl Eq for ConstantValue {}

/// Module type: represents an imported module with its exports
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleType {
    pub module_id: ModuleId,
    /// Exports keyed by fully-qualified name id
    pub exports: std::collections::HashMap<NameId, Type>,
    /// Constant values from the module (let PI = 3.14...)
    pub constants: std::collections::HashMap<NameId, ConstantValue>,
    /// Names of functions that are external (FFI) - others are pure Vole
    pub external_funcs: std::collections::HashSet<NameId>,
}

impl PartialEq for FunctionType {
    fn eq(&self, other: &Self) -> bool {
        // is_closure is not part of type equality - a closure () -> i64 is
        // compatible with a function type () -> i64 for type checking purposes
        self.params == other.params && self.return_type == other.return_type
    }
}

impl Type {
    pub fn from_primitive(p: PrimitiveType) -> Self {
        match p {
            PrimitiveType::I8 => Type::I8,
            PrimitiveType::I16 => Type::I16,
            PrimitiveType::I32 => Type::I32,
            PrimitiveType::I64 => Type::I64,
            PrimitiveType::I128 => Type::I128,
            PrimitiveType::U8 => Type::U8,
            PrimitiveType::U16 => Type::U16,
            PrimitiveType::U32 => Type::U32,
            PrimitiveType::U64 => Type::U64,
            PrimitiveType::F32 => Type::F32,
            PrimitiveType::F64 => Type::F64,
            PrimitiveType::Bool => Type::Bool,
            PrimitiveType::String => Type::String,
        }
    }

    /// Check if this type is numeric (can do arithmetic)
    pub fn is_numeric(&self) -> bool {
        matches!(
            self,
            Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
                | Type::F32
                | Type::F64
        )
    }

    /// Check if this type is an integer
    pub fn is_integer(&self) -> bool {
        matches!(
            self,
            Type::I8
                | Type::I16
                | Type::I32
                | Type::I64
                | Type::I128
                | Type::U8
                | Type::U16
                | Type::U32
                | Type::U64
        )
    }

    /// Check if this is a signed integer type
    pub fn is_signed(&self) -> bool {
        matches!(
            self,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128
        )
    }

    /// Check if this is an unsigned integer type
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Type::U8 | Type::U16 | Type::U32 | Type::U64)
    }

    /// Check if this is a floating point type
    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }

    /// Get the bit width of a numeric type
    pub fn bit_width(&self) -> Option<u8> {
        match self {
            Type::I8 | Type::U8 => Some(8),
            Type::I16 | Type::U16 => Some(16),
            Type::I32 | Type::U32 | Type::F32 => Some(32),
            Type::I64 | Type::U64 | Type::F64 => Some(64),
            Type::I128 => Some(128),
            _ => None,
        }
    }

    /// Check if this type can be implicitly widened to target type
    pub fn can_widen_to(&self, target: &Type) -> bool {
        if self == target {
            return true;
        }
        match (self, target) {
            // Signed to larger signed
            (Type::I8, Type::I16 | Type::I32 | Type::I64 | Type::I128) => true,
            (Type::I16, Type::I32 | Type::I64 | Type::I128) => true,
            (Type::I32, Type::I64 | Type::I128) => true,
            (Type::I64, Type::I128) => true,
            // Unsigned to larger unsigned
            (Type::U8, Type::U16 | Type::U32 | Type::U64) => true,
            (Type::U16, Type::U32 | Type::U64) => true,
            (Type::U32, Type::U64) => true,
            // Unsigned to larger signed (always fits)
            (Type::U8, Type::I16 | Type::I32 | Type::I64 | Type::I128) => true,
            (Type::U16, Type::I32 | Type::I64 | Type::I128) => true,
            (Type::U32, Type::I64 | Type::I128) => true,
            (Type::U64, Type::I128) => true,
            // Float widening
            (Type::F32, Type::F64) => true,
            _ => false,
        }
    }

    /// Get the type name for error messages
    pub fn name(&self) -> &'static str {
        match self {
            Type::I8 => "i8",
            Type::I16 => "i16",
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::I128 => "i128",
            Type::U8 => "u8",
            Type::U16 => "u16",
            Type::U32 => "u32",
            Type::U64 => "u64",
            Type::F32 => "f32",
            Type::F64 => "f64",
            Type::Bool => "bool",
            Type::String => "string",
            Type::Void => "void",
            Type::Nil => "nil",
            Type::Done => "Done",
            Type::Union(_) => "union", // Display impl handles full representation
            Type::Range => "range",
            Type::Array(_) => "array",
            Type::Function(_) => "function",
            Type::Unknown => "unknown",
            Type::Error => "error",
            Type::Type => "type",
            Type::Class(_) => "class",
            Type::Record(_) => "record",
            Type::Interface(_) => "interface",
            Type::ErrorType(_) => "error",
            Type::Fallible(_) => "fallible",
            Type::Module(_) => "module",
            Type::TypeParam(_) => "type parameter",
            Type::GenericInstance { .. } => "generic",
            Type::RuntimeIterator(_) => "iterator",
            Type::Tuple(_) => "tuple",
            Type::FixedArray { .. } => "fixed array",
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
                    1 => Some(non_nil.into_iter().next().unwrap()),
                    _ => Some(Type::Union(non_nil)),
                }
            }
            _ => None,
        }
    }

    /// Create an optional type (T | nil)
    pub fn optional(inner: Type) -> Type {
        Type::Union(vec![inner, Type::Nil])
    }

    /// Normalize a union: flatten nested unions, sort, dedupe, unwrap single-element
    pub fn normalize_union(mut types: Vec<Type>) -> Type {
        // Flatten nested unions
        let mut flattened = Vec::new();
        for ty in types.drain(..) {
            match ty {
                Type::Union(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }

        // Sort for canonical representation (use debug string for now)
        flattened.sort_by_key(|t| format!("{:?}", t));

        // Dedupe
        flattened.dedup();

        // Unwrap single-element union
        if flattened.len() == 1 {
            flattened.into_iter().next().unwrap()
        } else {
            Type::Union(flattened)
        }
    }

    /// Get a field from a class or record type by name
    pub fn get_field(&self, field: &str) -> Option<&StructField> {
        match self {
            Type::Class(c) => c.fields.iter().find(|f| f.name == field),
            Type::Record(r) => r.fields.iter().find(|f| f.name == field),
            _ => None,
        }
    }

    /// Promote two numeric types to their common supertype
    pub fn promote(left: &Type, right: &Type) -> Type {
        match (left, right) {
            (Type::F64, _) | (_, Type::F64) => Type::F64,
            (Type::F32, _) | (_, Type::F32) => Type::F32,
            (Type::I64, _) | (_, Type::I64) => Type::I64,
            (Type::I32, _) | (_, Type::I32) => Type::I32,
            _ => left.clone(),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
            Type::Class(_) => write!(f, "class"),
            Type::Record(_) => write!(f, "record"),
            Type::ErrorType(_) => {
                write!(f, "error")
            }
            Type::Fallible(ft) => {
                write!(f, "fallible({}, {})", ft.success_type, ft.error_type)
            }
            Type::Module(m) => write!(f, "module(id:{})", m.module_id.index()),
            Type::TypeParam(sym) => write!(f, "{:?}", sym), // Symbol Debug shows interned string
            Type::GenericInstance { def, args } => {
                write!(f, "{:?}<", def)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ">")
            }
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

    #[test]
    fn type_is_numeric() {
        assert!(Type::I8.is_numeric());
        assert!(Type::I16.is_numeric());
        assert!(Type::I32.is_numeric());
        assert!(Type::I64.is_numeric());
        assert!(Type::I128.is_numeric());
        assert!(Type::U8.is_numeric());
        assert!(Type::U16.is_numeric());
        assert!(Type::U32.is_numeric());
        assert!(Type::U64.is_numeric());
        assert!(Type::F32.is_numeric());
        assert!(Type::F64.is_numeric());
        assert!(!Type::Bool.is_numeric());
        assert!(!Type::String.is_numeric());
    }

    #[test]
    fn type_is_integer() {
        assert!(Type::I32.is_integer());
        assert!(Type::I64.is_integer());
        assert!(Type::U32.is_integer());
        assert!(!Type::F64.is_integer());
        assert!(!Type::Bool.is_integer());
    }

    #[test]
    fn type_is_signed_unsigned() {
        assert!(Type::I32.is_signed());
        assert!(Type::I128.is_signed());
        assert!(!Type::U32.is_signed());
        assert!(!Type::F64.is_signed());

        assert!(Type::U32.is_unsigned());
        assert!(Type::U64.is_unsigned());
        assert!(!Type::I32.is_unsigned());
    }

    #[test]
    fn type_widening() {
        // Signed widening
        assert!(Type::I8.can_widen_to(&Type::I16));
        assert!(Type::I8.can_widen_to(&Type::I64));
        assert!(!Type::I64.can_widen_to(&Type::I32));

        // Unsigned widening
        assert!(Type::U8.can_widen_to(&Type::U16));
        assert!(Type::U16.can_widen_to(&Type::U64));

        // Unsigned to signed
        assert!(Type::U8.can_widen_to(&Type::I16));
        assert!(Type::U32.can_widen_to(&Type::I64));
        assert!(!Type::U64.can_widen_to(&Type::I64));

        // Float widening
        assert!(Type::F32.can_widen_to(&Type::F64));
        assert!(!Type::F64.can_widen_to(&Type::F32));
    }

    #[test]
    fn type_from_primitive() {
        assert_eq!(Type::from_primitive(PrimitiveType::I32), Type::I32);
        assert_eq!(Type::from_primitive(PrimitiveType::U64), Type::U64);
        assert_eq!(Type::from_primitive(PrimitiveType::F32), Type::F32);
    }

    #[test]
    fn type_optional() {
        let opt = Type::optional(Type::I32);
        assert!(opt.is_optional());
        assert_eq!(opt.unwrap_optional(), Some(Type::I32));
    }

    #[test]
    fn type_normalize_union() {
        // Nested unions flatten
        let normalized =
            Type::normalize_union(vec![Type::I32, Type::Union(vec![Type::String, Type::Nil])]);
        assert!(matches!(normalized, Type::Union(v) if v.len() == 3));

        // Single element unwraps
        let single = Type::normalize_union(vec![Type::I32]);
        assert_eq!(single, Type::I32);
    }
}

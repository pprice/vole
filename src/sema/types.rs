// src/sema/types.rs

use crate::frontend::PrimitiveType;

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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionType {
    pub params: Vec<Type>,
    pub return_type: Box<Type>,
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
            Type::Union(_) => "union", // Display impl handles full representation
            Type::Range => "range",
            Type::Array(_) => "array",
            Type::Function(_) => "function",
            Type::Unknown => "unknown",
            Type::Error => "error",
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
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Union(types) => {
                let parts: Vec<_> = types.iter().map(|t| t.name()).collect();
                write!(f, "{}", parts.join(" | "))
            }
            _ => write!(f, "{}", self.name()),
        }
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
        let normalized = Type::normalize_union(vec![
            Type::I32,
            Type::Union(vec![Type::String, Type::Nil]),
        ]);
        assert!(matches!(normalized, Type::Union(v) if v.len() == 3));

        // Single element unwraps
        let single = Type::normalize_union(vec![Type::I32]);
        assert_eq!(single, Type::I32);
    }
}

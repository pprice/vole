// src/sema/types.rs

use crate::frontend::PrimitiveType;

/// Resolved types in the type system
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// Primitive types
    I32,
    I64,
    F64,
    Bool,
    String,
    /// Void (no return value)
    Void,
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
            PrimitiveType::I32 => Type::I32,
            PrimitiveType::I64 => Type::I64,
            PrimitiveType::F64 => Type::F64,
            PrimitiveType::Bool => Type::Bool,
            PrimitiveType::String => Type::String,
        }
    }

    /// Check if this type is numeric (can do arithmetic)
    pub fn is_numeric(&self) -> bool {
        matches!(self, Type::I32 | Type::I64 | Type::F64)
    }

    /// Check if this type is an integer
    pub fn is_integer(&self) -> bool {
        matches!(self, Type::I32 | Type::I64)
    }

    /// Get the type name for error messages
    pub fn name(&self) -> &'static str {
        match self {
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::F64 => "f64",
            Type::Bool => "bool",
            Type::String => "string",
            Type::Void => "void",
            Type::Range => "range",
            Type::Array(_) => "array",
            Type::Function(_) => "function",
            Type::Unknown => "unknown",
            Type::Error => "error",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_is_numeric() {
        assert!(Type::I32.is_numeric());
        assert!(Type::I64.is_numeric());
        assert!(Type::F64.is_numeric());
        assert!(!Type::Bool.is_numeric());
        assert!(!Type::String.is_numeric());
    }

    #[test]
    fn type_is_integer() {
        assert!(Type::I32.is_integer());
        assert!(Type::I64.is_integer());
        assert!(!Type::F64.is_integer());
        assert!(!Type::Bool.is_integer());
    }

    #[test]
    fn type_from_primitive() {
        assert_eq!(Type::from_primitive(PrimitiveType::I32), Type::I32);
        assert_eq!(Type::from_primitive(PrimitiveType::F64), Type::F64);
        assert_eq!(Type::from_primitive(PrimitiveType::String), Type::String);
    }
}

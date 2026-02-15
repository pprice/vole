// primitive_type.rs
//
// Primitive type enumeration shared across all compiler crates.

/// Enumeration of primitive types in the Vole type system.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
}

// src/sema/types/primitive.rs
//
// Primitive type enum consolidating all primitive type variants.
// This reduces the Type enum from 25+ variants and centralizes
// all primitive-related operations.

use vole_frontend::PrimitiveType as AstPrimitiveType;

/// Primitive types in the Vole type system.
/// Consolidates signed/unsigned integers, floats, bool, and string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    // Signed integers
    I8,
    I16,
    I32,
    I64,
    I128,
    // Unsigned integers
    U8,
    U16,
    U32,
    U64,
    // Floating point
    F32,
    F64,
    // Other primitives
    Bool,
    String,
}

impl PrimitiveType {
    /// Get the bit width of this primitive type.
    /// Returns None for Bool and String.
    pub fn bit_width(self) -> Option<u8> {
        match self {
            PrimitiveType::I8 | PrimitiveType::U8 => Some(8),
            PrimitiveType::I16 | PrimitiveType::U16 => Some(16),
            PrimitiveType::I32 | PrimitiveType::U32 | PrimitiveType::F32 => Some(32),
            PrimitiveType::I64 | PrimitiveType::U64 | PrimitiveType::F64 => Some(64),
            PrimitiveType::I128 => Some(128),
            PrimitiveType::Bool | PrimitiveType::String => None,
        }
    }

    /// Check if this type is numeric (can do arithmetic).
    pub fn is_numeric(self) -> bool {
        matches!(
            self,
            PrimitiveType::I8
                | PrimitiveType::I16
                | PrimitiveType::I32
                | PrimitiveType::I64
                | PrimitiveType::I128
                | PrimitiveType::U8
                | PrimitiveType::U16
                | PrimitiveType::U32
                | PrimitiveType::U64
                | PrimitiveType::F32
                | PrimitiveType::F64
        )
    }

    /// Check if this type is a signed integer.
    pub fn is_signed(self) -> bool {
        matches!(
            self,
            PrimitiveType::I8
                | PrimitiveType::I16
                | PrimitiveType::I32
                | PrimitiveType::I64
                | PrimitiveType::I128
        )
    }

    /// Check if this type is an unsigned integer.
    pub fn is_unsigned(self) -> bool {
        matches!(
            self,
            PrimitiveType::U8 | PrimitiveType::U16 | PrimitiveType::U32 | PrimitiveType::U64
        )
    }

    /// Check if this type is an integer (signed or unsigned).
    pub fn is_integer(self) -> bool {
        self.is_signed() || self.is_unsigned()
    }

    /// Check if this type is a floating point type.
    pub fn is_float(self) -> bool {
        matches!(self, PrimitiveType::F32 | PrimitiveType::F64)
    }

    /// Check if this type can be implicitly widened to target type.
    pub fn can_widen_to(self, target: PrimitiveType) -> bool {
        if self == target {
            return true;
        }
        match (self, target) {
            // Signed to larger signed
            (
                PrimitiveType::I8,
                PrimitiveType::I16 | PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128,
            ) => true,
            (PrimitiveType::I16, PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128) => {
                true
            }
            (PrimitiveType::I32, PrimitiveType::I64 | PrimitiveType::I128) => true,
            (PrimitiveType::I64, PrimitiveType::I128) => true,
            // Unsigned to larger unsigned
            (PrimitiveType::U8, PrimitiveType::U16 | PrimitiveType::U32 | PrimitiveType::U64) => {
                true
            }
            (PrimitiveType::U16, PrimitiveType::U32 | PrimitiveType::U64) => true,
            (PrimitiveType::U32, PrimitiveType::U64) => true,
            // Unsigned to larger signed (always fits)
            (
                PrimitiveType::U8,
                PrimitiveType::I16 | PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128,
            ) => true,
            (PrimitiveType::U16, PrimitiveType::I32 | PrimitiveType::I64 | PrimitiveType::I128) => {
                true
            }
            (PrimitiveType::U32, PrimitiveType::I64 | PrimitiveType::I128) => true,
            (PrimitiveType::U64, PrimitiveType::I128) => true,
            // Float widening
            (PrimitiveType::F32, PrimitiveType::F64) => true,
            _ => false,
        }
    }

    /// Get the type name for error messages.
    pub fn name(self) -> &'static str {
        match self {
            PrimitiveType::I8 => "i8",
            PrimitiveType::I16 => "i16",
            PrimitiveType::I32 => "i32",
            PrimitiveType::I64 => "i64",
            PrimitiveType::I128 => "i128",
            PrimitiveType::U8 => "u8",
            PrimitiveType::U16 => "u16",
            PrimitiveType::U32 => "u32",
            PrimitiveType::U64 => "u64",
            PrimitiveType::F32 => "f32",
            PrimitiveType::F64 => "f64",
            PrimitiveType::Bool => "bool",
            PrimitiveType::String => "string",
        }
    }

    /// Convert from AST PrimitiveType to sema PrimitiveType.
    pub fn from_ast(p: AstPrimitiveType) -> Self {
        match p {
            AstPrimitiveType::I8 => PrimitiveType::I8,
            AstPrimitiveType::I16 => PrimitiveType::I16,
            AstPrimitiveType::I32 => PrimitiveType::I32,
            AstPrimitiveType::I64 => PrimitiveType::I64,
            AstPrimitiveType::I128 => PrimitiveType::I128,
            AstPrimitiveType::U8 => PrimitiveType::U8,
            AstPrimitiveType::U16 => PrimitiveType::U16,
            AstPrimitiveType::U32 => PrimitiveType::U32,
            AstPrimitiveType::U64 => PrimitiveType::U64,
            AstPrimitiveType::F32 => PrimitiveType::F32,
            AstPrimitiveType::F64 => PrimitiveType::F64,
            AstPrimitiveType::Bool => PrimitiveType::Bool,
            AstPrimitiveType::String => PrimitiveType::String,
        }
    }

    /// Promote two numeric types to their common supertype.
    /// Returns None if either type is non-numeric.
    pub fn promote(left: PrimitiveType, right: PrimitiveType) -> Option<PrimitiveType> {
        if !left.is_numeric() || !right.is_numeric() {
            return None;
        }
        Some(match (left, right) {
            (PrimitiveType::F64, _) | (_, PrimitiveType::F64) => PrimitiveType::F64,
            (PrimitiveType::F32, _) | (_, PrimitiveType::F32) => PrimitiveType::F32,
            (PrimitiveType::I128, _) | (_, PrimitiveType::I128) => PrimitiveType::I128,
            (PrimitiveType::I64, _) | (_, PrimitiveType::I64) => PrimitiveType::I64,
            (PrimitiveType::U64, _) | (_, PrimitiveType::U64) => PrimitiveType::U64,
            (PrimitiveType::I32, _) | (_, PrimitiveType::I32) => PrimitiveType::I32,
            (PrimitiveType::U32, _) | (_, PrimitiveType::U32) => PrimitiveType::U32,
            (PrimitiveType::I16, _) | (_, PrimitiveType::I16) => PrimitiveType::I16,
            (PrimitiveType::U16, _) | (_, PrimitiveType::U16) => PrimitiveType::U16,
            (PrimitiveType::I8, _) | (_, PrimitiveType::I8) => PrimitiveType::I8,
            (PrimitiveType::U8, _) | (_, PrimitiveType::U8) => PrimitiveType::U8,
            _ => left, // Both bool/string - shouldn't happen due to is_numeric check
        })
    }
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_numeric() {
        assert!(PrimitiveType::I8.is_numeric());
        assert!(PrimitiveType::I16.is_numeric());
        assert!(PrimitiveType::I32.is_numeric());
        assert!(PrimitiveType::I64.is_numeric());
        assert!(PrimitiveType::I128.is_numeric());
        assert!(PrimitiveType::U8.is_numeric());
        assert!(PrimitiveType::U16.is_numeric());
        assert!(PrimitiveType::U32.is_numeric());
        assert!(PrimitiveType::U64.is_numeric());
        assert!(PrimitiveType::F32.is_numeric());
        assert!(PrimitiveType::F64.is_numeric());
        assert!(!PrimitiveType::Bool.is_numeric());
        assert!(!PrimitiveType::String.is_numeric());
    }

    #[test]
    fn test_is_integer() {
        assert!(PrimitiveType::I32.is_integer());
        assert!(PrimitiveType::I64.is_integer());
        assert!(PrimitiveType::U32.is_integer());
        assert!(!PrimitiveType::F64.is_integer());
        assert!(!PrimitiveType::Bool.is_integer());
    }

    #[test]
    fn test_is_signed_unsigned() {
        assert!(PrimitiveType::I32.is_signed());
        assert!(PrimitiveType::I128.is_signed());
        assert!(!PrimitiveType::U32.is_signed());
        assert!(!PrimitiveType::F64.is_signed());

        assert!(PrimitiveType::U32.is_unsigned());
        assert!(PrimitiveType::U64.is_unsigned());
        assert!(!PrimitiveType::I32.is_unsigned());
    }

    #[test]
    fn test_widening() {
        // Signed widening
        assert!(PrimitiveType::I8.can_widen_to(PrimitiveType::I16));
        assert!(PrimitiveType::I8.can_widen_to(PrimitiveType::I64));
        assert!(!PrimitiveType::I64.can_widen_to(PrimitiveType::I32));

        // Unsigned widening
        assert!(PrimitiveType::U8.can_widen_to(PrimitiveType::U16));
        assert!(PrimitiveType::U16.can_widen_to(PrimitiveType::U64));

        // Unsigned to signed
        assert!(PrimitiveType::U8.can_widen_to(PrimitiveType::I16));
        assert!(PrimitiveType::U32.can_widen_to(PrimitiveType::I64));
        assert!(!PrimitiveType::U64.can_widen_to(PrimitiveType::I64));

        // Float widening
        assert!(PrimitiveType::F32.can_widen_to(PrimitiveType::F64));
        assert!(!PrimitiveType::F64.can_widen_to(PrimitiveType::F32));
    }

    #[test]
    fn test_bit_width() {
        assert_eq!(PrimitiveType::I8.bit_width(), Some(8));
        assert_eq!(PrimitiveType::I16.bit_width(), Some(16));
        assert_eq!(PrimitiveType::I32.bit_width(), Some(32));
        assert_eq!(PrimitiveType::I64.bit_width(), Some(64));
        assert_eq!(PrimitiveType::I128.bit_width(), Some(128));
        assert_eq!(PrimitiveType::F32.bit_width(), Some(32));
        assert_eq!(PrimitiveType::F64.bit_width(), Some(64));
        assert_eq!(PrimitiveType::Bool.bit_width(), None);
        assert_eq!(PrimitiveType::String.bit_width(), None);
    }

    #[test]
    fn test_promote() {
        assert_eq!(
            PrimitiveType::promote(PrimitiveType::I32, PrimitiveType::I64),
            Some(PrimitiveType::I64)
        );
        assert_eq!(
            PrimitiveType::promote(PrimitiveType::F32, PrimitiveType::I32),
            Some(PrimitiveType::F32)
        );
        assert_eq!(
            PrimitiveType::promote(PrimitiveType::F32, PrimitiveType::F64),
            Some(PrimitiveType::F64)
        );
        assert_eq!(
            PrimitiveType::promote(PrimitiveType::Bool, PrimitiveType::I32),
            None
        );
    }

    #[test]
    fn test_from_ast() {
        use vole_frontend::PrimitiveType as AstPrimitive;
        assert_eq!(
            PrimitiveType::from_ast(AstPrimitive::I32),
            PrimitiveType::I32
        );
        assert_eq!(
            PrimitiveType::from_ast(AstPrimitive::U64),
            PrimitiveType::U64
        );
        assert_eq!(
            PrimitiveType::from_ast(AstPrimitive::F32),
            PrimitiveType::F32
        );
    }
}

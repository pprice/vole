// src/sema/compatibility/traits.rs
//
// TypeCompatibility trait for unified type compatibility checking.

use crate::sema::types::Type;

/// Trait for type compatibility operations.
///
/// This trait provides a unified interface for type compatibility checking,
/// including widening, numeric properties, and literal fitting.
///
/// Currently implemented only for `Type`, but abstracted into a trait to:
/// - Centralize compatibility logic documentation
/// - Enable potential future extensions (mock types for testing)
/// - Provide clear API contract for type system operations
pub trait TypeCompatibility {
    /// Check if this type is compatible with (assignable to) another type.
    fn is_compatible(&self, other: &Type) -> bool;

    /// Check if this type can be implicitly widened to the target type.
    /// e.g., i32 -> i64, f32 -> f64, u8 -> i16
    fn can_widen_to(&self, target: &Type) -> bool;

    /// Check if this type is numeric (supports arithmetic operations).
    fn is_numeric(&self) -> bool;

    /// Check if this type is an integer type.
    fn is_integer(&self) -> bool;

    /// Check if this type is a signed integer.
    fn is_signed(&self) -> bool;

    /// Check if this type is a floating point type.
    fn is_float(&self) -> bool;

    /// Check if this type is an unsigned integer.
    fn is_unsigned(&self) -> bool;

    /// Get the bit width of this type, if applicable.
    fn bit_width(&self) -> Option<u8>;

    /// Check if an integer literal value fits within this type's range.
    fn fits_literal(&self, value: i64) -> bool;
}

impl TypeCompatibility for Type {
    fn is_compatible(&self, other: &Type) -> bool {
        super::core::types_compatible_core(self, other)
    }

    fn can_widen_to(&self, target: &Type) -> bool {
        // Delegate to Type's existing method
        Type::can_widen_to(self, target)
    }

    fn is_numeric(&self) -> bool {
        Type::is_numeric(self)
    }

    fn is_integer(&self) -> bool {
        Type::is_integer(self)
    }

    fn is_signed(&self) -> bool {
        Type::is_signed(self)
    }

    fn is_float(&self) -> bool {
        Type::is_float(self)
    }

    fn is_unsigned(&self) -> bool {
        Type::is_unsigned(self)
    }

    fn bit_width(&self) -> Option<u8> {
        Type::bit_width(self)
    }

    fn fits_literal(&self, value: i64) -> bool {
        super::core::literal_fits(value, self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::types::PrimitiveType;

    #[test]
    fn test_trait_is_numeric() {
        let i32_ty = Type::Primitive(PrimitiveType::I32);
        let bool_ty = Type::Primitive(PrimitiveType::Bool);

        assert!(i32_ty.is_numeric());
        assert!(!bool_ty.is_numeric());
    }

    #[test]
    fn test_trait_can_widen_to() {
        let i32_ty = Type::Primitive(PrimitiveType::I32);
        let i64_ty = Type::Primitive(PrimitiveType::I64);
        let string_ty = Type::Primitive(PrimitiveType::String);

        assert!(i32_ty.can_widen_to(&i64_ty));
        assert!(!i64_ty.can_widen_to(&i32_ty));
        assert!(!i32_ty.can_widen_to(&string_ty));
    }

    #[test]
    fn test_trait_fits_literal() {
        let i8_ty = Type::Primitive(PrimitiveType::I8);
        let i32_ty = Type::Primitive(PrimitiveType::I32);

        assert!(i8_ty.fits_literal(100));
        assert!(!i8_ty.fits_literal(200));
        assert!(i32_ty.fits_literal(200));
    }

    #[test]
    fn test_trait_is_compatible() {
        let i32_ty = Type::Primitive(PrimitiveType::I32);
        let i64_ty = Type::Primitive(PrimitiveType::I64);

        // Same type is compatible
        assert!(i32_ty.is_compatible(&i32_ty));
        // Widening is compatible
        assert!(i32_ty.is_compatible(&i64_ty));
        // Narrowing is not compatible
        assert!(!i64_ty.is_compatible(&i32_ty));
    }
}

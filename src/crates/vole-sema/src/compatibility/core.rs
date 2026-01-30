// src/sema/compatibility/core.rs
//
// Type compatibility checking functions using TypeId.

use crate::type_arena::{SemaType, TypeArena, TypeId};

/// Check if two types are compatible.
pub fn types_compatible_core_id(from: TypeId, to: TypeId, arena: &TypeArena) -> bool {
    // TypeId equality is O(1)
    if from == to {
        return true;
    }

    let from_ty = arena.get(from);
    let to_ty = arena.get(to);

    // Check widening (primitive numeric types)
    if can_widen_to_id(from, to, arena) {
        return true;
    }

    // Allow numeric coercion
    if is_integer_id(from_ty) && to == arena.i64() {
        return true;
    }
    if is_numeric_id(from_ty) && to == arena.f64() {
        return true;
    }

    // Check if assigning to a union that contains the from type
    if let SemaType::Union(variants) = to_ty {
        // Direct containment
        if variants.contains(&from) {
            return true;
        }
        // Also check if from can widen into a union variant
        for &variant in variants.iter() {
            if can_widen_to_id(from, variant, arena) {
                return true;
            }
        }
    }

    // Nil is compatible with any optional (union containing Nil)
    if from == arena.nil() && is_optional_id(to, arena) {
        return true;
    }

    // Invalid type is compatible with anything (for error recovery)
    if from == arena.invalid() || to == arena.invalid() {
        return true;
    }

    // Never is compatible with any type (bottom type)
    // The never type has no values, so it can be coerced to any type
    if from.is_never() {
        return true;
    }

    // Any type is compatible with unknown (top type)
    // The unknown type can hold any value
    if to.is_unknown() {
        return true;
    }

    // Class compatibility: compare by type_def_id and type_args
    if let (
        SemaType::Class {
            type_def_id: from_def,
            type_args: from_args,
        },
        SemaType::Class {
            type_def_id: to_def,
            type_args: to_args,
        },
    ) = (from_ty, to_ty)
        && from_def == to_def
        && from_args.len() == to_args.len()
        && from_args
            .iter()
            .zip(to_args.iter())
            .all(|(&f, &t)| types_compatible_core_id(f, t, arena))
    {
        return true;
    }

    // Record compatibility: compare by type_def_id and type_args
    if let (
        SemaType::Record {
            type_def_id: from_def,
            type_args: from_args,
        },
        SemaType::Record {
            type_def_id: to_def,
            type_args: to_args,
        },
    ) = (from_ty, to_ty)
        && from_def == to_def
        && from_args.len() == to_args.len()
        && from_args
            .iter()
            .zip(to_args.iter())
            .all(|(&f, &t)| types_compatible_core_id(f, t, arena))
    {
        return true;
    }

    // Struct compatibility: nominal (same type_def_id)
    if let (
        SemaType::Struct {
            type_def_id: from_def,
            type_args: from_args,
        },
        SemaType::Struct {
            type_def_id: to_def,
            type_args: to_args,
        },
    ) = (from_ty, to_ty)
        && from_def == to_def
        && from_args.len() == to_args.len()
        && from_args
            .iter()
            .zip(to_args.iter())
            .all(|(&f, &t)| types_compatible_core_id(f, t, arena))
    {
        return true;
    }

    // Tuple compatibility: same length and each element is compatible
    if let (SemaType::Tuple(from_elems), SemaType::Tuple(to_elems)) = (from_ty, to_ty)
        && from_elems.len() == to_elems.len()
    {
        return from_elems
            .iter()
            .zip(to_elems.iter())
            .all(|(&f, &t)| types_compatible_core_id(f, t, arena));
    }

    // Fixed array compatibility: same element type and same size
    if let (
        SemaType::FixedArray {
            element: from_elem,
            size: from_size,
        },
        SemaType::FixedArray {
            element: to_elem,
            size: to_size,
        },
    ) = (from_ty, to_ty)
        && from_size == to_size
    {
        return types_compatible_core_id(*from_elem, *to_elem, arena);
    }

    // Function type compatibility: same params and return type (ignore is_closure)
    if let (
        SemaType::Function {
            params: from_params,
            ret: from_ret,
            ..
        },
        SemaType::Function {
            params: to_params,
            ret: to_ret,
            ..
        },
    ) = (from_ty, to_ty)
        && from_params.len() == to_params.len()
        && from_params
            .iter()
            .zip(to_params.iter())
            .all(|(&f, &t)| types_compatible_core_id(f, t, arena))
        && types_compatible_core_id(*from_ret, *to_ret, arena)
    {
        return true;
    }

    false
}

/// Check if a type can be widened to another using TypeId
fn can_widen_to_id(from: TypeId, to: TypeId, arena: &TypeArena) -> bool {
    let from_ty = arena.get(from);
    let to_ty = arena.get(to);

    match (from_ty, to_ty) {
        (SemaType::Primitive(from_prim), SemaType::Primitive(to_prim)) => {
            from_prim.can_widen_to(*to_prim)
        }
        _ => false,
    }
}

/// Check if a SemaType is numeric
fn is_numeric_id(ty: &SemaType) -> bool {
    match ty {
        SemaType::Primitive(p) => p.is_numeric(),
        _ => false,
    }
}

/// Check if a SemaType is an integer
fn is_integer_id(ty: &SemaType) -> bool {
    match ty {
        SemaType::Primitive(p) => p.is_integer(),
        _ => false,
    }
}

/// Check if a TypeId represents an optional type (union containing nil)
fn is_optional_id(id: TypeId, arena: &TypeArena) -> bool {
    if let SemaType::Union(variants) = arena.get(id) {
        variants.contains(&arena.nil())
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_arena::TypeId;

    #[test]
    fn test_literal_fits_signed() {
        // i8 range: -128 to 127
        assert!(TypeId::I8.fits_literal(0));
        assert!(TypeId::I8.fits_literal(127));
        assert!(TypeId::I8.fits_literal(-128));
        assert!(!TypeId::I8.fits_literal(128));
        assert!(!TypeId::I8.fits_literal(-129));

        // i16 range
        assert!(TypeId::I16.fits_literal(32767));
        assert!(!TypeId::I16.fits_literal(32768));

        // i32 range
        assert!(TypeId::I32.fits_literal(2147483647));
        assert!(!TypeId::I32.fits_literal(2147483648));

        // i64 always fits
        assert!(TypeId::I64.fits_literal(i64::MAX));
        assert!(TypeId::I64.fits_literal(i64::MIN));
    }

    #[test]
    fn test_literal_fits_unsigned() {
        // u8 range: 0 to 255
        assert!(TypeId::U8.fits_literal(0));
        assert!(TypeId::U8.fits_literal(255));
        assert!(!TypeId::U8.fits_literal(256));
        assert!(!TypeId::U8.fits_literal(-1));

        // u16 range
        assert!(TypeId::U16.fits_literal(65535));
        assert!(!TypeId::U16.fits_literal(65536));

        // u32 range
        assert!(TypeId::U32.fits_literal(4294967295));
        assert!(!TypeId::U32.fits_literal(4294967296));

        // u64 accepts all positive i64 values
        assert!(TypeId::U64.fits_literal(0));
        assert!(TypeId::U64.fits_literal(i64::MAX));
        assert!(!TypeId::U64.fits_literal(-1));
    }

    #[test]
    fn test_literal_fits_float() {
        assert!(TypeId::F32.fits_literal(0));
        assert!(TypeId::F64.fits_literal(i64::MAX));
    }

    #[test]
    fn test_literal_fits_union() {
        let mut arena = TypeArena::new();
        let union_id = arena.union(vec![TypeId::I8, TypeId::I32]);
        assert!(arena.literal_fits_id(100, union_id)); // Fits in i8
        assert!(arena.literal_fits_id(1000, union_id)); // Fits in i32
        assert!(!arena.literal_fits_id(i64::MAX, union_id)); // Doesn't fit in either
    }

    #[test]
    fn test_types_compatible_same() {
        let arena = TypeArena::new();
        assert!(types_compatible_core_id(TypeId::I32, TypeId::I32, &arena));
        assert!(types_compatible_core_id(
            TypeId::STRING,
            TypeId::STRING,
            &arena
        ));
        assert!(types_compatible_core_id(TypeId::BOOL, TypeId::BOOL, &arena));
    }

    #[test]
    fn test_types_compatible_widening() {
        let arena = TypeArena::new();
        assert!(types_compatible_core_id(TypeId::I32, TypeId::I64, &arena));
        assert!(types_compatible_core_id(TypeId::F32, TypeId::F64, &arena));
        assert!(types_compatible_core_id(TypeId::U8, TypeId::I16, &arena));
    }

    #[test]
    fn test_types_compatible_union() {
        let mut arena = TypeArena::new();
        let union_id = arena.union(vec![TypeId::I32, TypeId::STRING]);
        assert!(types_compatible_core_id(TypeId::I32, union_id, &arena));
        assert!(types_compatible_core_id(TypeId::STRING, union_id, &arena));
        assert!(!types_compatible_core_id(TypeId::BOOL, union_id, &arena));
    }

    #[test]
    fn test_types_compatible_optional() {
        let mut arena = TypeArena::new();
        let optional_id = arena.optional(TypeId::I32);
        assert!(types_compatible_core_id(TypeId::NIL, optional_id, &arena));
        assert!(types_compatible_core_id(TypeId::I32, optional_id, &arena));
    }

    #[test]
    fn test_types_compatible_invalid() {
        let arena = TypeArena::new();
        let invalid = arena.invalid();
        assert!(types_compatible_core_id(invalid, TypeId::I32, &arena));
        assert!(types_compatible_core_id(TypeId::I32, invalid, &arena));
    }

    #[test]
    fn test_types_compatible_tuple() {
        let mut arena = TypeArena::new();
        let tuple1 = arena.tuple(vec![TypeId::I32, TypeId::STRING]);
        let tuple2 = arena.tuple(vec![TypeId::I32, TypeId::STRING]);
        let tuple3 = arena.tuple(vec![TypeId::I32, TypeId::BOOL]); // Different element
        let tuple4 = arena.tuple(vec![TypeId::I32]); // Different length

        assert!(types_compatible_core_id(tuple1, tuple2, &arena));
        assert!(!types_compatible_core_id(tuple1, tuple3, &arena));
        assert!(!types_compatible_core_id(tuple1, tuple4, &arena));
    }

    #[test]
    fn test_types_compatible_tuple_widening() {
        let mut arena = TypeArena::new();
        let narrow = arena.tuple(vec![TypeId::I32, TypeId::F32]);
        let wide = arena.tuple(vec![TypeId::I64, TypeId::F64]);
        assert!(types_compatible_core_id(narrow, wide, &arena));
    }

    #[test]
    fn test_types_compatible_fixed_array() {
        let mut arena = TypeArena::new();
        let arr1 = arena.fixed_array(TypeId::I32, 10);
        let arr2 = arena.fixed_array(TypeId::I32, 10);
        let arr3 = arena.fixed_array(TypeId::I32, 5); // Different size
        let arr4 = arena.fixed_array(TypeId::STRING, 10); // Different element

        assert!(types_compatible_core_id(arr1, arr2, &arena));
        assert!(!types_compatible_core_id(arr1, arr3, &arena));
        assert!(!types_compatible_core_id(arr1, arr4, &arena));
    }

    #[test]
    fn test_types_compatible_fixed_array_widening() {
        let mut arena = TypeArena::new();
        let narrow = arena.fixed_array(TypeId::I32, 5);
        let wide = arena.fixed_array(TypeId::I64, 5);
        assert!(types_compatible_core_id(narrow, wide, &arena));
    }
}

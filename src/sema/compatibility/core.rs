// src/sema/compatibility.rs
//
// Type compatibility checking functions.
// These are pure functions that determine if types are compatible for assignment.

use crate::sema::type_arena::{SemaType, TypeArena, TypeId};
use crate::sema::types::{FunctionType, LegacyType, NominalType, PrimitiveType};

/// Check if an integer literal value fits within a type's range
pub fn literal_fits(value: i64, target: &LegacyType) -> bool {
    match target {
        LegacyType::Primitive(prim) => match prim {
            PrimitiveType::I8 => value >= i8::MIN as i64 && value <= i8::MAX as i64,
            PrimitiveType::I16 => value >= i16::MIN as i64 && value <= i16::MAX as i64,
            PrimitiveType::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
            PrimitiveType::I64 => true,
            PrimitiveType::I128 => true, // i64 always fits in i128
            PrimitiveType::U8 => value >= 0 && value <= u8::MAX as i64,
            PrimitiveType::U16 => value >= 0 && value <= u16::MAX as i64,
            PrimitiveType::U32 => value >= 0 && value <= u32::MAX as i64,
            PrimitiveType::U64 => value >= 0, // i64 positive values fit
            PrimitiveType::F32 | PrimitiveType::F64 => true, // Integers can become floats
            PrimitiveType::Bool | PrimitiveType::String => false,
        },
        // For unions, check if literal fits any numeric variant
        LegacyType::Union(variants) => variants.iter().any(|v| literal_fits(value, v)),
        _ => false,
    }
}

/// Check if two types are compatible (assignable) without considering interfaces.
///
/// This function handles all type compatibility checks except for function-to-interface
/// compatibility, which requires access to the interface registry.
///
/// Returns `true` if a value of type `from` can be assigned to a location of type `to`.
pub fn types_compatible_core(from: &LegacyType, to: &LegacyType) -> bool {
    if from == to {
        return true;
    }

    // Check if from can widen to to
    if from.can_widen_to(to) {
        return true;
    }

    // Allow numeric coercion (kept for backwards compatibility)
    if from.is_integer() && *to == LegacyType::Primitive(PrimitiveType::I64) {
        return true;
    }
    if from.is_numeric() && *to == LegacyType::Primitive(PrimitiveType::F64) {
        return true;
    }

    // Check if assigning to a union that contains the from type
    if let LegacyType::Union(variants) = to {
        // Direct containment
        if variants.contains(from) {
            return true;
        }
        // Also check if from can widen into a union variant
        for variant in variants.iter() {
            if from.can_widen_to(variant) {
                return true;
            }
        }
    }

    // Nil is compatible with any optional (union containing Nil)
    if *from == LegacyType::Nil && to.is_optional() {
        return true;
    }

    // Error type is compatible with anything (for error recovery)
    if from.is_invalid() || to.is_invalid() {
        return true;
    }

    // Class compatibility: compare by type_def_id and type_args
    // Class types are invariant, so compatibility = equality (now uses type_args_id)
    if let (
        LegacyType::Nominal(NominalType::Class(from_class)),
        LegacyType::Nominal(NominalType::Class(to_class)),
    ) = (from, to)
        && from_class == to_class
    {
        return true;
    }

    // Record compatibility: compare by type_def_id and type_args
    // Record types are invariant, so compatibility = equality (now uses type_args_id)
    if let (
        LegacyType::Nominal(NominalType::Record(from_rec)),
        LegacyType::Nominal(NominalType::Record(to_rec)),
    ) = (from, to)
        && from_rec == to_rec
    {
        return true;
    }

    // Interface<->GenericInstance compatibility is handled by types_compatible() in analyzer/methods/compatibility.rs
    // which has access to entity_registry for TypeDefId<->NameId conversion.
    // Direct comparison here would require InterfaceType.type_def_id == GenericInstance.def (NameId),
    // but these are different ID types. The full compatibility check handles interface subtyping.

    // Tuple compatibility: same length and each element is compatible
    if let (LegacyType::Tuple(from_elems), LegacyType::Tuple(to_elems)) = (from, to)
        && from_elems.len() == to_elems.len()
    {
        return from_elems
            .iter()
            .zip(to_elems.iter())
            .all(|(f, t)| types_compatible_core(f, t));
    }

    // Fixed array compatibility: same element type and same size
    if let (
        LegacyType::FixedArray {
            element: from_elem,
            size: from_size,
        },
        LegacyType::FixedArray {
            element: to_elem,
            size: to_size,
        },
    ) = (from, to)
        && from_size == to_size
    {
        return types_compatible_core(from_elem, to_elem);
    }

    false
}

/// Check if two types are compatible using TypeId (no LegacyType conversion).
///
/// This is the TypeId-based version of `types_compatible_core` for Phase 3 migration.
/// It performs the same compatibility checks but operates directly on TypeId and the arena.
#[allow(unused)] // Phase 3 infrastructure - callers will migrate
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

/// Check if a function type is compatible with a functional interface.
///
/// This is used by the analyzer to extend type compatibility checking to include
/// function-to-interface compatibility. The `interface_fn` parameter should be
/// the function signature extracted from the interface definition.
///
/// Note: This delegates to `FunctionType::is_compatible_with_interface`.
/// Consider using that method directly on FunctionType instances.
pub fn function_compatible_with_interface(
    fn_type: &FunctionType,
    interface_fn: &FunctionType,
) -> bool {
    fn_type.is_compatible_with_interface(interface_fn)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_fits_signed() {
        // i8 range: -128 to 127
        assert!(literal_fits(0, &LegacyType::Primitive(PrimitiveType::I8)));
        assert!(literal_fits(127, &LegacyType::Primitive(PrimitiveType::I8)));
        assert!(literal_fits(
            -128,
            &LegacyType::Primitive(PrimitiveType::I8)
        ));
        assert!(!literal_fits(
            128,
            &LegacyType::Primitive(PrimitiveType::I8)
        ));
        assert!(!literal_fits(
            -129,
            &LegacyType::Primitive(PrimitiveType::I8)
        ));

        // i16 range
        assert!(literal_fits(
            32767,
            &LegacyType::Primitive(PrimitiveType::I16)
        ));
        assert!(!literal_fits(
            32768,
            &LegacyType::Primitive(PrimitiveType::I16)
        ));

        // i32 range
        assert!(literal_fits(
            2147483647,
            &LegacyType::Primitive(PrimitiveType::I32)
        ));
        assert!(!literal_fits(
            2147483648,
            &LegacyType::Primitive(PrimitiveType::I32)
        ));

        // i64 always fits
        assert!(literal_fits(
            i64::MAX,
            &LegacyType::Primitive(PrimitiveType::I64)
        ));
        assert!(literal_fits(
            i64::MIN,
            &LegacyType::Primitive(PrimitiveType::I64)
        ));
    }

    #[test]
    fn test_literal_fits_unsigned() {
        // u8 range: 0 to 255
        assert!(literal_fits(0, &LegacyType::Primitive(PrimitiveType::U8)));
        assert!(literal_fits(255, &LegacyType::Primitive(PrimitiveType::U8)));
        assert!(!literal_fits(
            256,
            &LegacyType::Primitive(PrimitiveType::U8)
        ));
        assert!(!literal_fits(-1, &LegacyType::Primitive(PrimitiveType::U8)));

        // u16 range
        assert!(literal_fits(
            65535,
            &LegacyType::Primitive(PrimitiveType::U16)
        ));
        assert!(!literal_fits(
            65536,
            &LegacyType::Primitive(PrimitiveType::U16)
        ));

        // u32 range
        assert!(literal_fits(
            4294967295,
            &LegacyType::Primitive(PrimitiveType::U32)
        ));
        assert!(!literal_fits(
            4294967296,
            &LegacyType::Primitive(PrimitiveType::U32)
        ));

        // u64 accepts all positive i64 values
        assert!(literal_fits(0, &LegacyType::Primitive(PrimitiveType::U64)));
        assert!(literal_fits(
            i64::MAX,
            &LegacyType::Primitive(PrimitiveType::U64)
        ));
        assert!(!literal_fits(
            -1,
            &LegacyType::Primitive(PrimitiveType::U64)
        ));
    }

    #[test]
    fn test_literal_fits_float() {
        assert!(literal_fits(0, &LegacyType::Primitive(PrimitiveType::F32)));
        assert!(literal_fits(
            i64::MAX,
            &LegacyType::Primitive(PrimitiveType::F64)
        ));
    }

    #[test]
    fn test_literal_fits_union() {
        let union_ty = LegacyType::Union(
            vec![
                LegacyType::Primitive(PrimitiveType::I8),
                LegacyType::Primitive(PrimitiveType::I32),
            ]
            .into(),
        );
        assert!(literal_fits(100, &union_ty)); // Fits in i8
        assert!(literal_fits(1000, &union_ty)); // Fits in i32
        assert!(!literal_fits(i64::MAX, &union_ty)); // Doesn't fit in either
    }

    #[test]
    fn test_types_compatible_same() {
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::I32),
            &LegacyType::Primitive(PrimitiveType::I32)
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::String),
            &LegacyType::Primitive(PrimitiveType::String)
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::Bool),
            &LegacyType::Primitive(PrimitiveType::Bool)
        ));
    }

    #[test]
    fn test_types_compatible_widening() {
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::I32),
            &LegacyType::Primitive(PrimitiveType::I64)
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::F32),
            &LegacyType::Primitive(PrimitiveType::F64)
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::U8),
            &LegacyType::Primitive(PrimitiveType::I16)
        ));
    }

    #[test]
    fn test_types_compatible_union() {
        let union_ty = LegacyType::Union(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::String),
            ]
            .into(),
        );
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::I32),
            &union_ty
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::String),
            &union_ty
        ));
        assert!(!types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::Bool),
            &union_ty
        ));
    }

    #[test]
    fn test_types_compatible_optional() {
        let optional = LegacyType::optional(LegacyType::Primitive(PrimitiveType::I32));
        assert!(types_compatible_core(&LegacyType::Nil, &optional));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::I32),
            &optional
        ));
    }

    #[test]
    fn test_types_compatible_error() {
        let err = LegacyType::invalid("test");
        assert!(types_compatible_core(
            &err,
            &LegacyType::Primitive(PrimitiveType::I32)
        ));
        assert!(types_compatible_core(
            &LegacyType::Primitive(PrimitiveType::I32),
            &err
        ));
    }

    #[test]
    fn test_function_compatible_with_interface() {
        let fn_type = FunctionType {
            params: vec![LegacyType::Primitive(PrimitiveType::I32)].into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::Bool)),
            is_closure: false,
            params_id: None,
            return_type_id: None,
        };

        let iface_fn = FunctionType {
            params: vec![LegacyType::Primitive(PrimitiveType::I32)].into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::Bool)),
            is_closure: true,
            params_id: None,
            return_type_id: None,
        };

        assert!(function_compatible_with_interface(&fn_type, &iface_fn));

        // Incompatible return type
        let iface_fn_bad = FunctionType {
            params: vec![LegacyType::Primitive(PrimitiveType::I32)].into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::String)),
            is_closure: true,
            params_id: None,
            return_type_id: None,
        };
        assert!(!function_compatible_with_interface(&fn_type, &iface_fn_bad));

        // Different param count
        let iface_fn_wrong_params = FunctionType {
            params: vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::I32),
            ]
            .into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::Bool)),
            is_closure: true,
            params_id: None,
            return_type_id: None,
        };
        assert!(!function_compatible_with_interface(
            &fn_type,
            &iface_fn_wrong_params
        ));
    }

    #[test]
    fn test_types_compatible_tuple() {
        let tuple1 = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::String),
            ]
            .into(),
        );
        let tuple2 = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::String),
            ]
            .into(),
        );
        let tuple3 = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::Bool),
            ]
            .into(),
        ); // Different element type
        let tuple4 = LegacyType::Tuple(vec![LegacyType::Primitive(PrimitiveType::I32)].into()); // Different length

        assert!(types_compatible_core(&tuple1, &tuple2));
        assert!(!types_compatible_core(&tuple1, &tuple3));
        assert!(!types_compatible_core(&tuple1, &tuple4));
    }

    #[test]
    fn test_types_compatible_tuple_widening() {
        // Tuple with widening: [i32, f32] compatible with [i64, f64]
        let narrow = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::F32),
            ]
            .into(),
        );
        let wide = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I64),
                LegacyType::Primitive(PrimitiveType::F64),
            ]
            .into(),
        );
        assert!(types_compatible_core(&narrow, &wide));
    }

    #[test]
    fn test_types_compatible_fixed_array() {
        let arr1 = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I32)),
            size: 10,
        };
        let arr2 = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I32)),
            size: 10,
        };
        let arr3 = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I32)),
            size: 5,
        }; // Different size
        let arr4 = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::String)),
            size: 10,
        }; // Different element type

        assert!(types_compatible_core(&arr1, &arr2));
        assert!(!types_compatible_core(&arr1, &arr3));
        assert!(!types_compatible_core(&arr1, &arr4));
    }

    #[test]
    fn test_types_compatible_fixed_array_widening() {
        // Fixed array with widening: [i32; 5] compatible with [i64; 5]
        let narrow = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I32)),
            size: 5,
        };
        let wide = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I64)),
            size: 5,
        };
        assert!(types_compatible_core(&narrow, &wide));
    }
}

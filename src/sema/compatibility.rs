// src/sema/compatibility.rs
//
// Type compatibility checking functions.
// These are pure functions that determine if types are compatible for assignment.

use super::types::{FunctionType, Type};

/// Check if an integer literal value fits within a type's range
pub fn literal_fits(value: i64, target: &Type) -> bool {
    match target {
        Type::I8 => value >= i8::MIN as i64 && value <= i8::MAX as i64,
        Type::I16 => value >= i16::MIN as i64 && value <= i16::MAX as i64,
        Type::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
        Type::I64 => true,
        Type::I128 => true, // i64 always fits in i128
        Type::U8 => value >= 0 && value <= u8::MAX as i64,
        Type::U16 => value >= 0 && value <= u16::MAX as i64,
        Type::U32 => value >= 0 && value <= u32::MAX as i64,
        Type::U64 => value >= 0,       // i64 positive values fit
        Type::F32 | Type::F64 => true, // Integers can become floats
        // For unions, check if literal fits any numeric variant
        Type::Union(variants) => variants.iter().any(|v| literal_fits(value, v)),
        _ => false,
    }
}

/// Check if two types are compatible (assignable) without considering interfaces.
///
/// This function handles all type compatibility checks except for function-to-interface
/// compatibility, which requires access to the interface registry.
///
/// Returns `true` if a value of type `from` can be assigned to a location of type `to`.
pub fn types_compatible_core(from: &Type, to: &Type) -> bool {
    if from == to {
        return true;
    }

    // Check if from can widen to to
    if from.can_widen_to(to) {
        return true;
    }

    // Allow numeric coercion (kept for backwards compatibility)
    if from.is_integer() && to == &Type::I64 {
        return true;
    }
    if from.is_numeric() && to == &Type::F64 {
        return true;
    }

    // Check if assigning to a union that contains the from type
    if let Type::Union(variants) = to {
        // Direct containment
        if variants.contains(from) {
            return true;
        }
        // Also check if from can widen into a union variant
        for variant in variants {
            if from.can_widen_to(variant) {
                return true;
            }
        }
    }

    // Nil is compatible with any optional (union containing Nil)
    if *from == Type::Nil && to.is_optional() {
        return true;
    }

    // Error type is compatible with anything (for error recovery)
    if from.is_invalid() || to.is_invalid() {
        return true;
    }

    // Interface is compatible with GenericInstance (and vice versa) when they have same def and args
    // This handles cases like Iterator<i64> (Interface) matching Iterator<T> instantiated as Iterator<i64> (GenericInstance)
    match (from, to) {
        (Type::Interface(iface), Type::GenericInstance { def, args }) => {
            if iface.name_id == *def && iface.type_args == *args {
                return true;
            }
        }
        (Type::GenericInstance { def, args }, Type::Interface(iface)) => {
            if *def == iface.name_id && *args == iface.type_args {
                return true;
            }
        }
        _ => {}
    }

    // Tuple compatibility: same length and each element is compatible
    if let (Type::Tuple(from_elems), Type::Tuple(to_elems)) = (from, to)
        && from_elems.len() == to_elems.len()
    {
        return from_elems
            .iter()
            .zip(to_elems.iter())
            .all(|(f, t)| types_compatible_core(f, t));
    }

    // Fixed array compatibility: same element type and same size
    if let (
        Type::FixedArray {
            element: from_elem,
            size: from_size,
        },
        Type::FixedArray {
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

/// Check if a function type is compatible with a functional interface.
///
/// This is used by the analyzer to extend type compatibility checking to include
/// function-to-interface compatibility. The `interface_fn` parameter should be
/// the function signature extracted from the interface definition.
pub fn function_compatible_with_interface(
    fn_type: &FunctionType,
    interface_fn: &FunctionType,
) -> bool {
    if fn_type.params.len() != interface_fn.params.len() {
        return false;
    }

    let params_match = fn_type
        .params
        .iter()
        .zip(interface_fn.params.iter())
        .all(|(fp, ip)| types_compatible_core(fp, ip));

    let return_matches = types_compatible_core(&fn_type.return_type, &interface_fn.return_type);

    params_match && return_matches
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literal_fits_signed() {
        // i8 range: -128 to 127
        assert!(literal_fits(0, &Type::I8));
        assert!(literal_fits(127, &Type::I8));
        assert!(literal_fits(-128, &Type::I8));
        assert!(!literal_fits(128, &Type::I8));
        assert!(!literal_fits(-129, &Type::I8));

        // i16 range
        assert!(literal_fits(32767, &Type::I16));
        assert!(!literal_fits(32768, &Type::I16));

        // i32 range
        assert!(literal_fits(2147483647, &Type::I32));
        assert!(!literal_fits(2147483648, &Type::I32));

        // i64 always fits
        assert!(literal_fits(i64::MAX, &Type::I64));
        assert!(literal_fits(i64::MIN, &Type::I64));
    }

    #[test]
    fn test_literal_fits_unsigned() {
        // u8 range: 0 to 255
        assert!(literal_fits(0, &Type::U8));
        assert!(literal_fits(255, &Type::U8));
        assert!(!literal_fits(256, &Type::U8));
        assert!(!literal_fits(-1, &Type::U8));

        // u16 range
        assert!(literal_fits(65535, &Type::U16));
        assert!(!literal_fits(65536, &Type::U16));

        // u32 range
        assert!(literal_fits(4294967295, &Type::U32));
        assert!(!literal_fits(4294967296, &Type::U32));

        // u64 accepts all positive i64 values
        assert!(literal_fits(0, &Type::U64));
        assert!(literal_fits(i64::MAX, &Type::U64));
        assert!(!literal_fits(-1, &Type::U64));
    }

    #[test]
    fn test_literal_fits_float() {
        assert!(literal_fits(0, &Type::F32));
        assert!(literal_fits(i64::MAX, &Type::F64));
    }

    #[test]
    fn test_literal_fits_union() {
        let union_ty = Type::Union(vec![Type::I8, Type::I32]);
        assert!(literal_fits(100, &union_ty)); // Fits in i8
        assert!(literal_fits(1000, &union_ty)); // Fits in i32
        assert!(!literal_fits(i64::MAX, &union_ty)); // Doesn't fit in either
    }

    #[test]
    fn test_types_compatible_same() {
        assert!(types_compatible_core(&Type::I32, &Type::I32));
        assert!(types_compatible_core(&Type::String, &Type::String));
        assert!(types_compatible_core(&Type::Bool, &Type::Bool));
    }

    #[test]
    fn test_types_compatible_widening() {
        assert!(types_compatible_core(&Type::I32, &Type::I64));
        assert!(types_compatible_core(&Type::F32, &Type::F64));
        assert!(types_compatible_core(&Type::U8, &Type::I16));
    }

    #[test]
    fn test_types_compatible_union() {
        let union_ty = Type::Union(vec![Type::I32, Type::String]);
        assert!(types_compatible_core(&Type::I32, &union_ty));
        assert!(types_compatible_core(&Type::String, &union_ty));
        assert!(!types_compatible_core(&Type::Bool, &union_ty));
    }

    #[test]
    fn test_types_compatible_optional() {
        let optional = Type::optional(Type::I32);
        assert!(types_compatible_core(&Type::Nil, &optional));
        assert!(types_compatible_core(&Type::I32, &optional));
    }

    #[test]
    fn test_types_compatible_error() {
        let err = Type::invalid("test");
        assert!(types_compatible_core(&err, &Type::I32));
        assert!(types_compatible_core(&Type::I32, &err));
    }

    #[test]
    fn test_function_compatible_with_interface() {
        let fn_type = FunctionType {
            params: vec![Type::I32],
            return_type: Box::new(Type::Bool),
            is_closure: false,
        };

        let iface_fn = FunctionType {
            params: vec![Type::I32],
            return_type: Box::new(Type::Bool),
            is_closure: true,
        };

        assert!(function_compatible_with_interface(&fn_type, &iface_fn));

        // Incompatible return type
        let iface_fn_bad = FunctionType {
            params: vec![Type::I32],
            return_type: Box::new(Type::String),
            is_closure: true,
        };
        assert!(!function_compatible_with_interface(&fn_type, &iface_fn_bad));

        // Different param count
        let iface_fn_wrong_params = FunctionType {
            params: vec![Type::I32, Type::I32],
            return_type: Box::new(Type::Bool),
            is_closure: true,
        };
        assert!(!function_compatible_with_interface(
            &fn_type,
            &iface_fn_wrong_params
        ));
    }

    #[test]
    fn test_types_compatible_tuple() {
        let tuple1 = Type::Tuple(vec![Type::I32, Type::String]);
        let tuple2 = Type::Tuple(vec![Type::I32, Type::String]);
        let tuple3 = Type::Tuple(vec![Type::I32, Type::Bool]); // Different element type
        let tuple4 = Type::Tuple(vec![Type::I32]); // Different length

        assert!(types_compatible_core(&tuple1, &tuple2));
        assert!(!types_compatible_core(&tuple1, &tuple3));
        assert!(!types_compatible_core(&tuple1, &tuple4));
    }

    #[test]
    fn test_types_compatible_tuple_widening() {
        // Tuple with widening: [i32, f32] compatible with [i64, f64]
        let narrow = Type::Tuple(vec![Type::I32, Type::F32]);
        let wide = Type::Tuple(vec![Type::I64, Type::F64]);
        assert!(types_compatible_core(&narrow, &wide));
    }

    #[test]
    fn test_types_compatible_fixed_array() {
        let arr1 = Type::FixedArray {
            element: Box::new(Type::I32),
            size: 10,
        };
        let arr2 = Type::FixedArray {
            element: Box::new(Type::I32),
            size: 10,
        };
        let arr3 = Type::FixedArray {
            element: Box::new(Type::I32),
            size: 5,
        }; // Different size
        let arr4 = Type::FixedArray {
            element: Box::new(Type::String),
            size: 10,
        }; // Different element type

        assert!(types_compatible_core(&arr1, &arr2));
        assert!(!types_compatible_core(&arr1, &arr3));
        assert!(!types_compatible_core(&arr1, &arr4));
    }

    #[test]
    fn test_types_compatible_fixed_array_widening() {
        // Fixed array with widening: [i32; 5] compatible with [i64; 5]
        let narrow = Type::FixedArray {
            element: Box::new(Type::I32),
            size: 5,
        };
        let wide = Type::FixedArray {
            element: Box::new(Type::I64),
            size: 5,
        };
        assert!(types_compatible_core(&narrow, &wide));
    }
}

// src/runtime/stdlib/intrinsics.rs
//! Native intrinsic functions for primitive types.

use crate::runtime::RcString;
use crate::runtime::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:intrinsics native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // i64_equals: (i64, i64) -> bool
    m.register(
        "i64_equals",
        i64_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    // i64_compare: (i64, i64) -> i32
    m.register(
        "i64_compare",
        i64_compare as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I32,
        },
    );

    // i64_to_string: (i64) -> string
    m.register(
        "i64_to_string",
        i64_to_string as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::String,
        },
    );

    // i32 functions
    m.register(
        "i32_equals",
        i32_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::I32, NativeType::I32],
            return_type: NativeType::Bool,
        },
    );
    m.register(
        "i32_compare",
        i32_compare as *const u8,
        NativeSignature {
            params: vec![NativeType::I32, NativeType::I32],
            return_type: NativeType::I32,
        },
    );
    m.register(
        "i32_to_string",
        i32_to_string as *const u8,
        NativeSignature {
            params: vec![NativeType::I32],
            return_type: NativeType::String,
        },
    );

    // f64 functions
    m.register(
        "f64_equals",
        f64_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::F64, NativeType::F64],
            return_type: NativeType::Bool,
        },
    );
    m.register(
        "f64_compare",
        f64_compare as *const u8,
        NativeSignature {
            params: vec![NativeType::F64, NativeType::F64],
            return_type: NativeType::I32,
        },
    );
    m.register(
        "f64_to_string",
        f64_to_string as *const u8,
        NativeSignature {
            params: vec![NativeType::F64],
            return_type: NativeType::String,
        },
    );

    // bool functions
    m.register(
        "bool_equals",
        bool_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::Bool, NativeType::Bool],
            return_type: NativeType::Bool,
        },
    );
    m.register(
        "bool_to_string",
        bool_to_string as *const u8,
        NativeSignature {
            params: vec![NativeType::Bool],
            return_type: NativeType::String,
        },
    );

    m
}

// =============================================================================
// i64 functions
// =============================================================================

/// Check if two i64 values are equal
#[unsafe(no_mangle)]
pub extern "C" fn i64_equals(a: i64, b: i64) -> i8 {
    if a == b { 1 } else { 0 }
}

/// Compare two i64 values, returns -1, 0, or 1
#[unsafe(no_mangle)]
pub extern "C" fn i64_compare(a: i64, b: i64) -> i32 {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

/// Convert an i64 to a string
#[unsafe(no_mangle)]
pub extern "C" fn i64_to_string(n: i64) -> *const RcString {
    RcString::new(&n.to_string())
}

// =============================================================================
// i32 functions
// =============================================================================

/// Check if two i32 values are equal
#[unsafe(no_mangle)]
pub extern "C" fn i32_equals(a: i32, b: i32) -> i8 {
    if a == b { 1 } else { 0 }
}

/// Compare two i32 values, returns -1, 0, or 1
#[unsafe(no_mangle)]
pub extern "C" fn i32_compare(a: i32, b: i32) -> i32 {
    match a.cmp(&b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

/// Convert an i32 to a string
#[unsafe(no_mangle)]
pub extern "C" fn i32_to_string(n: i32) -> *const RcString {
    RcString::new(&n.to_string())
}

// =============================================================================
// f64 functions
// =============================================================================

/// Check if two f64 values are equal
#[unsafe(no_mangle)]
pub extern "C" fn f64_equals(a: f64, b: f64) -> i8 {
    if a == b { 1 } else { 0 }
}

/// Compare two f64 values, returns -1, 0, or 1 (NaN returns 0)
#[unsafe(no_mangle)]
pub extern "C" fn f64_compare(a: f64, b: f64) -> i32 {
    match a.partial_cmp(&b) {
        Some(std::cmp::Ordering::Less) => -1,
        Some(std::cmp::Ordering::Equal) => 0,
        Some(std::cmp::Ordering::Greater) => 1,
        None => 0, // NaN comparison returns 0
    }
}

/// Convert an f64 to a string
#[unsafe(no_mangle)]
pub extern "C" fn f64_to_string(n: f64) -> *const RcString {
    RcString::new(&n.to_string())
}

// =============================================================================
// bool functions
// =============================================================================

/// Check if two bool values are equal
#[unsafe(no_mangle)]
pub extern "C" fn bool_equals(a: i8, b: i8) -> i8 {
    if a == b { 1 } else { 0 }
}

/// Convert a bool to a string
#[unsafe(no_mangle)]
pub extern "C" fn bool_to_string(b: i8) -> *const RcString {
    RcString::new(if b != 0 { "true" } else { "false" })
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // i64 function tests
    // =========================================================================

    #[test]
    fn test_i64_equals() {
        assert_eq!(i64_equals(42, 42), 1);
        assert_eq!(i64_equals(42, 43), 0);
        assert_eq!(i64_equals(-1, -1), 1);
        assert_eq!(i64_equals(0, 0), 1);
    }

    #[test]
    fn test_i64_compare() {
        assert_eq!(i64_compare(1, 2), -1);
        assert_eq!(i64_compare(2, 2), 0);
        assert_eq!(i64_compare(3, 2), 1);
        assert_eq!(i64_compare(-5, 5), -1);
        assert_eq!(i64_compare(i64::MAX, i64::MIN), 1);
    }

    #[test]
    fn test_i64_to_string() {
        let s = i64_to_string(42);
        unsafe {
            assert_eq!((*s).as_str(), "42");
            RcString::dec_ref(s as *mut RcString);
        }

        let s = i64_to_string(-123);
        unsafe {
            assert_eq!((*s).as_str(), "-123");
            RcString::dec_ref(s as *mut RcString);
        }
    }

    // =========================================================================
    // i32 function tests
    // =========================================================================

    #[test]
    fn test_i32_equals() {
        assert_eq!(i32_equals(42, 42), 1);
        assert_eq!(i32_equals(42, 43), 0);
    }

    #[test]
    fn test_i32_compare() {
        assert_eq!(i32_compare(1, 2), -1);
        assert_eq!(i32_compare(2, 2), 0);
        assert_eq!(i32_compare(3, 2), 1);
    }

    #[test]
    fn test_i32_to_string() {
        let s = i32_to_string(42);
        unsafe {
            assert_eq!((*s).as_str(), "42");
            RcString::dec_ref(s as *mut RcString);
        }
    }

    // =========================================================================
    // f64 function tests
    // =========================================================================

    #[test]
    fn test_f64_equals() {
        assert_eq!(f64_equals(3.14, 3.14), 1);
        assert_eq!(f64_equals(3.14, 3.15), 0);
        assert_eq!(f64_equals(0.0, -0.0), 1); // IEEE 754: +0 == -0
    }

    #[test]
    fn test_f64_compare() {
        assert_eq!(f64_compare(1.0, 2.0), -1);
        assert_eq!(f64_compare(2.0, 2.0), 0);
        assert_eq!(f64_compare(3.0, 2.0), 1);
    }

    #[test]
    fn test_f64_compare_nan() {
        let nan = f64::NAN;
        assert_eq!(f64_compare(nan, 1.0), 0);
        assert_eq!(f64_compare(1.0, nan), 0);
        assert_eq!(f64_compare(nan, nan), 0);
    }

    #[test]
    fn test_f64_to_string() {
        let s = f64_to_string(3.14);
        unsafe {
            assert_eq!((*s).as_str(), "3.14");
            RcString::dec_ref(s as *mut RcString);
        }
    }

    // =========================================================================
    // bool function tests
    // =========================================================================

    #[test]
    fn test_bool_equals() {
        assert_eq!(bool_equals(1, 1), 1);
        assert_eq!(bool_equals(0, 0), 1);
        assert_eq!(bool_equals(1, 0), 0);
        assert_eq!(bool_equals(0, 1), 0);
    }

    #[test]
    fn test_bool_to_string() {
        unsafe {
            let t = bool_to_string(1);
            assert_eq!((*t).as_str(), "true");
            RcString::dec_ref(t as *mut RcString);

            let f = bool_to_string(0);
            assert_eq!((*f).as_str(), "false");
            RcString::dec_ref(f as *mut RcString);
        }
    }

    // =========================================================================
    // Module registration tests
    // =========================================================================

    #[test]
    fn test_module_registration() {
        let m = module();

        // Verify all functions are registered
        assert!(m.get("i64_equals").is_some());
        assert!(m.get("i64_compare").is_some());
        assert!(m.get("i64_to_string").is_some());
        assert!(m.get("i32_equals").is_some());
        assert!(m.get("i32_compare").is_some());
        assert!(m.get("i32_to_string").is_some());
        assert!(m.get("f64_equals").is_some());
        assert!(m.get("f64_compare").is_some());
        assert!(m.get("f64_to_string").is_some());
        assert!(m.get("bool_equals").is_some());
        assert!(m.get("bool_to_string").is_some());

        // Verify signatures
        let i64_eq = m.get("i64_equals").unwrap();
        assert_eq!(i64_eq.signature.params.len(), 2);
        assert_eq!(i64_eq.signature.params[0], NativeType::I64);
        assert_eq!(i64_eq.signature.params[1], NativeType::I64);
        assert_eq!(i64_eq.signature.return_type, NativeType::Bool);

        let i64_cmp = m.get("i64_compare").unwrap();
        assert_eq!(i64_cmp.signature.params.len(), 2);
        assert_eq!(i64_cmp.signature.return_type, NativeType::I32);

        let i64_str = m.get("i64_to_string").unwrap();
        assert_eq!(i64_str.signature.params.len(), 1);
        assert_eq!(i64_str.signature.return_type, NativeType::String);
    }
}

// src/runtime/stdlib/intrinsics.rs
//! Native intrinsic functions for primitive types.

use crate::runtime::RcString;
use crate::runtime::iterator;
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

    // i64_hash: (i64) -> i64 (Thomas Wang hash)
    m.register(
        "i64_hash",
        i64_hash as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
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
    m.register(
        "i32_hash",
        i32_hash as *const u8,
        NativeSignature {
            params: vec![NativeType::I32],
            return_type: NativeType::I64,
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

    // Iterator intrinsics
    m.register(
        "array_iter",
        iterator::vole_array_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::Array(Box::new(NativeType::I64))],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_map",
        iterator::vole_map_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_next",
        iterator::vole_iter_next as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_filter",
        iterator::vole_filter_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_take",
        iterator::vole_take_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_skip",
        iterator::vole_skip_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_collect",
        iterator::vole_array_iter_collect as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Array(Box::new(NativeType::I64)),
        },
    );
    m.register(
        "iter_count",
        iterator::vole_iter_count as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_sum",
        iterator::vole_iter_sum as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_for_each",
        iterator::vole_iter_for_each as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Nil,
        },
    );
    m.register(
        "iter_reduce",
        iterator::vole_iter_reduce as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_first",
        iterator::vole_iter_first as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64, // Returns pointer to optional
        },
    );
    m.register(
        "iter_last",
        iterator::vole_iter_last as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64, // Returns pointer to optional
        },
    );
    m.register(
        "iter_nth",
        iterator::vole_iter_nth as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64, // Returns pointer to optional
        },
    );
    m.register(
        "iter_find",
        iterator::vole_iter_find as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64, // Returns pointer to optional
        },
    );
    m.register(
        "iter_any",
        iterator::vole_iter_any as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );
    m.register(
        "iter_all",
        iterator::vole_iter_all as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Bool,
        },
    );
    m.register(
        "iter_chain",
        iterator::vole_chain_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_flatten",
        iterator::vole_flatten_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_flat_map",
        iterator::vole_flat_map_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_reverse",
        iterator::vole_reverse_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_sorted",
        iterator::vole_sorted_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_unique",
        iterator::vole_unique_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_chunks",
        iterator::vole_chunks_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );
    m.register(
        "iter_windows",
        iterator::vole_windows_iter as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
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

/// Thomas Wang's 64-bit integer hash function (from V8/Wren)
/// Provides excellent bit mixing for hash table distribution
#[inline]
fn hash_bits(mut hash: u64) -> i64 {
    hash = (!hash).wrapping_add(hash << 18);
    hash ^= hash >> 31;
    hash = hash.wrapping_mul(21);
    hash ^= hash >> 11;
    hash = hash.wrapping_add(hash << 6);
    hash ^= hash >> 22;
    hash as i64
}

/// Hash an i64 value using Thomas Wang's hash
#[unsafe(no_mangle)]
pub extern "C" fn i64_hash(n: i64) -> i64 {
    hash_bits(n as u64)
}

/// Hash an i32 value using Thomas Wang's hash
#[unsafe(no_mangle)]
pub extern "C" fn i32_hash(n: i32) -> i64 {
    hash_bits(n as u64)
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
    // Hash function tests (Thomas Wang)
    // =========================================================================

    #[test]
    fn test_i64_hash_distribution() {
        // Sequential integers should produce different hashes
        let h0 = i64_hash(0);
        let h1 = i64_hash(1);
        let h2 = i64_hash(2);
        let h3 = i64_hash(3);

        // All hashes should be different
        assert_ne!(h0, h1);
        assert_ne!(h1, h2);
        assert_ne!(h2, h3);
        assert_ne!(h0, h2);

        // Hashes should be well-distributed (not sequential)
        assert_ne!(h1 - h0, h2 - h1); // Not linear
    }

    #[test]
    fn test_i64_hash_consistency() {
        // Same input should always produce same hash
        assert_eq!(i64_hash(42), i64_hash(42));
        assert_eq!(i64_hash(-1), i64_hash(-1));
        assert_eq!(i64_hash(i64::MAX), i64_hash(i64::MAX));
    }

    #[test]
    fn test_i32_hash_distribution() {
        let h0 = i32_hash(0);
        let h1 = i32_hash(1);
        let h2 = i32_hash(2);

        assert_ne!(h0, h1);
        assert_ne!(h1, h2);
        assert_ne!(h0, h2);
    }

    #[test]
    fn test_hash_bits_known_values() {
        // Verify the hash function produces expected mixing
        // Zero should not hash to zero (good mixing)
        assert_ne!(i64_hash(0), 0);

        // Negative numbers should work
        let h_neg = i64_hash(-1);
        let h_pos = i64_hash(1);
        assert_ne!(h_neg, h_pos);
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
        assert!(m.get("i32_hash").is_some());
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

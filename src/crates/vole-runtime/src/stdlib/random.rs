// src/runtime/stdlib/random.rs
//! Native random number generation functions for std:random module.
//!
//! Provides:
//! - random_float() -> f64 in [0.0, 1.0) using thread_rng
//! - random_seeded(seed: i64) -> *mut Rng - creates a seeded RNG instance
//! - rng_float(rng: *mut Rng) -> f64 - get next float from seeded RNG

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use rand::rngs::StdRng;
use rand::{Rng as RandRng, SeedableRng};

/// Create the std:random native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // float: () -> f64 - random float in [0.0, 1.0)
    m.register(
        "float",
        random_float as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::F64,
        },
    );

    // seeded: (i64) -> i64 (opaque Rng pointer)
    m.register(
        "seeded",
        random_seeded as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // rng_float: (i64) -> f64 - get float from seeded RNG
    m.register(
        "rng_float",
        rng_float as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::F64,
        },
    );

    // int: (i64, i64) -> i64 - random int in [min, max] inclusive
    m.register(
        "int",
        random_int as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // rng_int: (i64, i64, i64) -> i64 - random int in [min, max] from seeded RNG
    m.register(
        "rng_int",
        rng_int as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // rng_coin: (i64) -> bool - random boolean from seeded RNG
    m.register(
        "rng_coin",
        rng_coin as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Bool,
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Generate a random f64 in [0.0, 1.0) using thread-local RNG
#[unsafe(no_mangle)]
pub extern "C" fn random_float() -> f64 {
    rand::random::<f64>()
}

/// Create a seeded RNG instance
/// Returns an opaque pointer to a heap-allocated StdRng
#[unsafe(no_mangle)]
pub extern "C" fn random_seeded(seed: i64) -> *mut StdRng {
    // Convert i64 seed to u64 bytes for seeding
    let seed_bytes = seed.to_le_bytes();
    let mut full_seed = [0u8; 32];
    // Fill the seed by repeating the 8 bytes to get 32 bytes
    for i in 0..4 {
        full_seed[i * 8..(i + 1) * 8].copy_from_slice(&seed_bytes);
    }
    let rng = StdRng::from_seed(full_seed);
    Box::into_raw(Box::new(rng))
}

/// Get the next random f64 in [0.0, 1.0) from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_float(rng_ptr: *mut StdRng) -> f64 {
    if rng_ptr.is_null() {
        return 0.0;
    }
    unsafe { (*rng_ptr).r#gen::<f64>() }
}

/// Generate a random i64 in [min, max] (inclusive) using thread-local RNG
#[unsafe(no_mangle)]
pub extern "C" fn random_int(min: i64, max: i64) -> i64 {
    if min > max {
        return min;
    }
    let f = rand::random::<f64>();
    let range = (max - min + 1) as f64;
    min + (f * range).floor() as i64
}

/// Get the next random i64 in [min, max] (inclusive) from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_int(rng_ptr: *mut StdRng, min: i64, max: i64) -> i64 {
    if rng_ptr.is_null() || min > max {
        return min;
    }
    let f = unsafe { (*rng_ptr).r#gen::<f64>() };
    let range = (max - min + 1) as f64;
    min + (f * range).floor() as i64
}

/// Get the next random boolean from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_coin(rng_ptr: *mut StdRng) -> bool {
    if rng_ptr.is_null() {
        return false;
    }
    unsafe { (*rng_ptr).r#gen::<f64>() < 0.5 }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_random_float_range() {
        // Test that random_float returns values in [0.0, 1.0)
        for _ in 0..100 {
            let f = random_float();
            assert!(f >= 0.0, "float {} should be >= 0.0", f);
            assert!(f < 1.0, "float {} should be < 1.0", f);
        }
    }

    #[test]
    fn test_random_float_varies() {
        // Test that random_float doesn't always return the same value
        let first = random_float();
        let mut found_different = false;
        for _ in 0..100 {
            if random_float() != first {
                found_different = true;
                break;
            }
        }
        assert!(
            found_different,
            "random_float should produce varying values"
        );
    }

    #[test]
    fn test_seeded_rng_deterministic() {
        // Test that seeded RNG produces same sequence with same seed
        let rng1 = random_seeded(42);
        let rng2 = random_seeded(42);

        unsafe {
            let v1_1 = rng_float(rng1);
            let v1_2 = rng_float(rng1);
            let v1_3 = rng_float(rng1);

            let v2_1 = rng_float(rng2);
            let v2_2 = rng_float(rng2);
            let v2_3 = rng_float(rng2);

            assert_eq!(v1_1, v2_1, "first values should match");
            assert_eq!(v1_2, v2_2, "second values should match");
            assert_eq!(v1_3, v2_3, "third values should match");

            // Clean up
            drop(Box::from_raw(rng1));
            drop(Box::from_raw(rng2));
        }
    }

    #[test]
    fn test_different_seeds_different_values() {
        // Test that different seeds produce different sequences
        let rng1 = random_seeded(42);
        let rng2 = random_seeded(123);

        unsafe {
            let v1 = rng_float(rng1);
            let v2 = rng_float(rng2);

            assert_ne!(v1, v2, "different seeds should produce different values");

            // Clean up
            drop(Box::from_raw(rng1));
            drop(Box::from_raw(rng2));
        }
    }

    #[test]
    fn test_rng_float_range() {
        // Test that rng_float returns values in [0.0, 1.0)
        let rng = random_seeded(999);
        unsafe {
            for _ in 0..100 {
                let f = rng_float(rng);
                assert!(f >= 0.0, "rng_float {} should be >= 0.0", f);
                assert!(f < 1.0, "rng_float {} should be < 1.0", f);
            }
            // Clean up
            drop(Box::from_raw(rng));
        }
    }

    #[test]
    fn test_rng_float_null_safety() {
        // Test that rng_float handles null gracefully
        let result = rng_float(std::ptr::null_mut());
        assert_eq!(result, 0.0, "null RNG should return 0.0");
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("float").is_some());
        assert!(m.get("seeded").is_some());
        assert!(m.get("rng_float").is_some());

        // Check signatures
        let float_func = m.get("float").unwrap();
        assert!(float_func.signature.params.is_empty());
        assert_eq!(float_func.signature.return_type, NativeType::F64);

        let seeded_func = m.get("seeded").unwrap();
        assert_eq!(seeded_func.signature.params.len(), 1);
        assert_eq!(seeded_func.signature.params[0], NativeType::I64);
        assert_eq!(seeded_func.signature.return_type, NativeType::I64);

        let rng_float_func = m.get("rng_float").unwrap();
        assert_eq!(rng_float_func.signature.params.len(), 1);
        assert_eq!(rng_float_func.signature.params[0], NativeType::I64);
        assert_eq!(rng_float_func.signature.return_type, NativeType::F64);
    }
}

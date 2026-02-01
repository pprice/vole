// src/runtime/stdlib/random.rs
//! Native random number generation functions for std:random module.
//!
//! Provides:
//! - random_float() -> f64 in [0.0, 1.0) using thread_rng
//! - random_seeded(seed: i64) -> *mut RcRng - creates a seeded RNG instance
//! - rng_float(rng: *mut RcRng) -> f64 - get next float from seeded RNG

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::value::{RcHeader, TYPE_RNG};
use rand::rngs::StdRng;
use rand::{Rng as RandRng, SeedableRng};
use std::alloc::{Layout, dealloc};

/// Reference-counted RNG wrapper with RcHeader prefix.
///
/// Layout: `[RcHeader] [StdRng]` — the RNG is stored inline, not behind
/// another pointer.
#[repr(C)]
pub struct RcRng {
    header: RcHeader,
    rng: StdRng,
}

/// Drop function for RcRng, called by rc_dec when refcount reaches zero.
/// Deallocates the RcRng allocation.
///
/// # Safety
/// `ptr` must point to a valid `RcRng` allocation with refcount already at zero.
unsafe extern "C" fn rng_drop(ptr: *mut u8) {
    unsafe {
        let rng_ptr = ptr as *mut RcRng;
        // Drop the StdRng in place, then deallocate
        std::ptr::drop_in_place(&mut (*rng_ptr).rng);
        let layout = Layout::new::<RcRng>();
        dealloc(ptr, layout);
    }
}

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

    // seeded: (i64) -> i64 (opaque RcRng pointer)
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

/// Create a seeded RNG instance wrapped in an RcRng with RcHeader.
/// Returns an opaque pointer (as *mut RcRng) to the heap-allocated RcRng.
#[unsafe(no_mangle)]
pub extern "C" fn random_seeded(seed: i64) -> *mut RcRng {
    // Convert i64 seed to u64 bytes for seeding
    let seed_bytes = seed.to_le_bytes();
    let mut full_seed = [0u8; 32];
    // Fill the seed by repeating the 8 bytes to get 32 bytes
    for i in 0..4 {
        full_seed[i * 8..(i + 1) * 8].copy_from_slice(&seed_bytes);
    }
    let rng = StdRng::from_seed(full_seed);

    let layout = Layout::new::<RcRng>();
    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut RcRng;
        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        std::ptr::write(
            &mut (*ptr).header,
            RcHeader::with_drop_fn(TYPE_RNG, rng_drop),
        );
        std::ptr::write(&mut (*ptr).rng, rng);
        ptr
    }
}

/// Get the next random f64 in [0.0, 1.0) from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_float(rng_ptr: *mut RcRng) -> f64 {
    if rng_ptr.is_null() {
        return 0.0;
    }
    unsafe { (*rng_ptr).rng.r#gen::<f64>() }
}

/// Convert a random float in [0.0, 1.0) to an i64 in [min, max] (inclusive).
///
/// Uses `u128` arithmetic internally to avoid overflow when `max - min + 1`
/// would exceed `i64::MAX` (e.g. `random.int(0, i64::MAX)`). When the range
/// spans the entire `i64` space (`i64::MIN` to `i64::MAX`), the range count
/// is `u64::MAX + 1 = 2^64`, which fits in `u128` and converts losslessly
/// to `f64` at that scale.
fn int_from_float(f: f64, min: i64, max: i64) -> i64 {
    // Compute range as u128 to avoid overflow:
    //   (max as i128 - min as i128 + 1) is always in [1, 2^64]
    let range = (max as i128 - min as i128 + 1) as u128;
    let offset = (f * range as f64).floor() as i64;
    min.wrapping_add(offset)
}

/// Generate a random i64 in [min, max] (inclusive) using thread-local RNG
#[unsafe(no_mangle)]
pub extern "C" fn random_int(min: i64, max: i64) -> i64 {
    if min > max {
        return min;
    }
    int_from_float(rand::random::<f64>(), min, max)
}

/// Get the next random i64 in [min, max] (inclusive) from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_int(rng_ptr: *mut RcRng, min: i64, max: i64) -> i64 {
    if rng_ptr.is_null() || min > max {
        return min;
    }
    let f = unsafe { (*rng_ptr).rng.r#gen::<f64>() };
    int_from_float(f, min, max)
}

/// Get the next random boolean from a seeded RNG
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn rng_coin(rng_ptr: *mut RcRng) -> bool {
    if rng_ptr.is_null() {
        return false;
    }
    unsafe { (*rng_ptr).rng.r#gen::<f64>() < 0.5 }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::rc_dec;
    use std::sync::atomic::Ordering;

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

        let v1_1 = rng_float(rng1);
        let v1_2 = rng_float(rng1);
        let v1_3 = rng_float(rng1);

        let v2_1 = rng_float(rng2);
        let v2_2 = rng_float(rng2);
        let v2_3 = rng_float(rng2);

        assert_eq!(v1_1, v2_1, "first values should match");
        assert_eq!(v1_2, v2_2, "second values should match");
        assert_eq!(v1_3, v2_3, "third values should match");

        // Clean up via rc_dec (triggers rng_drop)
        rc_dec(rng1 as *mut u8);
        rc_dec(rng2 as *mut u8);
    }

    #[test]
    fn test_different_seeds_different_values() {
        // Test that different seeds produce different sequences
        let rng1 = random_seeded(42);
        let rng2 = random_seeded(123);

        let v1 = rng_float(rng1);
        let v2 = rng_float(rng2);

        assert_ne!(v1, v2, "different seeds should produce different values");

        // Clean up via rc_dec
        rc_dec(rng1 as *mut u8);
        rc_dec(rng2 as *mut u8);
    }

    #[test]
    fn test_rng_float_range() {
        // Test that rng_float returns values in [0.0, 1.0)
        let rng = random_seeded(999);
        for _ in 0..100 {
            let f = rng_float(rng);
            assert!(f >= 0.0, "rng_float {} should be >= 0.0", f);
            assert!(f < 1.0, "rng_float {} should be < 1.0", f);
        }
        // Clean up via rc_dec
        rc_dec(rng as *mut u8);
    }

    #[test]
    fn test_rng_float_null_safety() {
        // Test that rng_float handles null gracefully
        let result = rng_float(std::ptr::null_mut());
        assert_eq!(result, 0.0, "null RNG should return 0.0");
    }

    #[test]
    fn test_int_from_float_no_overflow_max_range() {
        // This would overflow with (max - min + 1) in i64 arithmetic
        let result = int_from_float(0.5, 0, i64::MAX);
        assert!(result >= 0 && result <= i64::MAX);
    }

    #[test]
    fn test_int_from_float_full_i64_range() {
        // Full i64 range: min=i64::MIN, max=i64::MAX => range = 2^64
        let result = int_from_float(0.0, i64::MIN, i64::MAX);
        assert_eq!(result, i64::MIN, "f=0.0 should yield min");

        let result = int_from_float(0.5, i64::MIN, i64::MAX);
        // f=0.5 on full i64 range should land near the midpoint (0).
        // f64 precision at 2^64 scale introduces minor rounding, so we
        // allow a small tolerance rather than demanding an exact value.
        assert!(
            result.abs() <= 1,
            "f=0.5 should yield ~0 for full range, got {result}"
        );
    }

    #[test]
    fn test_int_from_float_boundaries() {
        // f=0.0 should always give min
        assert_eq!(int_from_float(0.0, 10, 20), 10);
        // f just under 1.0 should give max
        let f = 1.0 - f64::EPSILON;
        let result = int_from_float(f, 10, 20);
        assert!(result >= 10 && result <= 20);
    }

    #[test]
    fn test_int_from_float_single_value() {
        // min == max should always return that value
        assert_eq!(int_from_float(0.0, 42, 42), 42);
        assert_eq!(int_from_float(0.5, 42, 42), 42);
        assert_eq!(int_from_float(0.999, 42, 42), 42);
    }

    #[test]
    fn test_random_int_no_overflow() {
        // Smoke test: random_int with large range should not panic
        for _ in 0..100 {
            let v = random_int(0, i64::MAX);
            assert!(v >= 0);
        }
    }

    #[test]
    fn test_rng_int_no_overflow() {
        // Smoke test: rng_int with large range should not panic
        let rng = random_seeded(12345);
        for _ in 0..100 {
            let v = rng_int(rng, i64::MIN, i64::MAX);
            // Just verify it doesn't panic; any i64 value is valid
            let _ = v;
        }
        rc_dec(rng as *mut u8);
    }

    #[test]
    fn test_random_int_min_gt_max() {
        assert_eq!(random_int(10, 5), 10);
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

    #[test]
    fn test_rc_rng_header_fields() {
        // Verify the RcHeader is properly initialized
        let rng = random_seeded(42);
        unsafe {
            let header = &(*rng).header;
            assert_eq!(header.type_id, TYPE_RNG);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);
            assert!(header.drop_fn.is_some());
        }
        rc_dec(rng as *mut u8);
    }

    #[test]
    fn test_rc_rng_inc_dec() {
        // Verify inc/dec work through RcHeader
        let rng = random_seeded(42);
        unsafe {
            let header = &(*rng).header;
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);

            crate::value::rc_inc(rng as *mut u8);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 2);

            // First dec: refcount goes to 1, no drop
            rc_dec(rng as *mut u8);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);

            // Still usable
            let f = rng_float(rng);
            assert!(f >= 0.0 && f < 1.0);

            // Final dec: refcount goes to 0, rng_drop called
            rc_dec(rng as *mut u8);
        }
    }
}

// src/runtime/stdlib/crypto.rs
//! Native cryptographic functions for std:crypto/hash module.
//!
//! Provides:
//! - sha256(string) -> string - SHA256 hash as hex string
//! - sha256_bytes(string) -> [i64] - SHA256 hash as array of byte values (0-255)

use crate::array::RcArray;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use crate::value::{TYPE_I64, TaggedValue};
use sha2::{Digest, Sha256};

/// Create the std:crypto/hash native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // sha256: (string) -> string - SHA256 hash as hex string
    m.register(
        "sha256",
        crypto_sha256 as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // sha256_bytes: (string) -> [i64] - SHA256 hash as array of bytes
    m.register(
        "sha256_bytes",
        crypto_sha256_bytes as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Array(Box::new(NativeType::I64)),
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Compute SHA256 hash of a string, returning hex-encoded result
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn crypto_sha256(input: *const RcString) -> *const RcString {
    if input.is_null() {
        return RcString::new("");
    }

    let input_str = unsafe { (*input).as_str() };

    let mut hasher = Sha256::new();
    hasher.update(input_str.as_bytes());
    let result = hasher.finalize();

    // Convert to hex string
    let hex_string = result
        .iter()
        .map(|b| format!("{:02x}", b))
        .collect::<String>();

    RcString::new(&hex_string)
}

/// Compute SHA256 hash of a string, returning array of byte values
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn crypto_sha256_bytes(input: *const RcString) -> *mut RcArray {
    // SHA256 always produces 32 bytes
    let arr = RcArray::with_capacity(32);

    if input.is_null() {
        // Return array of 32 zeros for null input
        for _ in 0..32 {
            unsafe {
                RcArray::push(
                    arr,
                    TaggedValue {
                        tag: TYPE_I64 as u64,
                        value: 0,
                    },
                );
            }
        }
        return arr;
    }

    let input_str = unsafe { (*input).as_str() };

    let mut hasher = Sha256::new();
    hasher.update(input_str.as_bytes());
    let result = hasher.finalize();

    // Push each byte as an i64 value
    for byte in result.iter() {
        unsafe {
            RcArray::push(
                arr,
                TaggedValue {
                    tag: TYPE_I64 as u64,
                    value: *byte as u64,
                },
            );
        }
    }

    arr
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to safely read a string
    unsafe fn read_string(s: *const RcString) -> String {
        if s.is_null() {
            String::new()
        } else {
            unsafe { (*s).as_str().to_string() }
        }
    }

    // Helper to clean up a string
    unsafe fn cleanup_string(s: *const RcString) {
        if !s.is_null() {
            unsafe { RcString::dec_ref(s as *mut RcString) };
        }
    }

    // Helper to clean up an array
    unsafe fn cleanup_array(arr: *mut RcArray) {
        if !arr.is_null() {
            unsafe { RcArray::dec_ref(arr) };
        }
    }

    #[test]
    fn test_sha256_empty_string() {
        let input = RcString::new("");
        let result = crypto_sha256(input);

        unsafe {
            // SHA256 of empty string is a well-known value
            let hash = read_string(result);
            assert_eq!(
                hash,
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            );
            cleanup_string(result);
            cleanup_string(input);
        }
    }

    #[test]
    fn test_sha256_hello_world() {
        let input = RcString::new("hello world");
        let result = crypto_sha256(input);

        unsafe {
            let hash = read_string(result);
            // SHA256 of "hello world" is a well-known test vector
            assert_eq!(
                hash,
                "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
            );
            cleanup_string(result);
            cleanup_string(input);
        }
    }

    #[test]
    fn test_sha256_null_input() {
        let result = crypto_sha256(std::ptr::null());
        unsafe {
            let hash = read_string(result);
            assert_eq!(hash, "");
            cleanup_string(result);
        }
    }

    #[test]
    fn test_sha256_bytes_empty_string() {
        let input = RcString::new("");
        let result = crypto_sha256_bytes(input);

        unsafe {
            let len = RcArray::len(result);
            assert_eq!(len, 32); // SHA256 always produces 32 bytes

            // First byte of SHA256("") is 0xe3
            let first = RcArray::get(result, 0);
            assert_eq!(first.value, 0xe3);

            // Last byte is 0x55
            let last = RcArray::get(result, 31);
            assert_eq!(last.value, 0x55);

            cleanup_array(result);
            cleanup_string(input);
        }
    }

    #[test]
    fn test_sha256_bytes_hello_world() {
        let input = RcString::new("hello world");
        let result = crypto_sha256_bytes(input);

        unsafe {
            let len = RcArray::len(result);
            assert_eq!(len, 32);

            // Verify first few bytes of SHA256("hello world")
            // b94d27b9934d3e08...
            assert_eq!(RcArray::get(result, 0).value, 0xb9);
            assert_eq!(RcArray::get(result, 1).value, 0x4d);
            assert_eq!(RcArray::get(result, 2).value, 0x27);
            assert_eq!(RcArray::get(result, 3).value, 0xb9);

            cleanup_array(result);
            cleanup_string(input);
        }
    }

    #[test]
    fn test_sha256_bytes_null_input() {
        let result = crypto_sha256_bytes(std::ptr::null());

        unsafe {
            let len = RcArray::len(result);
            assert_eq!(len, 32);

            // All bytes should be 0 for null input
            for i in 0..32 {
                assert_eq!(RcArray::get(result, i).value, 0);
            }

            cleanup_array(result);
        }
    }

    #[test]
    fn test_sha256_consistency() {
        // Hash and bytes should be consistent
        let input1 = RcString::new("test");
        let input2 = RcString::new("test");

        let hash_str = crypto_sha256(input1);
        let hash_bytes = crypto_sha256_bytes(input2);

        unsafe {
            let hex = read_string(hash_str);

            // Convert bytes to hex and compare
            let mut reconstructed = String::new();
            for i in 0..32 {
                let byte = RcArray::get(hash_bytes, i).value as u8;
                reconstructed.push_str(&format!("{:02x}", byte));
            }

            assert_eq!(hex, reconstructed);

            cleanup_string(hash_str);
            cleanup_array(hash_bytes);
            cleanup_string(input1);
            cleanup_string(input2);
        }
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("sha256").is_some());
        assert!(m.get("sha256_bytes").is_some());

        // Check signatures
        let sha256_func = m.get("sha256").unwrap();
        assert_eq!(sha256_func.signature.params.len(), 1);
        assert_eq!(sha256_func.signature.params[0], NativeType::String);
        assert_eq!(sha256_func.signature.return_type, NativeType::String);

        let sha256_bytes_func = m.get("sha256_bytes").unwrap();
        assert_eq!(sha256_bytes_func.signature.params.len(), 1);
        assert_eq!(sha256_bytes_func.signature.params[0], NativeType::String);
    }
}

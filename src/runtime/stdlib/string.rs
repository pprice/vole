// src/runtime/stdlib/string.rs
//! Native string functions for std:string module.

use crate::runtime::RcString;
use crate::runtime::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:string native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // string_length: (string) -> i64
    m.register(
        "string_length",
        string_length as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // string_contains: (string, string) -> bool
    m.register(
        "string_contains",
        string_contains as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    m
}

/// Get the length of a string (in bytes for now)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn string_length(s: *const RcString) -> i64 {
    if s.is_null() {
        return 0;
    }
    unsafe { (*s).as_str().len() as i64 }
}

/// Check if a string contains a substring
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn string_contains(s: *const RcString, needle: *const RcString) -> i8 {
    if s.is_null() || needle.is_null() {
        return 0;
    }
    unsafe {
        let haystack = (*s).as_str();
        let needle_str = (*needle).as_str();
        if haystack.contains(needle_str) { 1 } else { 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_length() {
        let s = RcString::new("hello");
        let len = string_length(s);
        assert_eq!(len, 5);
        // Clean up using dec_ref
        unsafe { RcString::dec_ref(s as *mut RcString) };
    }

    #[test]
    fn test_string_length_empty() {
        let s = RcString::new("");
        let len = string_length(s);
        assert_eq!(len, 0);
        unsafe { RcString::dec_ref(s as *mut RcString) };
    }

    #[test]
    fn test_string_length_null() {
        let len = string_length(std::ptr::null());
        assert_eq!(len, 0);
    }

    #[test]
    fn test_string_contains() {
        let s = RcString::new("hello world");
        let needle = RcString::new("world");
        let result = string_contains(s, needle);
        assert_eq!(result, 1);
        // Clean up
        unsafe {
            RcString::dec_ref(s as *mut RcString);
            RcString::dec_ref(needle as *mut RcString);
        }
    }

    #[test]
    fn test_string_contains_not_found() {
        let s = RcString::new("hello world");
        let needle = RcString::new("xyz");
        let result = string_contains(s, needle);
        assert_eq!(result, 0);
        unsafe {
            RcString::dec_ref(s as *mut RcString);
            RcString::dec_ref(needle as *mut RcString);
        }
    }

    #[test]
    fn test_string_contains_null() {
        let s = RcString::new("hello");
        // Test with null needle
        let result = string_contains(s, std::ptr::null());
        assert_eq!(result, 0);
        // Test with null haystack
        let needle = RcString::new("world");
        let result = string_contains(std::ptr::null(), needle);
        assert_eq!(result, 0);
        // Clean up
        unsafe {
            RcString::dec_ref(s as *mut RcString);
            RcString::dec_ref(needle as *mut RcString);
        }
    }

    #[test]
    fn test_module_registration() {
        let m = module();
        assert!(m.get("string_length").is_some());
        assert!(m.get("string_contains").is_some());

        let len_func = m.get("string_length").unwrap();
        assert_eq!(len_func.signature.params.len(), 1);
        assert_eq!(len_func.signature.params[0], NativeType::String);
        assert_eq!(len_func.signature.return_type, NativeType::I64);

        let contains_func = m.get("string_contains").unwrap();
        assert_eq!(contains_func.signature.params.len(), 2);
        assert_eq!(contains_func.signature.return_type, NativeType::Bool);
    }
}

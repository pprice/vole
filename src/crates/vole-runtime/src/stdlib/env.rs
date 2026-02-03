// src/runtime/stdlib/env.rs
//! Native environment functions for std:env module.
//!
//! Provides access to:
//! - CLI arguments
//! - Environment variables
//! - System paths (cwd, exe, home, temp)

use crate::array::RcArray;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use crate::value::{TYPE_ARRAY, TYPE_STRING, TaggedValue};
use std::alloc::{Layout, alloc};

/// Create the std:env native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // args: () -> [string] - CLI args excluding program name
    m.register(
        "args",
        env_args as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::Array(Box::new(NativeType::String)),
        },
    );

    // get: (string) -> string? - env var or nil
    m.register(
        "get",
        env_get as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Optional(Box::new(NativeType::String)),
        },
    );

    // vars: () -> [string, string][] - all env vars as array of [key, value] pairs
    m.register(
        "vars",
        env_vars as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::Array(Box::new(NativeType::Array(Box::new(
                NativeType::String,
            )))),
        },
    );

    // cwd: () -> string - current working directory
    m.register(
        "cwd",
        env_cwd as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::String,
        },
    );

    // exe_path: () -> string - path to current executable
    m.register(
        "exe_path",
        env_exe_path as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::String,
        },
    );

    // home_dir: () -> string? - user home directory or nil
    m.register(
        "home_dir",
        env_home_dir as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::Optional(Box::new(NativeType::String)),
        },
    );

    // temp_dir: () -> string - system temp directory
    m.register(
        "temp_dir",
        env_temp_dir as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::String,
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Get CLI arguments (excluding program name)
/// Returns an array of strings
#[unsafe(no_mangle)]
pub extern "C" fn env_args() -> *mut RcArray {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let arr = RcArray::with_capacity(args.len());

    for arg in args {
        let s = RcString::new(&arg);
        unsafe {
            RcArray::push(
                arr,
                TaggedValue {
                    tag: TYPE_STRING as u64,
                    value: s as u64,
                },
            );
        }
    }

    arr
}

/// Get environment variable by name
/// Returns a boxed optional: tag at offset 0 (0=present, 1=nil), value at offset 8
#[unsafe(no_mangle)]
pub extern "C" fn env_get(name: *const RcString) -> *mut u8 {
    // Allocate boxed optional (16 bytes: 8 byte tag + 8 byte value)
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    if name.is_null() {
        // Return nil for null name
        unsafe {
            std::ptr::write(ptr, 1u8); // tag 1 = nil
            std::ptr::write(ptr.add(8) as *mut i64, 0);
        }
        return ptr;
    }

    let name_str = unsafe { (*name).as_str() };

    match std::env::var(name_str) {
        Ok(value) => {
            let s = RcString::new(&value);
            unsafe {
                std::ptr::write(ptr, 0u8); // tag 0 = value present
                std::ptr::write(ptr.add(8) as *mut i64, s as i64);
            }
        }
        Err(_) => {
            unsafe {
                std::ptr::write(ptr, 1u8); // tag 1 = nil
                std::ptr::write(ptr.add(8) as *mut i64, 0);
            }
        }
    }
    ptr
}

/// Get all environment variables as array of [key, value] pairs
/// Each pair is a 2-element array of strings
#[unsafe(no_mangle)]
pub extern "C" fn env_vars() -> *mut RcArray {
    let vars: Vec<(String, String)> = std::env::vars().collect();
    let arr = RcArray::with_capacity(vars.len());

    for (key, value) in vars {
        // Create a 2-element array [key, value]
        let pair = RcArray::with_capacity(2);
        let key_str = RcString::new(&key);
        let value_str = RcString::new(&value);

        unsafe {
            RcArray::push(
                pair,
                TaggedValue {
                    tag: TYPE_STRING as u64,
                    value: key_str as u64,
                },
            );
            RcArray::push(
                pair,
                TaggedValue {
                    tag: TYPE_STRING as u64,
                    value: value_str as u64,
                },
            );

            // Add pair to outer array
            RcArray::push(
                arr,
                TaggedValue {
                    tag: TYPE_ARRAY as u64,
                    value: pair as u64,
                },
            );
        }
    }

    arr
}

/// Get current working directory
/// Returns empty string on error
#[unsafe(no_mangle)]
pub extern "C" fn env_cwd() -> *const RcString {
    match std::env::current_dir() {
        Ok(path) => RcString::new(&path.to_string_lossy()),
        Err(_) => RcString::new(""),
    }
}

/// Get path to current executable
/// Returns empty string on error
#[unsafe(no_mangle)]
pub extern "C" fn env_exe_path() -> *const RcString {
    match std::env::current_exe() {
        Ok(path) => RcString::new(&path.to_string_lossy()),
        Err(_) => RcString::new(""),
    }
}

/// Get user home directory
/// Returns a boxed optional: tag at offset 0 (0=present, 1=nil), value at offset 8
#[unsafe(no_mangle)]
pub extern "C" fn env_home_dir() -> *mut u8 {
    // Allocate boxed optional (16 bytes: 8 byte tag + 8 byte value)
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    // Try to get home directory from environment
    let home_path = {
        #[cfg(target_family = "unix")]
        {
            std::env::var_os("HOME")
        }
        #[cfg(target_family = "windows")]
        {
            std::env::var_os("USERPROFILE")
        }
        #[cfg(not(any(target_family = "unix", target_family = "windows")))]
        {
            None
        }
    };

    match home_path {
        Some(path) => {
            let s = RcString::new(&path.to_string_lossy());
            unsafe {
                std::ptr::write(ptr, 0u8); // tag 0 = value present
                std::ptr::write(ptr.add(8) as *mut i64, s as i64);
            }
        }
        None => {
            unsafe {
                std::ptr::write(ptr, 1u8); // tag 1 = nil
                std::ptr::write(ptr.add(8) as *mut i64, 0);
            }
        }
    }
    ptr
}

/// Get system temp directory
#[unsafe(no_mangle)]
pub extern "C" fn env_temp_dir() -> *const RcString {
    let path = std::env::temp_dir();
    RcString::new(&path.to_string_lossy())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::dealloc;

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

    // Helper to read a boxed optional - returns (is_present, string_ptr)
    unsafe fn read_boxed_optional(ptr: *mut u8) -> (bool, *const RcString) {
        if ptr.is_null() {
            return (false, std::ptr::null());
        }
        let tag = unsafe { *ptr };
        let value = unsafe { std::ptr::read(ptr.add(8) as *const i64) };
        (tag == 0, value as *const RcString)
    }

    // Helper to clean up a boxed optional
    unsafe fn cleanup_boxed_optional(ptr: *mut u8) {
        if !ptr.is_null() {
            let (is_present, string_ptr) = unsafe { read_boxed_optional(ptr) };
            if is_present {
                unsafe { cleanup_string(string_ptr) };
            }
            let layout = Layout::from_size_align(16, 8).unwrap();
            unsafe { dealloc(ptr, layout) };
        }
    }

    #[test]
    fn test_env_args_returns_array() {
        let args = env_args();
        assert!(!args.is_null());
        // During tests, there may or may not be args
        unsafe {
            cleanup_array(args);
        }
    }

    #[test]
    fn test_env_get_existing_var() {
        // Set a test variable
        // Safety: This test is single-threaded and the var name is unique
        unsafe { std::env::set_var("VOLE_TEST_VAR", "test_value") };

        let name = RcString::new("VOLE_TEST_VAR");
        let result = env_get(name);

        assert!(!result.is_null());
        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result);
            assert!(is_present);
            assert_eq!(read_string(string_ptr), "test_value");
            cleanup_boxed_optional(result);
            cleanup_string(name);
        }

        // Safety: Single-threaded test cleanup
        unsafe { std::env::remove_var("VOLE_TEST_VAR") };
    }

    #[test]
    fn test_env_get_nonexistent_var() {
        let name = RcString::new("VOLE_NONEXISTENT_VAR_12345");
        let result = env_get(name);

        assert!(!result.is_null()); // Boxed optional is never null
        unsafe {
            let (is_present, _) = read_boxed_optional(result);
            assert!(!is_present); // Should be nil
            cleanup_boxed_optional(result);
            cleanup_string(name);
        }
    }

    #[test]
    fn test_env_get_null_name() {
        let result = env_get(std::ptr::null());
        assert!(!result.is_null()); // Boxed optional is never null
        unsafe {
            let (is_present, _) = read_boxed_optional(result);
            assert!(!is_present); // Should be nil
            cleanup_boxed_optional(result);
        }
    }

    #[test]
    fn test_env_vars_returns_array() {
        let vars = env_vars();
        assert!(!vars.is_null());

        unsafe {
            // Should have at least some environment variables
            let len = RcArray::len(vars);
            assert!(len > 0);
            cleanup_array(vars);
        }
    }

    #[test]
    fn test_env_cwd_returns_nonempty() {
        let cwd = env_cwd();
        assert!(!cwd.is_null());

        unsafe {
            let s = read_string(cwd);
            assert!(!s.is_empty());
            cleanup_string(cwd);
        }
    }

    #[test]
    fn test_env_exe_path_returns_nonempty() {
        let exe = env_exe_path();
        assert!(!exe.is_null());

        unsafe {
            let s = read_string(exe);
            assert!(!s.is_empty());
            cleanup_string(exe);
        }
    }

    #[test]
    fn test_env_home_dir() {
        let home = env_home_dir();
        // home_dir always returns a boxed optional (never null)
        assert!(!home.is_null());

        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(home);
            // home_dir may return nil on some systems
            if is_present {
                let s = read_string(string_ptr);
                assert!(!s.is_empty());
            }
            cleanup_boxed_optional(home);
        }
    }

    #[test]
    fn test_env_temp_dir_returns_nonempty() {
        let temp = env_temp_dir();
        assert!(!temp.is_null());

        unsafe {
            let s = read_string(temp);
            assert!(!s.is_empty());
            cleanup_string(temp);
        }
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("args").is_some());
        assert!(m.get("get").is_some());
        assert!(m.get("vars").is_some());
        assert!(m.get("cwd").is_some());
        assert!(m.get("exe_path").is_some());
        assert!(m.get("home_dir").is_some());
        assert!(m.get("temp_dir").is_some());

        // Check signatures
        let args_func = m.get("args").unwrap();
        assert!(args_func.signature.params.is_empty());

        let get_func = m.get("get").unwrap();
        assert_eq!(get_func.signature.params.len(), 1);
        assert_eq!(get_func.signature.params[0], NativeType::String);

        let cwd_func = m.get("cwd").unwrap();
        assert!(cwd_func.signature.params.is_empty());
        assert_eq!(cwd_func.signature.return_type, NativeType::String);
    }
}

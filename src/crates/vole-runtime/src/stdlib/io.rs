// src/runtime/stdlib/io.rs
//! Native I/O functions for std:io module.
//!
//! Provides:
//! - read_line() -> string? - reads line from stdin, nil on EOF
//! - flush() - flush stdout

use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;
use std::alloc::{Layout, alloc};
use std::cell::RefCell;
use std::io::{self, BufRead};

thread_local! {
    static STDIN_CAPTURE: RefCell<Option<Box<dyn BufRead + Send>>> = const { RefCell::new(None) };
}

/// Set a custom reader for stdin capture. Pass None to restore normal stdin.
/// This is useful for testing I/O functions.
pub fn set_stdin_capture(reader: Option<Box<dyn BufRead + Send>>) {
    STDIN_CAPTURE.with(|cell| {
        *cell.borrow_mut() = reader;
    });
}

/// Create the std:io native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // read_line: () -> string? - read line from stdin, nil on EOF
    m.register(
        "read_line",
        io_read_line as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::Optional(Box::new(NativeType::String)),
        },
    );

    // flush: () -> nil - flush stdout
    m.register(
        "flush",
        io_flush as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::Nil,
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Read a line from stdin.
/// Returns a boxed optional: tag at offset 0 (0=present, 1=nil), value at offset 8.
/// Returns nil on EOF or error.
#[unsafe(no_mangle)]
pub extern "C" fn io_read_line() -> *mut u8 {
    // Allocate boxed optional (16 bytes: 8 byte tag + 8 byte value)
    let layout = Layout::from_size_align(16, 8).expect("valid optional layout");
    let ptr = unsafe { alloc(layout) };
    if ptr.is_null() {
        std::alloc::handle_alloc_error(layout);
    }

    let read_result = STDIN_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let mut line = String::new();

        if let Some(ref mut reader) = *borrow {
            // Use captured stdin (for testing)
            match reader.read_line(&mut line) {
                Ok(0) => None, // EOF
                Ok(_) => Some(line),
                Err(_) => None, // Error treated as EOF
            }
        } else {
            // Use real stdin
            let stdin = io::stdin();
            let mut handle = stdin.lock();
            match handle.read_line(&mut line) {
                Ok(0) => None, // EOF
                Ok(_) => Some(line),
                Err(_) => None, // Error treated as EOF
            }
        }
    });

    match read_result {
        Some(mut line) => {
            // Remove trailing newline if present
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            let s = RcString::new(&line);
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

/// Flush stdout.
/// This is a wrapper around the vole_flush builtin for consistency.
#[unsafe(no_mangle)]
pub extern "C" fn io_flush() {
    // Use the existing stdout capture mechanism from builtins
    use crate::builtins::vole_flush;
    vole_flush();
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::dealloc;
    use std::io::Cursor;

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
            let layout = Layout::from_size_align(16, 8).expect("valid layout for boxed optional");
            unsafe { dealloc(ptr, layout) };
        }
    }

    #[test]
    fn test_read_line_with_capture() {
        // Set up captured stdin with test data
        let test_input = "hello world\n";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        let result = io_read_line();
        assert!(!result.is_null());

        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result);
            assert!(is_present, "should have a value");
            assert_eq!(read_string(string_ptr), "hello world");
            cleanup_boxed_optional(result);
        }

        // Clean up capture
        set_stdin_capture(None);
    }

    #[test]
    fn test_read_line_strips_newline() {
        let test_input = "test line\n";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        let result = io_read_line();

        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result);
            assert!(is_present);
            let line = read_string(string_ptr);
            assert!(!line.ends_with('\n'), "newline should be stripped");
            assert_eq!(line, "test line");
            cleanup_boxed_optional(result);
        }

        set_stdin_capture(None);
    }

    #[test]
    fn test_read_line_strips_crlf() {
        let test_input = "windows line\r\n";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        let result = io_read_line();

        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result);
            assert!(is_present);
            let line = read_string(string_ptr);
            assert!(!line.ends_with('\n'), "LF should be stripped");
            assert!(!line.ends_with('\r'), "CR should be stripped");
            assert_eq!(line, "windows line");
            cleanup_boxed_optional(result);
        }

        set_stdin_capture(None);
    }

    #[test]
    fn test_read_line_eof() {
        // Empty input simulates EOF
        let test_input = "";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        let result = io_read_line();

        unsafe {
            let (is_present, _) = read_boxed_optional(result);
            assert!(!is_present, "should be nil on EOF");
            cleanup_boxed_optional(result);
        }

        set_stdin_capture(None);
    }

    #[test]
    fn test_read_line_multiple_lines() {
        let test_input = "line1\nline2\nline3\n";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        // Read first line
        let result1 = io_read_line();
        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result1);
            assert!(is_present);
            assert_eq!(read_string(string_ptr), "line1");
            cleanup_boxed_optional(result1);
        }

        // Read second line
        let result2 = io_read_line();
        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result2);
            assert!(is_present);
            assert_eq!(read_string(string_ptr), "line2");
            cleanup_boxed_optional(result2);
        }

        // Read third line
        let result3 = io_read_line();
        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result3);
            assert!(is_present);
            assert_eq!(read_string(string_ptr), "line3");
            cleanup_boxed_optional(result3);
        }

        // Read EOF
        let result4 = io_read_line();
        unsafe {
            let (is_present, _) = read_boxed_optional(result4);
            assert!(!is_present, "should be nil on EOF");
            cleanup_boxed_optional(result4);
        }

        set_stdin_capture(None);
    }

    #[test]
    fn test_read_line_empty_line() {
        let test_input = "\n";
        let cursor = Cursor::new(test_input.as_bytes().to_vec());
        set_stdin_capture(Some(Box::new(cursor)));

        let result = io_read_line();

        unsafe {
            let (is_present, string_ptr) = read_boxed_optional(result);
            assert!(is_present, "empty line should not be nil");
            assert_eq!(read_string(string_ptr), "");
            cleanup_boxed_optional(result);
        }

        set_stdin_capture(None);
    }

    #[test]
    fn test_flush_does_not_panic() {
        // Just verify flush doesn't panic
        io_flush();
    }

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("read_line").is_some());
        assert!(m.get("flush").is_some());

        // Check signatures
        let read_line_func = m.get("read_line").unwrap();
        assert!(read_line_func.signature.params.is_empty());
        assert_eq!(
            read_line_func.signature.return_type,
            NativeType::Optional(Box::new(NativeType::String))
        );

        let flush_func = m.get("flush").unwrap();
        assert!(flush_func.signature.params.is_empty());
        assert_eq!(flush_func.signature.return_type, NativeType::Nil);
    }
}

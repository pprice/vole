// src/runtime/builtins.rs
//!
//! Core runtime FFI functions for the Vole JIT compiler.
//! Includes I/O, string conversion, and array operations.

use crate::RcString;
use crate::array::RcArray;
use crate::value::TaggedValue;
use std::cell::{Cell, RefCell};
use std::io::{self, Write};

// =============================================================================
// Macro for generating to_string FFI functions
// =============================================================================

/// Macro to generate numeric to_string FFI functions.
/// Creates a `vole_{type}_to_string` function and a non-prefixed alias.
macro_rules! to_string_ffi {
    ($type:ty, $name:ident) => {
        paste::paste! {
            #[doc = concat!("Convert ", stringify!($type), " to string (FFI entry point)")]
            #[unsafe(no_mangle)]
            pub extern "C" fn [<vole_ $name _to_string>](value: $type) -> *mut RcString {
                RcString::new(&value.to_string())
            }

            #[doc = concat!("Convert ", stringify!($type), " to string (alias for intrinsics)")]
            #[unsafe(no_mangle)]
            pub extern "C" fn [<$name _to_string>](value: $type) -> *mut RcString {
                [<vole_ $name _to_string>](value)
            }
        }
    };
}

// Generate to_string functions for numeric types
to_string_ffi!(i64, i64);
to_string_ffi!(i32, i32);
to_string_ffi!(f64, f64);
to_string_ffi!(f32, f32);
to_string_ffi!(i128, i128);

/// Convert bool to string (FFI entry point)
/// Uses i8 representation (0 = false, non-0 = true)
#[unsafe(no_mangle)]
pub extern "C" fn vole_bool_to_string(value: i8) -> *mut RcString {
    let s = if value != 0 { "true" } else { "false" };
    RcString::new(s)
}

/// Convert bool to string (alias for intrinsics)
#[unsafe(no_mangle)]
pub extern "C" fn bool_to_string(value: i8) -> *mut RcString {
    vole_bool_to_string(value)
}

/// Convert nil to string (FFI entry point)
#[unsafe(no_mangle)]
pub extern "C" fn vole_nil_to_string() -> *mut RcString {
    RcString::new("nil")
}

/// Convert nil to string (alias for intrinsics)
#[unsafe(no_mangle)]
pub extern "C" fn nil_to_string() -> *mut RcString {
    vole_nil_to_string()
}

thread_local! {
    static STDOUT_CAPTURE: RefCell<Option<Box<dyn Write + Send>>> = const { RefCell::new(None) };
    static STDERR_CAPTURE: RefCell<Option<Box<dyn Write + Send>>> = const { RefCell::new(None) };
    static CAPTURE_MODE: Cell<bool> = const { Cell::new(false) };
}

/// Set a custom writer for stdout capture. Pass None to restore normal stdout.
pub fn set_stdout_capture(writer: Option<Box<dyn Write + Send>>) {
    STDOUT_CAPTURE.with(|cell| {
        *cell.borrow_mut() = writer;
    });
}

/// Set a custom writer for stderr capture. Pass None to restore normal stderr.
pub fn set_stderr_capture(writer: Option<Box<dyn Write + Send>>) {
    STDERR_CAPTURE.with(|cell| {
        *cell.borrow_mut() = writer;
    });
}

/// Set capture mode. When enabled, panic will not call exit().
/// This is used for snapshot testing where we want to capture output
/// without killing the test runner process.
pub fn set_capture_mode(enabled: bool) {
    CAPTURE_MODE.with(|cell| {
        cell.set(enabled);
    });
}

/// Write to captured stdout or real stdout
fn write_stdout(s: &str) {
    STDOUT_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ref mut writer) = *borrow {
            let _ = write!(writer, "{}", s);
        } else {
            print!("{}", s);
        }
    });
}

fn writeln_stdout(s: &str) {
    STDOUT_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ref mut writer) = *borrow {
            let _ = writeln!(writer, "{}", s);
        } else {
            println!("{}", s);
        }
    });
}

/// Write bytes to the stderr capture if active, otherwise to real stderr.
pub fn write_to_stderr_capture(bytes: &[u8]) {
    STDERR_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ref mut writer) = *borrow {
            let _ = writer.write_all(bytes);
        } else {
            let _ = io::stderr().write_all(bytes);
        }
    });
}

fn writeln_stderr(s: &str) {
    STDERR_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ref mut writer) = *borrow {
            let _ = writeln!(writer, "{}", s);
        } else {
            eprintln!("{}", s);
        }
    });
}

// =============================================================================
// Macro for generating print/println FFI functions
// =============================================================================

/// Macro to generate print and println FFI functions for a given type.
/// Creates both `vole_print_{name}` and `vole_println_{name}` functions.
macro_rules! print_fns {
    ($name:ident, $arg_type:ty, $to_str:expr) => {
        paste::paste! {
            #[doc = concat!("Print a ", stringify!($name), " to stdout with newline")]
            #[unsafe(no_mangle)]
            pub extern "C" fn [<vole_println_ $name>](value: $arg_type) {
                let to_str: fn($arg_type) -> std::borrow::Cow<'static, str> = $to_str;
                writeln_stdout(&to_str(value));
            }

            #[doc = concat!("Print a ", stringify!($name), " to stdout without newline")]
            #[unsafe(no_mangle)]
            pub extern "C" fn [<vole_print_ $name>](value: $arg_type) {
                let to_str: fn($arg_type) -> std::borrow::Cow<'static, str> = $to_str;
                write_stdout(&to_str(value));
            }
        }
    };
}

// Generate print/println functions for each type
print_fns!(string, *const RcString, |ptr| {
    if ptr.is_null() {
        std::borrow::Cow::Borrowed("")
    } else {
        std::borrow::Cow::Owned(unsafe { (*ptr).as_str() }.to_string())
    }
});

print_fns!(i64, i64, |v| std::borrow::Cow::Owned(v.to_string()));
print_fns!(f64, f64, |v| std::borrow::Cow::Owned(v.to_string()));
print_fns!(bool, i8, |v| {
    if v != 0 {
        std::borrow::Cow::Borrowed("true")
    } else {
        std::borrow::Cow::Borrowed("false")
    }
});

/// Concatenate two strings
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_concat(a: *const RcString, b: *const RcString) -> *mut RcString {
    unsafe {
        let bytes_a: &[u8] = if a.is_null() { &[] } else { (*a).data() };
        let bytes_b: &[u8] = if b.is_null() { &[] } else { (*b).data() };
        RcString::from_two_parts(bytes_a, bytes_b)
    }
}

/// Convert an i64 array to string representation
/// Shows first 5 elements, then "..." for truncation
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_i64_to_string(ptr: *const RcArray) -> *mut RcString {
    if ptr.is_null() {
        return RcString::new("[]");
    }
    unsafe {
        let len = (*ptr).len;
        let mut result = String::from("[");
        let show_count = len.min(5);

        for i in 0..show_count {
            if i > 0 {
                result.push_str(", ");
            }
            let elem = RcArray::get(ptr, i);
            result.push_str(&elem.as_i64().to_string());
        }

        if len > 5 {
            result.push_str(", ...");
        }
        result.push(']');
        RcString::new(&result)
    }
}

/// Flush stdout (useful for interactive output)
#[unsafe(no_mangle)]
pub extern "C" fn vole_flush() {
    STDOUT_CAPTURE.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(ref mut writer) = *borrow {
            let _ = writer.flush();
        } else {
            let _ = io::stdout().flush();
        }
    });
}

/// Print a character (for mandelbrot output)
#[unsafe(no_mangle)]
pub extern "C" fn vole_print_char(c: u8) {
    write_stdout(&(c as char).to_string());
}

/// Panic with a message - prints to stderr and exits with code 1.
/// If a test jmp_buf is set (unit tests or capture mode), uses longjmp to escape.
#[unsafe(no_mangle)]
pub extern "C" fn vole_panic(
    msg: *const RcString,
    file: *const u8,
    file_len: usize,
    line: u32,
) -> ! {
    let msg_str = unsafe { if msg.is_null() { "" } else { (*msg).as_str() } };

    let file_str = unsafe {
        if file.is_null() || file_len == 0 {
            "<unknown>"
        } else {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(file, file_len))
        }
    };

    writeln_stderr(&format!("panic: {}", msg_str));
    writeln_stderr(&format!("  at {}:{}", file_str, line));

    // If a test jmp_buf is set, longjmp back to the test harness.
    // This handles both unit test mode (set_test_jmp_buf) and capture mode.
    use crate::assert::{ASSERT_FAILURE, ASSERT_JMP_BUF, AssertFailure, siglongjmp};
    ASSERT_JMP_BUF.with(|jb| {
        let buf = jb.get();
        if !buf.is_null() {
            ASSERT_FAILURE.with(|f| {
                f.set(Some(AssertFailure {
                    file: file_str.to_string(),
                    line,
                }));
            });
            unsafe {
                siglongjmp(buf, 2); // Use value 2 to distinguish from assert failure
            }
        }
    });

    // No jmp_buf set - exit process
    std::process::exit(1);
}

// Array FFI functions

/// Trigger a clean Vole panic for array index out of bounds.
/// Uses the longjmp-based error path so extern "C" functions don't unwind.
#[cold]
#[inline(never)]
fn array_index_oob(index: usize, len: usize) -> ! {
    let msg = RcString::new(&format!(
        "array index out of bounds: index {} but length is {}",
        index, len
    ));
    let file = b"<runtime>";
    vole_panic(msg, file.as_ptr(), file.len(), 0);
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_new() -> *mut RcArray {
    RcArray::new()
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_with_capacity(capacity: usize) -> *mut RcArray {
    RcArray::with_capacity(capacity)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_push(arr: *mut RcArray, tag: u64, value: u64) {
    unsafe {
        RcArray::push(arr, TaggedValue { tag, value });
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_get_tag(arr: *const RcArray, index: usize) -> u64 {
    if arr.is_null() {
        return 0;
    }
    let len = unsafe { (*arr).len };
    if index >= len {
        array_index_oob(index, len);
    }
    unsafe { RcArray::get(arr, index).tag }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_get_value(arr: *const RcArray, index: usize) -> u64 {
    if arr.is_null() {
        return 0;
    }
    let len = unsafe { (*arr).len };
    if index >= len {
        array_index_oob(index, len);
    }
    unsafe { RcArray::get(arr, index).value }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_set(arr: *mut RcArray, index: usize, tag: u64, value: u64) {
    if arr.is_null() {
        return;
    }
    let len = unsafe { (*arr).len };
    if index >= len {
        array_index_oob(index, len);
    }
    unsafe {
        RcArray::set(arr, index, TaggedValue { tag, value });
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_len(arr: *const RcArray) -> usize {
    if arr.is_null() {
        return 0;
    }
    unsafe { RcArray::len(arr) }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_inc(ptr: *mut RcArray) {
    crate::value::rc_inc(ptr as *mut u8);
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_dec(ptr: *mut RcArray) {
    crate::value::rc_dec(ptr as *mut u8);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_concat() {
        let a = RcString::new("hello");
        let b = RcString::new(" world");
        let result = vole_string_concat(a, b);

        unsafe {
            assert_eq!((*result).as_str(), "hello world");
            // Safety: All pointers are valid from RcString::new
            RcString::dec_ref(result);
            RcString::dec_ref(a as *mut _);
            RcString::dec_ref(b as *mut _);
        }
    }

    #[test]
    fn test_i64_to_string() {
        let result = vole_i64_to_string(42);
        unsafe {
            assert_eq!((*result).as_str(), "42");
            // Safety: result is valid from vole_i64_to_string
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn test_f64_to_string() {
        let result = vole_f64_to_string(3.25);
        unsafe {
            assert!((*result).as_str().starts_with("3.25"));
            // Safety: result is valid from vole_f64_to_string
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn test_bool_to_string() {
        let t = vole_bool_to_string(1);
        let f = vole_bool_to_string(0);
        unsafe {
            assert_eq!((*t).as_str(), "true");
            assert_eq!((*f).as_str(), "false");
            // Safety: t and f are valid from vole_bool_to_string
            RcString::dec_ref(t);
            RcString::dec_ref(f);
        }
    }
}

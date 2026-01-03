// src/runtime/builtins.rs

use crate::runtime::RcString;
use crate::runtime::array::RcArray;
use crate::runtime::value::TaggedValue;
use std::cell::RefCell;
use std::io::{self, Write};

thread_local! {
    static STDOUT_CAPTURE: RefCell<Option<Box<dyn Write + Send>>> = const { RefCell::new(None) };
}

/// Set a custom writer for stdout capture. Pass None to restore normal stdout.
pub fn set_stdout_capture(writer: Option<Box<dyn Write + Send>>) {
    STDOUT_CAPTURE.with(|cell| {
        *cell.borrow_mut() = writer;
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

/// Print a string to stdout with newline
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_println_string(ptr: *const RcString) {
    if ptr.is_null() {
        writeln_stdout("");
        return;
    }
    unsafe {
        let s = (*ptr).as_str();
        writeln_stdout(s);
    }
}

/// Print an i64 to stdout with newline
#[unsafe(no_mangle)]
pub extern "C" fn vole_println_i64(value: i64) {
    writeln_stdout(&value.to_string());
}

/// Print an f64 to stdout with newline
#[unsafe(no_mangle)]
pub extern "C" fn vole_println_f64(value: f64) {
    writeln_stdout(&value.to_string());
}

/// Print a bool to stdout with newline
#[unsafe(no_mangle)]
pub extern "C" fn vole_println_bool(value: i8) {
    if value != 0 {
        writeln_stdout("true");
    } else {
        writeln_stdout("false");
    }
}

/// Concatenate two strings
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_concat(a: *const RcString, b: *const RcString) -> *mut RcString {
    unsafe {
        let s_a = if a.is_null() { "" } else { (*a).as_str() };
        let s_b = if b.is_null() { "" } else { (*b).as_str() };
        let result = format!("{}{}", s_a, s_b);
        RcString::new(&result)
    }
}

/// Convert i64 to string
#[unsafe(no_mangle)]
pub extern "C" fn vole_i64_to_string(value: i64) -> *mut RcString {
    let s = value.to_string();
    RcString::new(&s)
}

/// Convert f64 to string
#[unsafe(no_mangle)]
pub extern "C" fn vole_f64_to_string(value: f64) -> *mut RcString {
    let s = value.to_string();
    RcString::new(&s)
}

/// Convert bool to string
#[unsafe(no_mangle)]
pub extern "C" fn vole_bool_to_string(value: i8) -> *mut RcString {
    let s = if value != 0 { "true" } else { "false" };
    RcString::new(s)
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

// Array FFI functions

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_new() -> *mut RcArray {
    RcArray::new()
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_array_with_capacity(capacity: usize) -> *mut RcArray {
    RcArray::with_capacity(capacity)
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_push(arr: *mut RcArray, tag: u64, value: u64) {
    unsafe {
        RcArray::push(arr, TaggedValue { tag, value });
    }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_get_tag(arr: *const RcArray, index: usize) -> u64 {
    if arr.is_null() {
        return 0;
    }
    unsafe { RcArray::get(arr, index).tag }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_get_value(arr: *const RcArray, index: usize) -> u64 {
    if arr.is_null() {
        return 0;
    }
    unsafe { RcArray::get(arr, index).value }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_set(arr: *mut RcArray, index: usize, tag: u64, value: u64) {
    unsafe {
        RcArray::set(arr, index, TaggedValue { tag, value });
    }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_len(arr: *const RcArray) -> usize {
    if arr.is_null() {
        return 0;
    }
    unsafe { RcArray::len(arr) }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_inc(ptr: *mut RcArray) {
    unsafe { RcArray::inc_ref(ptr) }
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_dec(ptr: *mut RcArray) {
    unsafe { RcArray::dec_ref(ptr) }
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
        let result = vole_f64_to_string(3.14);
        unsafe {
            assert!((*result).as_str().starts_with("3.14"));
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

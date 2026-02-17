// src/runtime/builtins.rs
//!
//! Core runtime FFI functions for the Vole JIT compiler.
//! Includes I/O, string conversion, and array operations.
//!
//! # JIT-Runtime FFI safety contract
//!
//! All `extern "C"` functions in this module are called directly from
//! JIT-compiled code via symbol lookup. The JIT guarantees:
//!
//! - **Pointer validity**: every pointer argument is either null or points
//!   to a live, properly initialized allocation of the expected type.
//! - **Null handling**: functions that receive pointers defensively check
//!   for null and return a zero/empty/no-op result. This supports Vole's
//!   nil-propagation semantics where `nil.method()` flows through gracefully
//!   rather than crashing. The JIT does not emit null guards before calls.
//! - **String pointers**: `*const RcString` / `*mut RcString` are always
//!   valid RC-managed strings or null. The JIT manages their lifetimes via
//!   `rc_inc` / `rc_dec`.
//! - **Array pointers**: `*const RcArray` / `*mut RcArray` are always valid
//!   RC-managed arrays or null. Index bounds ARE checked at runtime (unlike
//!   instance field slots) because array indices come from user expressions.

use crate::RcString;
use crate::array::RcArray;
use crate::value::{RuntimeTypeId, TaggedValue, union_heap_cleanup};
use std::alloc::Layout;
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

#[inline]
fn f128_bits_to_f64(bits: i128) -> f64 {
    // Runtime f128 support currently uses a compact software representation where
    // the low 64 bits carry an f64 payload and the high 64 bits are zeroed.
    f64::from_bits((bits as u128) as u64)
}

#[inline]
fn f64_to_f128_bits(v: f64) -> i128 {
    (v.to_bits() as u128) as i128
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_to_string(bits: i128) -> *mut RcString {
    RcString::new(&f128_bits_to_f64(bits).to_string())
}

#[unsafe(no_mangle)]
pub extern "C" fn f128_to_string(bits: i128) -> *mut RcString {
    vole_f128_to_string(bits)
}

// =============================================================================
// i128 arithmetic helpers (Cranelift x64 doesn't support sdiv/srem for i128)
// =============================================================================

/// Signed 128-bit integer division.
///
/// Cranelift's x64 backend does not support i128 sdiv/srem natively, so
/// the JIT calls out to this runtime helper. Panics on division by zero
/// or overflow (i128::MIN / -1).
#[unsafe(no_mangle)]
pub extern "C" fn vole_i128_sdiv(a: i128, b: i128) -> i128 {
    if b == 0 {
        let msg = RcString::new("division by zero");
        let file = b"<runtime>";
        vole_panic(msg, file.as_ptr(), file.len(), 0);
    }
    if a == i128::MIN && b == -1 {
        let msg = RcString::new("integer overflow in division");
        let file = b"<runtime>";
        vole_panic(msg, file.as_ptr(), file.len(), 0);
    }
    a / b
}

/// Signed 128-bit integer remainder.
///
/// See `vole_i128_sdiv` for why this is a runtime helper.
/// Panics on division by zero or overflow (i128::MIN % -1).
#[unsafe(no_mangle)]
pub extern "C" fn vole_i128_srem(a: i128, b: i128) -> i128 {
    if b == 0 {
        let msg = RcString::new("division by zero");
        let file = b"<runtime>";
        vole_panic(msg, file.as_ptr(), file.len(), 0);
    }
    if a == i128::MIN && b == -1 {
        let msg = RcString::new("integer overflow in division");
        let file = b"<runtime>";
        vole_panic(msg, file.as_ptr(), file.len(), 0);
    }
    a % b
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_add(a: i128, b: i128) -> i128 {
    f64_to_f128_bits(f128_bits_to_f64(a) + f128_bits_to_f64(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_sub(a: i128, b: i128) -> i128 {
    f64_to_f128_bits(f128_bits_to_f64(a) - f128_bits_to_f64(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_mul(a: i128, b: i128) -> i128 {
    f64_to_f128_bits(f128_bits_to_f64(a) * f128_bits_to_f64(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_div(a: i128, b: i128) -> i128 {
    f64_to_f128_bits(f128_bits_to_f64(a) / f128_bits_to_f64(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_rem(a: i128, b: i128) -> i128 {
    f64_to_f128_bits(f128_bits_to_f64(a) % f128_bits_to_f64(b))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_neg(a: i128) -> i128 {
    f64_to_f128_bits(-f128_bits_to_f64(a))
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_eq(a: i128, b: i128) -> i8 {
    (f128_bits_to_f64(a) == f128_bits_to_f64(b)) as i8
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_lt(a: i128, b: i128) -> i8 {
    (f128_bits_to_f64(a) < f128_bits_to_f64(b)) as i8
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_le(a: i128, b: i128) -> i8 {
    (f128_bits_to_f64(a) <= f128_bits_to_f64(b)) as i8
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_gt(a: i128, b: i128) -> i8 {
    (f128_bits_to_f64(a) > f128_bits_to_f64(b)) as i8
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_ge(a: i128, b: i128) -> i8 {
    (f128_bits_to_f64(a) >= f128_bits_to_f64(b)) as i8
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f64_to_f128(value: f64) -> i128 {
    f64_to_f128_bits(value)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f32_to_f128(value: f32) -> i128 {
    f64_to_f128_bits(value as f64)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_i64_to_f128(value: i64) -> i128 {
    f64_to_f128_bits(value as f64)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_i128_to_f128(value: i128) -> i128 {
    f64_to_f128_bits(value as f64)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_to_f64(value: i128) -> f64 {
    f128_bits_to_f64(value)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_to_f32(value: i128) -> f32 {
    f128_bits_to_f64(value) as f32
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_to_i64(value: i128) -> i64 {
    f128_bits_to_f64(value) as i64
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_f128_to_i128(value: i128) -> i128 {
    f128_bits_to_f64(value) as i128
}

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

/// Concatenate two strings, returning a new RC string with refcount 1.
///
/// Null pointers are treated as empty strings (nil-propagation): `nil + "x"`
/// produces `"x"`, and `nil + nil` produces `""`.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
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
#[expect(clippy::not_unsafe_ptr_arg_deref)]
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
    let mut buf = [0u8; 4];
    let s = (c as char).encode_utf8(&mut buf);
    write_stdout(s);
}

/// Panic with a message - prints to stderr and exits with code 1.
/// If a test jmp_buf is set (unit tests or capture mode), uses longjmp to escape.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_panic(
    msg: *const RcString,
    file: *const u8,
    file_len: usize,
    line: u32,
) -> ! {
    // Extract the message into an owned String so we can free the RcString
    // before diverging (longjmp or exit). msg_str borrows from the RcString,
    // so we must copy it first.
    let msg_owned = unsafe {
        if msg.is_null() {
            String::new()
        } else {
            (*msg).as_str().to_string()
        }
    };

    // Free the message RcString before we diverge
    if !msg.is_null() {
        crate::value::rc_dec(msg as *mut u8);
    }

    let file_str = unsafe {
        if file.is_null() || file_len == 0 {
            "<unknown>"
        } else {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(file, file_len))
        }
    };

    writeln_stderr(&format!("panic: {}", msg_owned));
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

// =============================================================================
// Array FFI functions
// =============================================================================
//
// Unlike instance field access (where the JIT statically knows field indices),
// array indices come from user expressions and must be bounds-checked at
// runtime. Out-of-bounds access triggers a Vole panic via the longjmp error
// path, which unwinds to the test harness or exits the process.

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

/// Allocate a new empty array. Returns a non-null pointer with refcount 1.
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_new() -> *mut RcArray {
    RcArray::new()
}

/// Allocate a new empty array with pre-allocated capacity. Returns non-null with refcount 1.
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_with_capacity(capacity: usize) -> *mut RcArray {
    RcArray::with_capacity(capacity)
}

/// Push a tagged value onto the array. The JIT guarantees `arr` is a valid array pointer.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_array_push(arr: *mut RcArray, tag: u64, value: u64) {
    unsafe {
        RcArray::push(arr, TaggedValue { tag, value });
    }
}

/// Get the type tag of an array element. Returns 0 for null arrays.
/// Panics with a Vole error on out-of-bounds index (user-facing bounds check).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
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

/// Get the value of an array element. Returns 0 for null arrays.
/// Panics with a Vole error on out-of-bounds index (user-facing bounds check).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
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

/// Set an array element by index. No-ops for null arrays.
/// Panics with a Vole error on out-of-bounds index (user-facing bounds check).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
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

/// Get the length of an array. Returns 0 for null arrays (nil-propagation).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_array_len(arr: *const RcArray) -> usize {
    if arr.is_null() {
        return 0;
    }
    unsafe { RcArray::len(arr) }
}

/// Increment array reference count. Null is a no-op (delegated to `rc_inc`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_inc(ptr: *mut RcArray) {
    crate::value::rc_inc(ptr as *mut u8);
}

/// Decrement array reference count. Frees the array when count reaches zero.
/// Null is a no-op (delegated to `rc_dec`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_dec(ptr: *mut RcArray) {
    crate::value::rc_dec(ptr as *mut u8);
}

/// Create a new array of `count` elements, all set to the given tagged value.
/// Each slot gets its own RC reference (incremented for every slot).
/// The caller is responsible for managing the original value's RC lifecycle.
/// Panics on negative count.
#[unsafe(no_mangle)]
pub extern "C" fn vole_array_filled(count: i64, tag: u64, value: u64) -> *mut RcArray {
    if count < 0 {
        let msg = RcString::new(&format!(
            "Array.filled: count must be non-negative, got {}",
            count
        ));
        let file = b"<runtime>";
        vole_panic(msg, file.as_ptr(), file.len(), 0);
    }
    let n = count as usize;
    let arr = RcArray::with_capacity(n);
    let tv = TaggedValue { tag, value };
    unsafe {
        if tag == RuntimeTypeId::UnionHeap as u64 && value != 0 {
            // Union heap buffers: each slot needs its own clone of the buffer
            // (with rc_inc on the payload if RC). Sharing the same pointer
            // would cause double-free on array drop.
            for i in 0..n {
                let cloned_ptr = clone_union_heap_buffer(value as *const u8);
                std::ptr::write(
                    (*arr).data.add(i),
                    TaggedValue {
                        tag,
                        value: cloned_ptr as u64,
                    },
                );
            }
            // The source union heap buffer is no longer needed after cloning.
            union_heap_cleanup(value as *mut u8);
        } else {
            for i in 0..n {
                tv.rc_inc_if_needed();
                std::ptr::write((*arr).data.add(i), tv);
            }
        }
        (*arr).len = n;
    }
    arr
}

/// Clone a union heap buffer (16 bytes), incrementing the RC payload if present.
///
/// # Safety
/// `src` must point to a valid union heap buffer: `[tag: i8, is_rc: i8, pad(6), payload: i64]`.
unsafe fn clone_union_heap_buffer(src: *const u8) -> *mut u8 {
    unsafe {
        const UNION_HEAP_LAYOUT: Layout = match Layout::from_size_align(16, 8) {
            Ok(l) => l,
            Err(_) => panic!("union heap layout"),
        };
        let dst = std::alloc::alloc(UNION_HEAP_LAYOUT);
        if dst.is_null() {
            std::alloc::handle_alloc_error(UNION_HEAP_LAYOUT);
        }
        std::ptr::copy_nonoverlapping(src, dst, 16);
        let is_rc = *dst.add(1);
        if is_rc != 0 {
            let payload = *(dst.add(8) as *const u64);
            if payload != 0 {
                crate::value::rc_inc(payload as *mut u8);
            }
        }
        dst
    }
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

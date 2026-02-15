// src/runtime/buffer.rs
//! Reference-counted byte buffer for raw binary data.
//!
//! Provides a growable byte array with RC lifetime management,
//! following the same patterns as RcArray and RcString.

use crate::alloc_track;
use crate::string::RcString;
use crate::value::{RcHeader, RuntimeTypeId, rc_dec, rc_inc};
use std::alloc::{Layout, alloc, dealloc, realloc};
use std::ptr;

/// Reference-counted dynamic byte buffer
#[repr(C)]
pub struct RcBuffer {
    pub header: RcHeader,
    pub len: usize,
    pub capacity: usize,
    pub data: *mut u8,
}

impl RcBuffer {
    /// Allocate a new empty buffer
    pub fn new() -> *mut Self {
        Self::with_capacity(0)
    }

    /// Allocate with initial capacity
    pub fn with_capacity(capacity: usize) -> *mut Self {
        let layout = Layout::new::<RcBuffer>();

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let data = if capacity > 0 {
                let data_layout = Layout::array::<u8>(capacity)
                    .expect("buffer capacity exceeds maximum allocation size");
                alloc(data_layout)
            } else {
                ptr::null_mut()
            };

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Buffer as u32, buffer_drop),
            );
            ptr::write(&mut (*ptr).len, 0);
            ptr::write(&mut (*ptr).capacity, capacity);
            ptr::write(&mut (*ptr).data, data);

            alloc_track::track_alloc(RuntimeTypeId::Buffer as u32);
            ptr
        }
    }

    /// Push a byte onto the buffer
    ///
    /// # Safety
    /// `buf` must be a valid pointer to an initialized `RcBuffer`
    pub unsafe fn push(buf: *mut Self, byte: u8) {
        unsafe {
            let len = (*buf).len;
            let cap = (*buf).capacity;

            if len >= cap {
                Self::grow(buf);
            }

            ptr::write((*buf).data.add(len), byte);
            (*buf).len = len + 1;
        }
    }

    /// Grow the buffer capacity by doubling
    ///
    /// # Safety
    /// `buf` must be a valid pointer to an initialized `RcBuffer`
    unsafe fn grow(buf: *mut Self) {
        unsafe {
            let old_cap = (*buf).capacity;
            let new_cap = if old_cap == 0 { 8 } else { old_cap * 2 };
            Self::resize_to(buf, new_cap);
        }
    }

    /// Ensure the buffer has at least `min_cap` capacity, growing as needed.
    ///
    /// # Safety
    /// `buf` must be a valid pointer to an initialized `RcBuffer`
    unsafe fn ensure_capacity(buf: *mut Self, min_cap: usize) {
        unsafe {
            let mut cap = (*buf).capacity;
            if cap >= min_cap {
                return;
            }
            if cap == 0 {
                cap = 8;
            }
            while cap < min_cap {
                cap *= 2;
            }
            Self::resize_to(buf, cap);
        }
    }

    /// Resize the data buffer to exactly `new_cap`.
    ///
    /// # Safety
    /// `buf` must be a valid pointer to an initialized `RcBuffer`.
    /// `new_cap` must be greater than the current capacity.
    unsafe fn resize_to(buf: *mut Self, new_cap: usize) {
        unsafe {
            let old_cap = (*buf).capacity;

            let new_data = if old_cap == 0 {
                let layout = Layout::array::<u8>(new_cap)
                    .expect("buffer capacity exceeds maximum allocation size");
                alloc(layout)
            } else {
                let old_layout = Layout::array::<u8>(old_cap)
                    .expect("buffer capacity exceeds maximum allocation size");
                let new_layout = Layout::array::<u8>(new_cap)
                    .expect("buffer capacity exceeds maximum allocation size");
                realloc((*buf).data, old_layout, new_layout.size())
            };

            if new_data.is_null() {
                let layout = Layout::array::<u8>(new_cap)
                    .expect("buffer capacity exceeds maximum allocation size");
                std::alloc::handle_alloc_error(layout);
            }

            (*buf).data = new_data;
            (*buf).capacity = new_cap;
        }
    }

    /// Get buffer length
    ///
    /// # Safety
    /// `buf` must be a valid pointer to an initialized `RcBuffer`
    #[inline]
    pub unsafe fn len(buf: *const Self) -> usize {
        unsafe { (*buf).len }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcBuffer`
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        rc_inc(ptr as *mut u8);
    }

    /// Decrement reference count and free if zero (via unified rc_dec + drop_fn)
    ///
    /// # Safety
    /// `ptr` must be null or a valid pointer to an initialized `RcBuffer`
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }
}

/// Drop function for RcBuffer, called by rc_dec when refcount reaches zero.
/// Frees the data buffer and deallocates the RcBuffer struct itself.
///
/// # Safety
/// `ptr` must point to a valid `RcBuffer` allocation with refcount already at zero.
unsafe extern "C" fn buffer_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(RuntimeTypeId::Buffer as u32);
    unsafe {
        let buf = ptr as *mut RcBuffer;
        let cap = (*buf).capacity;

        if cap > 0 && !(*buf).data.is_null() {
            let data_layout =
                Layout::array::<u8>(cap).expect("buffer capacity exceeds maximum allocation size");
            dealloc((*buf).data, data_layout);
        }

        let layout = Layout::new::<RcBuffer>();
        dealloc(ptr, layout);
    }
}

// =============================================================================
// FFI functions for JIT-compiled code
// =============================================================================
//
// Safety contract: the JIT guarantees pointer validity for all arguments.
// Buffer pointers are either null or valid RcBuffer allocations.
//
// Null handling: functions that read from buffer pointers return zero/null
// for null inputs, supporting nil-propagation. RC operations delegate to
// rc_inc/rc_dec which handle null.

/// Create a new empty buffer. Returns non-null with refcount 1.
#[unsafe(no_mangle)]
pub extern "C" fn buffer_new() -> *mut RcBuffer {
    RcBuffer::new()
}

/// Create a new buffer with the given capacity. Returns non-null with refcount 1.
#[unsafe(no_mangle)]
pub extern "C" fn buffer_with_capacity(cap: i64) -> *mut RcBuffer {
    let cap = if cap < 0 { 0 } else { cap as usize };
    RcBuffer::with_capacity(cap)
}

/// Get the length of a buffer in bytes. Returns 0 for null pointers.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_len(buf: *mut RcBuffer) -> i64 {
    if buf.is_null() {
        return 0;
    }
    unsafe { (*buf).len as i64 }
}

/// Get the capacity of a buffer in bytes. Returns 0 for null pointers.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_capacity(buf: *mut RcBuffer) -> i64 {
    if buf.is_null() {
        return 0;
    }
    unsafe { (*buf).capacity as i64 }
}

/// Append a single byte to the buffer. No-op for null pointers.
/// The byte value is masked to the low 8 bits.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_append_byte(buf: *mut RcBuffer, byte: i64) {
    if buf.is_null() {
        return;
    }
    unsafe {
        RcBuffer::push(buf, byte as u8);
    }
}

/// Append all bytes from `src` to `dest`. No-op if either pointer is null.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_append(dest: *mut RcBuffer, src: *mut RcBuffer) {
    if dest.is_null() || src.is_null() {
        return;
    }
    unsafe {
        let src_len = (*src).len;
        if src_len == 0 {
            return;
        }
        // Ensure dest has enough capacity
        let dest_len = (*dest).len;
        let needed = dest_len + src_len;
        RcBuffer::ensure_capacity(dest, needed);
        ptr::copy_nonoverlapping((*src).data, (*dest).data.add(dest_len), src_len);
        (*dest).len = needed;
    }
}

/// Get a byte at the given index. Returns -1 for null or out-of-bounds.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_get(buf: *mut RcBuffer, index: i64) -> i64 {
    if buf.is_null() || index < 0 {
        return -1;
    }
    unsafe {
        let idx = index as usize;
        if idx >= (*buf).len {
            return -1;
        }
        *(*buf).data.add(idx) as i64
    }
}

/// Set a byte at the given index. No-op for null or out-of-bounds.
/// The value is masked to the low 8 bits.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_set(buf: *mut RcBuffer, index: i64, value: i64) {
    if buf.is_null() || index < 0 {
        return;
    }
    unsafe {
        let idx = index as usize;
        if idx >= (*buf).len {
            return;
        }
        *(*buf).data.add(idx) = value as u8;
    }
}

/// Create a new buffer containing a slice of the source buffer.
/// Returns an empty buffer for null pointers or invalid ranges.
/// Clamps indices to valid bounds.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_slice(buf: *mut RcBuffer, start: i64, end: i64) -> *mut RcBuffer {
    if buf.is_null() {
        return RcBuffer::new();
    }
    unsafe {
        let len = (*buf).len;
        let start_idx = if start < 0 {
            0
        } else {
            (start as usize).min(len)
        };
        let end_idx = if end < 0 {
            len
        } else {
            (end as usize).min(len)
        };

        if start_idx >= end_idx {
            return RcBuffer::new();
        }

        let slice_len = end_idx - start_idx;
        let new_buf = RcBuffer::with_capacity(slice_len);
        ptr::copy_nonoverlapping((*buf).data.add(start_idx), (*new_buf).data, slice_len);
        (*new_buf).len = slice_len;
        new_buf
    }
}

/// Convert buffer contents to a UTF-8 string.
/// Returns an empty string for null pointers.
/// Invalid UTF-8 bytes are replaced with the Unicode replacement character.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_to_string(buf: *mut RcBuffer) -> *mut RcString {
    if buf.is_null() {
        return RcString::new("");
    }
    unsafe {
        let len = (*buf).len;
        if len == 0 {
            return RcString::new("");
        }
        let bytes = std::slice::from_raw_parts((*buf).data, len);
        let s = String::from_utf8_lossy(bytes);
        RcString::new(&s)
    }
}

/// Create a buffer from a string's UTF-8 bytes.
/// Returns an empty buffer for null pointers.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_from_string(s: *mut RcString) -> *mut RcBuffer {
    if s.is_null() {
        return RcBuffer::new();
    }
    unsafe {
        let data = (*s).data();
        let len = data.len();
        let buf = RcBuffer::with_capacity(len);
        if len > 0 {
            ptr::copy_nonoverlapping(data.as_ptr(), (*buf).data, len);
        }
        (*buf).len = len;
        buf
    }
}

/// Clear the buffer, setting length to 0 without freeing capacity.
/// No-op for null pointers.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_clear(buf: *mut RcBuffer) {
    if buf.is_null() {
        return;
    }
    unsafe {
        (*buf).len = 0;
    }
}

/// Compare two buffers for equality. Returns 1 if equal, 0 otherwise.
/// Two null pointers are considered equal; a null and non-null are unequal.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn buffer_equals(a: *mut RcBuffer, b: *mut RcBuffer) -> i64 {
    if a.is_null() && b.is_null() {
        return 1;
    }
    if a.is_null() || b.is_null() {
        return 0;
    }
    unsafe {
        let a_len = (*a).len;
        let b_len = (*b).len;
        if a_len != b_len {
            return 0;
        }
        if a_len == 0 {
            return 1;
        }
        let a_slice = std::slice::from_raw_parts((*a).data, a_len);
        let b_slice = std::slice::from_raw_parts((*b).data, b_len);
        if a_slice == b_slice { 1 } else { 0 }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn create_empty_buffer() {
        let buf = RcBuffer::new();
        unsafe {
            assert_eq!((*buf).len, 0);
            assert_eq!((*buf).capacity, 0);
            assert!((*buf).data.is_null());
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn create_buffer_with_capacity() {
        let buf = RcBuffer::with_capacity(16);
        unsafe {
            assert_eq!((*buf).len, 0);
            assert_eq!((*buf).capacity, 16);
            assert!(!(*buf).data.is_null());
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn push_and_read_bytes() {
        let buf = RcBuffer::new();
        unsafe {
            RcBuffer::push(buf, 0x41); // 'A'
            RcBuffer::push(buf, 0x42); // 'B'
            RcBuffer::push(buf, 0x43); // 'C'

            assert_eq!(RcBuffer::len(buf), 3);
            assert_eq!(*(*buf).data.add(0), 0x41);
            assert_eq!(*(*buf).data.add(1), 0x42);
            assert_eq!(*(*buf).data.add(2), 0x43);

            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn capacity_growth() {
        let buf = RcBuffer::new();
        unsafe {
            // Push enough bytes to trigger multiple growths
            for i in 0..100u8 {
                RcBuffer::push(buf, i);
            }
            assert_eq!(RcBuffer::len(buf), 100);
            assert!((*buf).capacity >= 100);

            // Verify all bytes were written correctly
            for i in 0..100u8 {
                assert_eq!(*(*buf).data.add(i as usize), i);
            }

            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ref_counting() {
        let buf = RcBuffer::new();
        unsafe {
            RcBuffer::push(buf, 0xFF);

            assert_eq!((*buf).header.ref_count.load(Ordering::Relaxed), 1);

            RcBuffer::inc_ref(buf);
            assert_eq!((*buf).header.ref_count.load(Ordering::Relaxed), 2);

            RcBuffer::dec_ref(buf);
            assert_eq!((*buf).header.ref_count.load(Ordering::Relaxed), 1);

            // Final dec frees the buffer
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ffi_buffer_new_and_len() {
        let buf = buffer_new();
        assert_eq!(buffer_len(buf), 0);
        assert_eq!(buffer_capacity(buf), 0);
        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_with_capacity() {
        let buf = buffer_with_capacity(32);
        assert_eq!(buffer_len(buf), 0);
        assert_eq!(buffer_capacity(buf), 32);
        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_with_negative_capacity() {
        let buf = buffer_with_capacity(-5);
        assert_eq!(buffer_len(buf), 0);
        assert_eq!(buffer_capacity(buf), 0);
        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_append_byte_and_get() {
        let buf = buffer_new();
        buffer_append_byte(buf, 10);
        buffer_append_byte(buf, 20);
        buffer_append_byte(buf, 255);

        assert_eq!(buffer_len(buf), 3);
        assert_eq!(buffer_get(buf, 0), 10);
        assert_eq!(buffer_get(buf, 1), 20);
        assert_eq!(buffer_get(buf, 2), 255);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_get_out_of_bounds() {
        let buf = buffer_new();
        buffer_append_byte(buf, 42);

        assert_eq!(buffer_get(buf, -1), -1);
        assert_eq!(buffer_get(buf, 1), -1);
        assert_eq!(buffer_get(buf, 100), -1);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_set() {
        let buf = buffer_new();
        buffer_append_byte(buf, 0);
        buffer_append_byte(buf, 0);
        buffer_append_byte(buf, 0);

        buffer_set(buf, 0, 10);
        buffer_set(buf, 1, 20);
        buffer_set(buf, 2, 30);

        assert_eq!(buffer_get(buf, 0), 10);
        assert_eq!(buffer_get(buf, 1), 20);
        assert_eq!(buffer_get(buf, 2), 30);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_set_out_of_bounds() {
        let buf = buffer_new();
        buffer_append_byte(buf, 42);

        // Out of bounds set is a no-op
        buffer_set(buf, -1, 99);
        buffer_set(buf, 1, 99);
        buffer_set(buf, 100, 99);

        assert_eq!(buffer_get(buf, 0), 42);
        assert_eq!(buffer_len(buf), 1);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_append() {
        let a = buffer_new();
        buffer_append_byte(a, 1);
        buffer_append_byte(a, 2);

        let b = buffer_new();
        buffer_append_byte(b, 3);
        buffer_append_byte(b, 4);

        buffer_append(a, b);

        assert_eq!(buffer_len(a), 4);
        assert_eq!(buffer_get(a, 0), 1);
        assert_eq!(buffer_get(a, 1), 2);
        assert_eq!(buffer_get(a, 2), 3);
        assert_eq!(buffer_get(a, 3), 4);

        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_append_empty_src() {
        let a = buffer_new();
        buffer_append_byte(a, 1);

        let b = buffer_new();
        buffer_append(a, b);

        assert_eq!(buffer_len(a), 1);
        assert_eq!(buffer_get(a, 0), 1);

        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_slice_basic() {
        let buf = buffer_new();
        for i in 0..10u8 {
            buffer_append_byte(buf, i as i64);
        }

        let sliced = buffer_slice(buf, 2, 5);
        assert_eq!(buffer_len(sliced), 3);
        assert_eq!(buffer_get(sliced, 0), 2);
        assert_eq!(buffer_get(sliced, 1), 3);
        assert_eq!(buffer_get(sliced, 2), 4);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }

    #[test]
    fn ffi_buffer_slice_to_end() {
        let buf = buffer_new();
        for i in 0..5u8 {
            buffer_append_byte(buf, i as i64);
        }

        let sliced = buffer_slice(buf, 3, -1);
        assert_eq!(buffer_len(sliced), 2);
        assert_eq!(buffer_get(sliced, 0), 3);
        assert_eq!(buffer_get(sliced, 1), 4);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }

    #[test]
    fn ffi_buffer_slice_invalid_range() {
        let buf = buffer_new();
        buffer_append_byte(buf, 1);

        let sliced = buffer_slice(buf, 5, 3);
        assert_eq!(buffer_len(sliced), 0);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }

    #[test]
    fn ffi_buffer_slice_clamped() {
        let buf = buffer_new();
        buffer_append_byte(buf, 1);
        buffer_append_byte(buf, 2);
        buffer_append_byte(buf, 3);

        // End beyond length is clamped to length
        let sliced = buffer_slice(buf, 1, 100);
        assert_eq!(buffer_len(sliced), 2);
        assert_eq!(buffer_get(sliced, 0), 2);
        assert_eq!(buffer_get(sliced, 1), 3);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }

    #[test]
    fn ffi_buffer_to_string_ascii() {
        let buf = buffer_new();
        buffer_append_byte(buf, b'h' as i64);
        buffer_append_byte(buf, b'e' as i64);
        buffer_append_byte(buf, b'l' as i64);
        buffer_append_byte(buf, b'l' as i64);
        buffer_append_byte(buf, b'o' as i64);

        let s = buffer_to_string(buf);
        unsafe {
            assert_eq!((*s).as_str(), "hello");
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ffi_buffer_to_string_utf8() {
        let buf = buffer_new();
        // UTF-8 encoding of "cafe" with accented e (0xC3 0xA9)
        for &byte in b"caf\xc3\xa9" {
            buffer_append_byte(buf, byte as i64);
        }

        let s = buffer_to_string(buf);
        unsafe {
            assert_eq!((*s).as_str(), "caf\u{e9}");
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ffi_buffer_to_string_invalid_utf8() {
        let buf = buffer_new();
        buffer_append_byte(buf, 0xFF);
        buffer_append_byte(buf, 0xFE);

        let s = buffer_to_string(buf);
        unsafe {
            // Invalid bytes become replacement characters
            let text = (*s).as_str();
            assert!(text.contains('\u{FFFD}'));
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ffi_buffer_to_string_empty() {
        let buf = buffer_new();
        let s = buffer_to_string(buf);
        unsafe {
            assert_eq!((*s).as_str(), "");
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ffi_buffer_from_string() {
        let s = RcString::new("hello");
        let buf = buffer_from_string(s);

        assert_eq!(buffer_len(buf), 5);
        assert_eq!(buffer_get(buf, 0), b'h' as i64);
        assert_eq!(buffer_get(buf, 1), b'e' as i64);
        assert_eq!(buffer_get(buf, 2), b'l' as i64);
        assert_eq!(buffer_get(buf, 3), b'l' as i64);
        assert_eq!(buffer_get(buf, 4), b'o' as i64);

        unsafe {
            RcString::dec_ref(s);
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ffi_buffer_from_string_utf8() {
        let s = RcString::new("caf\u{e9}");
        let buf = buffer_from_string(s);

        // "cafe" with accent is 5 bytes in UTF-8
        assert_eq!(buffer_len(buf), 5);

        unsafe {
            RcString::dec_ref(s);
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ffi_string_round_trip() {
        let original = RcString::new("hello world");
        let buf = buffer_from_string(original);
        let restored = buffer_to_string(buf);

        unsafe {
            assert_eq!((*restored).as_str(), "hello world");
            RcString::dec_ref(original);
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(restored);
        }
    }

    #[test]
    fn ffi_string_round_trip_utf8() {
        let original = RcString::new("\u{1F600} emoji test \u{2764}");
        let buf = buffer_from_string(original);
        let restored = buffer_to_string(buf);

        unsafe {
            assert_eq!((*restored).as_str(), "\u{1F600} emoji test \u{2764}");
            RcString::dec_ref(original);
            RcBuffer::dec_ref(buf);
            RcString::dec_ref(restored);
        }
    }

    #[test]
    fn ffi_buffer_clear() {
        let buf = buffer_new();
        buffer_append_byte(buf, 1);
        buffer_append_byte(buf, 2);
        buffer_append_byte(buf, 3);

        assert_eq!(buffer_len(buf), 3);
        let cap_before = buffer_capacity(buf);

        buffer_clear(buf);

        assert_eq!(buffer_len(buf), 0);
        // Capacity should be preserved
        assert_eq!(buffer_capacity(buf), cap_before);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_equals_same_content() {
        let a = buffer_new();
        let b = buffer_new();

        buffer_append_byte(a, 1);
        buffer_append_byte(a, 2);
        buffer_append_byte(a, 3);

        buffer_append_byte(b, 1);
        buffer_append_byte(b, 2);
        buffer_append_byte(b, 3);

        assert_eq!(buffer_equals(a, b), 1);

        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_equals_different_content() {
        let a = buffer_new();
        let b = buffer_new();

        buffer_append_byte(a, 1);
        buffer_append_byte(a, 2);

        buffer_append_byte(b, 1);
        buffer_append_byte(b, 3);

        assert_eq!(buffer_equals(a, b), 0);

        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_equals_different_length() {
        let a = buffer_new();
        let b = buffer_new();

        buffer_append_byte(a, 1);
        buffer_append_byte(a, 2);

        buffer_append_byte(b, 1);

        assert_eq!(buffer_equals(a, b), 0);

        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_equals_both_empty() {
        let a = buffer_new();
        let b = buffer_new();
        assert_eq!(buffer_equals(a, b), 1);
        unsafe {
            RcBuffer::dec_ref(a);
            RcBuffer::dec_ref(b);
        }
    }

    #[test]
    fn ffi_buffer_equals_null_handling() {
        let buf = buffer_new();
        buffer_append_byte(buf, 1);

        assert_eq!(buffer_equals(ptr::null_mut(), ptr::null_mut()), 1);
        assert_eq!(buffer_equals(buf, ptr::null_mut()), 0);
        assert_eq!(buffer_equals(ptr::null_mut(), buf), 0);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_null_handling_len() {
        assert_eq!(buffer_len(ptr::null_mut()), 0);
    }

    #[test]
    fn ffi_null_handling_capacity() {
        assert_eq!(buffer_capacity(ptr::null_mut()), 0);
    }

    #[test]
    fn ffi_null_handling_append_byte() {
        // Should not crash
        buffer_append_byte(ptr::null_mut(), 42);
    }

    #[test]
    fn ffi_null_handling_append() {
        let buf = buffer_new();
        // Should not crash
        buffer_append(buf, ptr::null_mut());
        buffer_append(ptr::null_mut(), buf);
        buffer_append(ptr::null_mut(), ptr::null_mut());

        assert_eq!(buffer_len(buf), 0);
        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_null_handling_get() {
        assert_eq!(buffer_get(ptr::null_mut(), 0), -1);
    }

    #[test]
    fn ffi_null_handling_set() {
        // Should not crash
        buffer_set(ptr::null_mut(), 0, 42);
    }

    #[test]
    fn ffi_null_handling_slice() {
        let result = buffer_slice(ptr::null_mut(), 0, 5);
        assert_eq!(buffer_len(result), 0);
        unsafe { RcBuffer::dec_ref(result) };
    }

    #[test]
    fn ffi_null_handling_to_string() {
        let s = buffer_to_string(ptr::null_mut());
        unsafe {
            assert_eq!((*s).as_str(), "");
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ffi_null_handling_from_string() {
        let buf = buffer_from_string(ptr::null_mut());
        assert_eq!(buffer_len(buf), 0);
        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_null_handling_clear() {
        // Should not crash
        buffer_clear(ptr::null_mut());
    }

    #[test]
    fn ffi_append_byte_masks_to_u8() {
        let buf = buffer_new();
        // 256 should wrap to 0, 257 to 1
        buffer_append_byte(buf, 256);
        buffer_append_byte(buf, 257);
        buffer_append_byte(buf, -1);

        assert_eq!(buffer_get(buf, 0), 0);
        assert_eq!(buffer_get(buf, 1), 1);
        assert_eq!(buffer_get(buf, 2), 255);

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn ffi_buffer_set_masks_to_u8() {
        let buf = buffer_new();
        buffer_append_byte(buf, 0);

        buffer_set(buf, 0, 300);
        assert_eq!(buffer_get(buf, 0), 44); // 300 & 0xFF = 44

        buffer_set(buf, 0, -1);
        assert_eq!(buffer_get(buf, 0), 255); // -1 as u8 = 255

        unsafe { RcBuffer::dec_ref(buf) };
    }

    #[test]
    fn header_fields_correct() {
        let buf = RcBuffer::new();
        unsafe {
            assert_eq!((*buf).header.type_id, RuntimeTypeId::Buffer as u32);
            assert_eq!((*buf).header.ref_count.load(Ordering::Relaxed), 1);
            assert!((*buf).header.drop_fn.is_some());
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ffi_buffer_from_string_empty() {
        let s = RcString::new("");
        let buf = buffer_from_string(s);
        assert_eq!(buffer_len(buf), 0);
        unsafe {
            RcString::dec_ref(s);
            RcBuffer::dec_ref(buf);
        }
    }

    #[test]
    fn ffi_buffer_slice_full() {
        let buf = buffer_new();
        buffer_append_byte(buf, 10);
        buffer_append_byte(buf, 20);
        buffer_append_byte(buf, 30);

        let sliced = buffer_slice(buf, 0, -1);
        assert_eq!(buffer_len(sliced), 3);
        assert_eq!(buffer_get(sliced, 0), 10);
        assert_eq!(buffer_get(sliced, 1), 20);
        assert_eq!(buffer_get(sliced, 2), 30);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }

    #[test]
    fn ffi_buffer_slice_negative_start() {
        let buf = buffer_new();
        buffer_append_byte(buf, 1);
        buffer_append_byte(buf, 2);
        buffer_append_byte(buf, 3);

        // Negative start is clamped to 0
        let sliced = buffer_slice(buf, -5, 2);
        assert_eq!(buffer_len(sliced), 2);
        assert_eq!(buffer_get(sliced, 0), 1);
        assert_eq!(buffer_get(sliced, 1), 2);

        unsafe {
            RcBuffer::dec_ref(buf);
            RcBuffer::dec_ref(sliced);
        }
    }
}

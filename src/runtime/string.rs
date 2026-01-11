// src/runtime/string.rs

use crate::runtime::value::{RcHeader, TYPE_STRING};
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;
use std::slice;
use std::str;

/// Reference-counted string
#[repr(C)]
pub struct RcString {
    pub header: RcHeader,
    pub len: usize,
    pub hash: u64,
    // Data follows inline
}

impl RcString {
    /// Allocate a new RcString from a string slice
    pub fn new(s: &str) -> *mut Self {
        let len = s.len();
        let hash = Self::compute_hash(s.as_bytes());

        // Calculate layout: header + data
        let layout = Self::layout_for_len(len);

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // Initialize header
            ptr::write(&mut (*ptr).header, RcHeader::new(TYPE_STRING));
            ptr::write(&mut (*ptr).len, len);
            ptr::write(&mut (*ptr).hash, hash);

            // Copy string data
            let data_ptr = (ptr as *mut u8).add(size_of::<RcString>());
            ptr::copy_nonoverlapping(s.as_ptr(), data_ptr, len);

            ptr
        }
    }

    fn layout_for_len(len: usize) -> Layout {
        let size = size_of::<RcString>() + len;
        let align = align_of::<RcString>();
        Layout::from_size_align(size, align).unwrap()
    }

    fn compute_hash(bytes: &[u8]) -> u64 {
        // Simple FNV-1a hash
        let mut hash: u64 = 0xcbf29ce484222325;
        for &byte in bytes {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(0x100000001b3);
        }
        hash
    }

    /// Get the string data
    ///
    /// # Safety
    /// The caller must ensure `self` points to a valid, properly initialized `RcString`.
    pub unsafe fn data(&self) -> &[u8] {
        unsafe {
            let data_ptr = (self as *const Self as *const u8).add(size_of::<RcString>());
            slice::from_raw_parts(data_ptr, self.len)
        }
    }

    /// Get as str
    ///
    /// # Safety
    /// The caller must ensure `self` points to a valid, properly initialized `RcString`
    /// containing valid UTF-8 data.
    #[inline]
    pub unsafe fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.data()) }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcString`.
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        if !ptr.is_null() {
            unsafe { (*ptr).header.inc() };
        }
    }

    /// Decrement reference count and free if zero
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcString`.
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        if ptr.is_null() {
            return;
        }

        unsafe {
            let prev = (*ptr).header.dec();
            if prev == 1 {
                // Last reference, deallocate
                let len = (*ptr).len;
                let layout = Self::layout_for_len(len);
                dealloc(ptr as *mut u8, layout);
            }
        }
    }
}

// Functions exposed to JIT-compiled code
// These functions are called from JIT-generated code which is responsible for
// ensuring pointer validity.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_new(data: *const u8, len: usize) -> *mut RcString {
    let s = unsafe {
        let slice = slice::from_raw_parts(data, len);
        str::from_utf8_unchecked(slice)
    };
    RcString::new(s)
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_inc(ptr: *mut RcString) {
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { RcString::inc_ref(ptr) };
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_dec(ptr: *mut RcString) {
    // Safety: Called from JIT code which ensures pointer validity
    unsafe { RcString::dec_ref(ptr) };
}

#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_len(ptr: *const RcString) -> usize {
    if ptr.is_null() {
        return 0;
    }
    // Return character count, not byte count (UTF-8 aware)
    unsafe { (*ptr).as_str().chars().count() }
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_string_data(ptr: *const RcString) -> *const u8 {
    if ptr.is_null() {
        return ptr::null();
    }
    unsafe { (ptr as *const u8).add(size_of::<RcString>()) }
}

/// Compare two strings for equality, returns 1 if equal, 0 otherwise
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_eq(a: *const RcString, b: *const RcString) -> i8 {
    if a.is_null() && b.is_null() {
        return 1;
    }
    if a.is_null() || b.is_null() {
        return 0;
    }
    unsafe {
        let a_str = (*a).as_str();
        let b_str = (*b).as_str();
        if a_str == b_str { 1 } else { 0 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_and_read_string() {
        let s = RcString::new("hello");
        unsafe {
            assert_eq!((*s).len, 5);
            assert_eq!((*s).as_str(), "hello");
            // Safety: s is a valid pointer from RcString::new
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn ref_counting() {
        let s = RcString::new("test");
        unsafe {
            assert_eq!(
                (*s).header
                    .ref_count
                    .load(std::sync::atomic::Ordering::Relaxed),
                1
            );

            // Safety: s is a valid pointer from RcString::new
            RcString::inc_ref(s);
            assert_eq!(
                (*s).header
                    .ref_count
                    .load(std::sync::atomic::Ordering::Relaxed),
                2
            );

            // Safety: s is still valid
            RcString::dec_ref(s);
            assert_eq!(
                (*s).header
                    .ref_count
                    .load(std::sync::atomic::Ordering::Relaxed),
                1
            );

            // Safety: s is still valid, this will free the string
            RcString::dec_ref(s);
        }
    }

    #[test]
    fn extern_c_functions() {
        let data = b"hello";
        let s = vole_string_new(data.as_ptr(), data.len());

        // vole_string_len returns character count, not byte count
        assert_eq!(vole_string_len(s), 5);

        let read_data = vole_string_data(s);
        let read_str = unsafe {
            // For reading the actual bytes, use the raw byte length
            let byte_len = (*s).len;
            let slice = slice::from_raw_parts(read_data, byte_len);
            str::from_utf8_unchecked(slice)
        };
        assert_eq!(read_str, "hello");

        vole_string_dec(s);
    }

    #[test]
    fn string_len_unicode() {
        // "héllo" has 5 characters but 6 bytes
        let data = "héllo";
        let s = vole_string_new(data.as_ptr(), data.len());

        // vole_string_len returns character count
        assert_eq!(vole_string_len(s), 5);

        // But the actual byte storage is 6
        unsafe {
            assert_eq!((*s).len, 6);
        }

        vole_string_dec(s);
    }
}

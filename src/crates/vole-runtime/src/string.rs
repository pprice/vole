// src/runtime/string.rs

use crate::alloc_track;
use crate::value::{RcHeader, TYPE_STRING, rc_dec, rc_inc};
use std::alloc::{Layout, alloc, dealloc};
use std::ptr;
use std::slice;
use std::str;

/// Incremental FNV-1a 64-bit hasher. Allows hashing multiple byte slices
/// sequentially to produce the same result as hashing their concatenation.
pub struct Fnv1aHasher {
    hash: u64,
}

impl Default for Fnv1aHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Fnv1aHasher {
    const OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    pub fn new() -> Self {
        Self {
            hash: Self::OFFSET_BASIS,
        }
    }

    pub fn update(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.hash ^= b as u64;
            self.hash = self.hash.wrapping_mul(Self::PRIME);
        }
    }

    pub fn finish(self) -> u64 {
        self.hash
    }
}

/// FNV-1a hash for string bytes. Used by both runtime allocation and
/// compile-time static string embedding in codegen.
pub fn fnv1a_hash(bytes: &[u8]) -> u64 {
    let mut hasher = Fnv1aHasher::new();
    hasher.update(bytes);
    hasher.finish()
}

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

            // Initialize header with drop_fn for unified rc_dec cleanup
            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(TYPE_STRING, string_drop),
            );
            ptr::write(&mut (*ptr).len, len);
            ptr::write(&mut (*ptr).hash, hash);

            // Copy string data
            let data_ptr = (ptr as *mut u8).add(size_of::<RcString>());
            ptr::copy_nonoverlapping(s.as_ptr(), data_ptr, len);

            alloc_track::track_alloc(TYPE_STRING);
            ptr
        }
    }

    fn layout_for_len(len: usize) -> Layout {
        let size = size_of::<RcString>() + len;
        let align = align_of::<RcString>();
        Layout::from_size_align(size, align).expect("string layout overflow")
    }

    fn compute_hash(bytes: &[u8]) -> u64 {
        fnv1a_hash(bytes)
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

    /// Allocate a new RcString by concatenating two byte slices without an
    /// intermediate String allocation.
    pub fn from_two_parts(a: &[u8], b: &[u8]) -> *mut Self {
        let total_len = a.len() + b.len();

        // Hash both parts sequentially to produce the same result as hashing
        // the concatenated bytes.
        let mut hasher = Fnv1aHasher::new();
        hasher.update(a);
        hasher.update(b);
        let hash = hasher.finish();

        let layout = Self::layout_for_len(total_len);

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(TYPE_STRING, string_drop),
            );
            ptr::write(&mut (*ptr).len, total_len);
            ptr::write(&mut (*ptr).hash, hash);

            let data_ptr = (ptr as *mut u8).add(size_of::<RcString>());
            ptr::copy_nonoverlapping(a.as_ptr(), data_ptr, a.len());
            ptr::copy_nonoverlapping(b.as_ptr(), data_ptr.add(a.len()), b.len());

            alloc_track::track_alloc(TYPE_STRING);
            ptr
        }
    }

    /// Increment reference count
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcString`.
    #[inline]
    pub unsafe fn inc_ref(ptr: *mut Self) {
        rc_inc(ptr as *mut u8);
    }

    /// Decrement reference count and free if zero (via unified rc_dec + drop_fn)
    ///
    /// # Safety
    /// The pointer must be null or point to a valid, properly initialized `RcString`.
    #[inline]
    pub unsafe fn dec_ref(ptr: *mut Self) {
        rc_dec(ptr as *mut u8);
    }
}

/// Drop function for RcString, called by rc_dec when refcount reaches zero.
/// Deallocates the contiguous string allocation (header + inline data).
///
/// # Safety
/// `ptr` must point to a valid `RcString` allocation with refcount already at zero.
unsafe extern "C" fn string_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(TYPE_STRING);
    unsafe {
        let s = ptr as *mut RcString;
        let len = (*s).len;
        let layout = RcString::layout_for_len(len);
        dealloc(ptr, layout);
    }
}

// Functions exposed to JIT-compiled code
// These functions are called from JIT-generated code which is responsible for
// ensuring pointer validity.
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_new(data: *const u8, len: usize) -> *mut RcString {
    let s = unsafe {
        let slice = slice::from_raw_parts(data, len);
        str::from_utf8_unchecked(slice)
    };
    RcString::new(s)
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_string_inc(ptr: *mut RcString) {
    rc_inc(ptr as *mut u8);
}

#[unsafe(no_mangle)]
pub extern "C" fn vole_string_dec(ptr: *mut RcString) {
    rc_dec(ptr as *mut u8);
}

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

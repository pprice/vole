// src/runtime/string.rs

use crate::alloc_track;
use crate::value::{RcHeader, RuntimeTypeId, rc_dec, rc_inc};
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
    pub char_count: usize,
    pub hash: u64,
    // Data follows inline
}

/// Byte offset from the start of an `RcString` allocation to the inline string
/// data that immediately follows the header.
///
/// Because the data payload is an unsized byte tail (not a named struct field),
/// `offset_of!` cannot be used here. Instead we use `size_of::<RcString>()`.
/// This is correct because `u8` has an alignment of 1, so the compiler inserts
/// no padding between the last field of `RcString` and the first byte of data.
///
/// The static assertion below enforces this assumption at compile time.
const RCSTRING_DATA_OFFSET: usize = size_of::<RcString>();

// Verify that u8 (the type of the inline data bytes) has alignment 1, meaning
// no padding is inserted between the RcString header fields and the data tail.
const _: () = assert!(align_of::<u8>() == 1);

impl RcString {
    /// Allocate a new RcString from a string slice
    pub fn new(s: &str) -> *mut Self {
        let len = s.len();
        let char_count = s.chars().count();
        let hash = Self::compute_hash(s.as_bytes());

        // Calculate layout: header + data
        let layout = Self::layout_for_len(len);

        // SAFETY: Layout is valid (computed from str len + header size). We
        // initialize every field via ptr::write before returning.
        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            // Initialize header with drop_fn for unified rc_dec cleanup
            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::String as u32, string_drop),
            );
            ptr::write(&mut (*ptr).len, len);
            ptr::write(&mut (*ptr).char_count, char_count);
            ptr::write(&mut (*ptr).hash, hash);

            // Copy string data
            let data_ptr = (ptr as *mut u8).add(RCSTRING_DATA_OFFSET);
            ptr::copy_nonoverlapping(s.as_ptr(), data_ptr, len);

            alloc_track::track_alloc(RuntimeTypeId::String as u32);
            ptr
        }
    }

    fn layout_for_len(len: usize) -> Layout {
        let size = RCSTRING_DATA_OFFSET + len;
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
            let data_ptr = (self as *const Self as *const u8).add(RCSTRING_DATA_OFFSET);
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

        // Count characters from both UTF-8 byte slices.
        // SAFETY: Callers guarantee both slices contain valid UTF-8 bytes.
        let char_count = unsafe {
            str::from_utf8_unchecked(a).chars().count()
                + str::from_utf8_unchecked(b).chars().count()
        };

        // Hash both parts sequentially to produce the same result as hashing
        // the concatenated bytes.
        let mut hasher = Fnv1aHasher::new();
        hasher.update(a);
        hasher.update(b);
        let hash = hasher.finish();

        let layout = Self::layout_for_len(total_len);

        // SAFETY: Layout is valid (computed from combined len + header size).
        // Every field is initialized via ptr::write; data is copied from valid slices.
        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::String as u32, string_drop),
            );
            ptr::write(&mut (*ptr).len, total_len);
            ptr::write(&mut (*ptr).char_count, char_count);
            ptr::write(&mut (*ptr).hash, hash);

            let data_ptr = (ptr as *mut u8).add(RCSTRING_DATA_OFFSET);
            ptr::copy_nonoverlapping(a.as_ptr(), data_ptr, a.len());
            ptr::copy_nonoverlapping(b.as_ptr(), data_ptr.add(a.len()), b.len());

            alloc_track::track_alloc(RuntimeTypeId::String as u32);
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
    alloc_track::track_dealloc(RuntimeTypeId::String as u32);
    // SAFETY: Called only by rc_dec when refcount reaches zero, so ptr is a
    // valid RcString allocation. Layout matches the one used at allocation.
    unsafe {
        let s = ptr as *mut RcString;
        let len = (*s).len;
        let layout = RcString::layout_for_len(len);
        dealloc(ptr, layout);
    }
}

// =============================================================================
// FFI functions for JIT-compiled code
// =============================================================================
//
// Safety contract: the JIT guarantees pointer validity for all arguments.
// String pointers are either null or valid RcString allocations. The `data`
// pointer in `vole_string_new` points to valid UTF-8 bytes embedded in the
// JIT code segment or in a live RcString.
//
// Null handling: functions that read from string pointers (len, data, eq)
// return zero/null/false for null inputs, supporting nil-propagation.
// RC operations (inc/dec) delegate to rc_inc/rc_dec which handle null.

/// Create a new RC string from raw UTF-8 bytes. Returns non-null with refcount 1.
///
/// # JIT contract
/// `data` must point to `len` bytes of valid UTF-8. The JIT emits this for
/// string literals (pointing into the code segment) and runtime concatenations.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_string_new(data: *const u8, len: usize) -> *mut RcString {
    // SAFETY: JIT contract guarantees `data` points to `len` bytes of valid UTF-8.
    let s = unsafe {
        let slice = slice::from_raw_parts(data, len);
        str::from_utf8_unchecked(slice)
    };
    RcString::new(s)
}

/// Increment string reference count. Null is a no-op (delegated to `rc_inc`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_inc(ptr: *mut RcString) {
    rc_inc(ptr as *mut u8);
}

/// Decrement string reference count. Frees the string (via `string_drop`)
/// when the count reaches zero. Null is a no-op (delegated to `rc_dec`).
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_dec(ptr: *mut RcString) {
    rc_dec(ptr as *mut u8);
}

/// Get the character count of a string (O(1), cached at construction).
/// Returns 0 for null pointers (nil-propagation).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_string_len(ptr: *const RcString) -> usize {
    if ptr.is_null() {
        return 0;
    }
    // Return cached character count (O(1), computed at construction time)
    // SAFETY: Null case handled above; JIT guarantees non-null ptrs are valid RcStrings.
    unsafe { (*ptr).char_count }
}

/// Get a pointer to the string's raw UTF-8 byte data.
/// Returns null for null pointers (nil-propagation).
#[unsafe(no_mangle)]
pub extern "C" fn vole_string_data(ptr: *const RcString) -> *const u8 {
    if ptr.is_null() {
        return ptr::null();
    }
    // SAFETY: Null case handled above; inline data immediately follows the header.
    unsafe { (ptr as *const u8).add(RCSTRING_DATA_OFFSET) }
}

/// Compare two strings for equality. Returns 1 if equal, 0 otherwise.
/// Two null pointers are considered equal; a null and non-null are unequal.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_string_eq(a: *const RcString, b: *const RcString) -> i8 {
    if a.is_null() && b.is_null() {
        return 1;
    }
    if a.is_null() || b.is_null() {
        return 0;
    }
    // SAFETY: Both null cases handled above; JIT guarantees non-null ptrs are
    // valid RcStrings containing UTF-8 data.
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

// src/runtime/stdlib/string.rs
//! Native string functions for std:string module.
//!
//! All string functions are UTF-8/character-aware:
//! - Lengths are measured in characters, not bytes
//! - Indices are character indices, not byte indices
//! - Substrings use character-based slicing

use crate::RcString;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:string native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // str_len: (string) -> i64 - Character count
    m.register(
        "str_len",
        str_len as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // Backward compat alias
    m.register(
        "string_length",
        str_len as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // str_byte_len: (string) -> i64 - Byte count
    m.register(
        "str_byte_len",
        str_byte_len as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // str_equals: (string, string) -> bool
    m.register(
        "str_equals",
        str_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // str_compare: (string, string) -> i32 (-1, 0, 1)
    m.register(
        "str_compare",
        str_compare as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::I32,
        },
    );

    // str_hash: (string) -> i64 (FNV-1a hash)
    m.register(
        "str_hash",
        str_hash as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // str_contains: (string, string) -> bool
    m.register(
        "str_contains",
        str_contains as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // Backward compat alias
    m.register(
        "string_contains",
        str_contains as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // str_starts_with: (string, string) -> bool
    m.register(
        "str_starts_with",
        str_starts_with as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // str_ends_with: (string, string) -> bool
    m.register(
        "str_ends_with",
        str_ends_with as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::Bool,
        },
    );

    // str_index_of: (string, string) -> i32 (CHARACTER index, -1 if not found)
    m.register(
        "str_index_of",
        str_index_of as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String],
            return_type: NativeType::I32,
        },
    );

    // str_to_lower: (string) -> string
    m.register(
        "str_to_lower",
        str_to_lower as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_to_upper: (string) -> string
    m.register(
        "str_to_upper",
        str_to_upper as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_trim: (string) -> string
    m.register(
        "str_trim",
        str_trim as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_trim_start: (string) -> string
    m.register(
        "str_trim_start",
        str_trim_start as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_trim_end: (string) -> string
    m.register(
        "str_trim_end",
        str_trim_end as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_substring: (string, i32 start, i32 end) -> string (CHARACTER-based)
    m.register(
        "str_substring",
        str_substring as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::I32, NativeType::I32],
            return_type: NativeType::String,
        },
    );

    // str_replace: (string, string old, string new) -> string (first occurrence)
    m.register(
        "str_replace",
        str_replace as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String, NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_replace_all: (string, string old, string new) -> string (all occurrences)
    m.register(
        "str_replace_all",
        str_replace_all as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::String, NativeType::String],
            return_type: NativeType::String,
        },
    );

    // str_char_at: (string, i32 index) -> i32 (unicode codepoint, -1 if out of bounds)
    m.register(
        "str_char_at",
        str_char_at as *const u8,
        NativeSignature {
            params: vec![NativeType::String, NativeType::I32],
            return_type: NativeType::I32,
        },
    );

    m
}

// ============================================================================
// Helper functions for UTF-8 character operations
// ============================================================================

/// Convert a byte index to a character index in a string
fn byte_index_to_char_index(s: &str, byte_idx: usize) -> usize {
    s[..byte_idx].chars().count()
}

/// Convert a character index to a byte index in a string
/// Returns None if char_idx is out of bounds
fn char_index_to_byte_index(s: &str, char_idx: usize) -> Option<usize> {
    s.char_indices().nth(char_idx).map(|(byte_idx, _)| byte_idx)
}

// ============================================================================
// Native function implementations
// ============================================================================

/// Get the length of a string in characters (not bytes!)
#[unsafe(no_mangle)]
pub extern "C" fn str_len(s: *const RcString) -> i64 {
    if s.is_null() {
        return 0;
    }
    unsafe { (*s).as_str().chars().count() as i64 }
}

/// Get the length of a string in bytes (not characters!)
#[unsafe(no_mangle)]
pub extern "C" fn str_byte_len(s: *const RcString) -> i64 {
    if s.is_null() {
        return 0;
    }
    unsafe { (*s).as_str().len() as i64 }
}

/// Check if two strings are equal
#[unsafe(no_mangle)]
pub extern "C" fn str_equals(a: *const RcString, b: *const RcString) -> i8 {
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

/// Compare two strings lexicographically
/// Returns -1 if a < b, 0 if a == b, 1 if a > b
#[unsafe(no_mangle)]
pub extern "C" fn str_compare(a: *const RcString, b: *const RcString) -> i32 {
    let a_str = if a.is_null() {
        ""
    } else {
        unsafe { (*a).as_str() }
    };
    let b_str = if b.is_null() {
        ""
    } else {
        unsafe { (*b).as_str() }
    };
    super::intrinsics::ordering_to_i32(a_str.cmp(b_str))
}

/// Compute FNV-1a hash of a string
#[unsafe(no_mangle)]
pub extern "C" fn str_hash(s: *const RcString) -> i64 {
    if s.is_null() {
        return 0;
    }
    unsafe {
        let bytes = (*s).as_str().as_bytes();
        // FNV-1a 64-bit hash
        const FNV_OFFSET: u64 = 14695981039346656037;
        const FNV_PRIME: u64 = 1099511628211;

        let mut hash = FNV_OFFSET;
        for byte in bytes {
            hash ^= *byte as u64;
            hash = hash.wrapping_mul(FNV_PRIME);
        }
        hash as i64
    }
}

/// Check if a string contains a substring
#[unsafe(no_mangle)]
pub extern "C" fn str_contains(s: *const RcString, needle: *const RcString) -> i8 {
    if s.is_null() || needle.is_null() {
        return 0;
    }
    unsafe {
        let haystack = (*s).as_str();
        let needle_str = (*needle).as_str();
        if haystack.contains(needle_str) { 1 } else { 0 }
    }
}

/// Check if a string starts with a prefix
#[unsafe(no_mangle)]
pub extern "C" fn str_starts_with(s: *const RcString, prefix: *const RcString) -> i8 {
    if s.is_null() || prefix.is_null() {
        return 0;
    }
    unsafe {
        let s_str = (*s).as_str();
        let prefix_str = (*prefix).as_str();
        if s_str.starts_with(prefix_str) { 1 } else { 0 }
    }
}

/// Check if a string ends with a suffix
#[unsafe(no_mangle)]
pub extern "C" fn str_ends_with(s: *const RcString, suffix: *const RcString) -> i8 {
    if s.is_null() || suffix.is_null() {
        return 0;
    }
    unsafe {
        let s_str = (*s).as_str();
        let suffix_str = (*suffix).as_str();
        if s_str.ends_with(suffix_str) { 1 } else { 0 }
    }
}

/// Find the character index of the first occurrence of needle in s
/// Returns -1 if not found
/// IMPORTANT: Returns CHARACTER index, not byte index!
#[unsafe(no_mangle)]
pub extern "C" fn str_index_of(s: *const RcString, needle: *const RcString) -> i32 {
    if s.is_null() || needle.is_null() {
        return -1;
    }
    unsafe {
        let haystack = (*s).as_str();
        let needle_str = (*needle).as_str();
        match haystack.find(needle_str) {
            Some(byte_idx) => byte_index_to_char_index(haystack, byte_idx) as i32,
            None => -1,
        }
    }
}

/// Convert a string to lowercase
#[unsafe(no_mangle)]
pub extern "C" fn str_to_lower(s: *const RcString) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        RcString::new(&s_str.to_lowercase())
    }
}

/// Convert a string to uppercase
#[unsafe(no_mangle)]
pub extern "C" fn str_to_upper(s: *const RcString) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        RcString::new(&s_str.to_uppercase())
    }
}

/// Trim whitespace from both ends of a string
#[unsafe(no_mangle)]
pub extern "C" fn str_trim(s: *const RcString) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        RcString::new(s_str.trim())
    }
}

/// Trim whitespace from the start of a string
#[unsafe(no_mangle)]
pub extern "C" fn str_trim_start(s: *const RcString) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        RcString::new(s_str.trim_start())
    }
}

/// Trim whitespace from the end of a string
#[unsafe(no_mangle)]
pub extern "C" fn str_trim_end(s: *const RcString) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        RcString::new(s_str.trim_end())
    }
}

/// Extract a substring using CHARACTER indices (not byte indices!)
/// start: starting character index (0-based)
/// end: ending character index (exclusive), or -1 for end of string
#[unsafe(no_mangle)]
pub extern "C" fn str_substring(s: *const RcString, start: i32, end: i32) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        let char_count = s_str.chars().count();

        // Handle negative or out-of-bounds start
        let start_idx = if start < 0 { 0 } else { start as usize };
        if start_idx >= char_count {
            return RcString::new("");
        }

        // Handle end index: -1 means to end of string
        let end_idx = if end < 0 {
            char_count
        } else {
            (end as usize).min(char_count)
        };

        if start_idx >= end_idx {
            return RcString::new("");
        }

        // Convert character indices to byte indices
        let start_byte = char_index_to_byte_index(s_str, start_idx).unwrap_or(0);
        let end_byte = char_index_to_byte_index(s_str, end_idx).unwrap_or(s_str.len());

        RcString::new(&s_str[start_byte..end_byte])
    }
}

/// Replace the first occurrence of old with new
#[unsafe(no_mangle)]
pub extern "C" fn str_replace(
    s: *const RcString,
    old: *const RcString,
    new: *const RcString,
) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        let old_str = if old.is_null() { "" } else { (*old).as_str() };
        let new_str = if new.is_null() { "" } else { (*new).as_str() };

        // Replace first occurrence only
        let result = s_str.replacen(old_str, new_str, 1);
        RcString::new(&result)
    }
}

/// Replace all occurrences of old with new
#[unsafe(no_mangle)]
pub extern "C" fn str_replace_all(
    s: *const RcString,
    old: *const RcString,
    new: *const RcString,
) -> *const RcString {
    if s.is_null() {
        return RcString::new("");
    }
    unsafe {
        let s_str = (*s).as_str();
        let old_str = if old.is_null() { "" } else { (*old).as_str() };
        let new_str = if new.is_null() { "" } else { (*new).as_str() };

        let result = s_str.replace(old_str, new_str);
        RcString::new(&result)
    }
}

/// Get the character (unicode codepoint) at a given index
/// Returns -1 if index is out of bounds
#[unsafe(no_mangle)]
pub extern "C" fn str_char_at(s: *const RcString, index: i32) -> i32 {
    if s.is_null() || index < 0 {
        return -1;
    }
    unsafe {
        let s_str = (*s).as_str();
        match s_str.chars().nth(index as usize) {
            Some(ch) => ch as i32,
            None => -1,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a string and return a raw pointer
    fn make_str(s: &str) -> *const RcString {
        RcString::new(s)
    }

    // Helper to safely clean up a string
    unsafe fn cleanup(s: *const RcString) {
        if !s.is_null() {
            unsafe { RcString::dec_ref(s as *mut RcString) };
        }
    }

    // ========================================================================
    // str_len tests
    // ========================================================================

    #[test]
    fn test_str_len_ascii() {
        let s = make_str("hello");
        assert_eq!(str_len(s), 5);
        unsafe { cleanup(s) };
    }

    #[test]
    fn test_str_len_empty() {
        let s = make_str("");
        assert_eq!(str_len(s), 0);
        unsafe { cleanup(s) };
    }

    #[test]
    fn test_str_len_null() {
        assert_eq!(str_len(std::ptr::null()), 0);
    }

    #[test]
    fn test_str_len_utf8_cafe() {
        // "café" is 4 characters but 5 bytes (é is 2 bytes in UTF-8)
        let s = make_str("café");
        assert_eq!(str_len(s), 4); // Characters, not bytes!
        unsafe { cleanup(s) };
    }

    #[test]
    fn test_str_len_emoji() {
        // "hello 👋" is 7 characters (emoji is 1 character, 4 bytes)
        let s = make_str("hello 👋");
        assert_eq!(str_len(s), 7); // Characters, not bytes!
        unsafe { cleanup(s) };
    }

    #[test]
    fn test_str_len_chinese() {
        // Each Chinese character is 1 character but 3 bytes
        let s = make_str("你好");
        assert_eq!(str_len(s), 2);
        unsafe { cleanup(s) };
    }

    // ========================================================================
    // str_equals tests
    // ========================================================================

    #[test]
    fn test_str_equals_same() {
        let a = make_str("hello");
        let b = make_str("hello");
        assert_eq!(str_equals(a, b), 1);
        unsafe {
            cleanup(a);
            cleanup(b);
        }
    }

    #[test]
    fn test_str_equals_different() {
        let a = make_str("hello");
        let b = make_str("world");
        assert_eq!(str_equals(a, b), 0);
        unsafe {
            cleanup(a);
            cleanup(b);
        }
    }

    #[test]
    fn test_str_equals_null() {
        let a = make_str("hello");
        assert_eq!(str_equals(a, std::ptr::null()), 0);
        assert_eq!(str_equals(std::ptr::null(), a), 0);
        assert_eq!(str_equals(std::ptr::null(), std::ptr::null()), 1);
        unsafe { cleanup(a) };
    }

    // ========================================================================
    // str_compare tests
    // ========================================================================

    #[test]
    fn test_str_compare() {
        let a = make_str("apple");
        let b = make_str("banana");
        let c = make_str("apple");

        assert_eq!(str_compare(a, b), -1); // apple < banana
        assert_eq!(str_compare(b, a), 1); // banana > apple
        assert_eq!(str_compare(a, c), 0); // apple == apple

        unsafe {
            cleanup(a);
            cleanup(b);
            cleanup(c);
        }
    }

    // ========================================================================
    // str_hash tests
    // ========================================================================

    #[test]
    fn test_str_hash_consistency() {
        let a = make_str("hello");
        let b = make_str("hello");
        let c = make_str("world");

        let hash_a = str_hash(a);
        let hash_b = str_hash(b);
        let hash_c = str_hash(c);

        assert_eq!(hash_a, hash_b); // Same string = same hash
        assert_ne!(hash_a, hash_c); // Different strings = different hash (usually)

        unsafe {
            cleanup(a);
            cleanup(b);
            cleanup(c);
        }
    }

    #[test]
    fn test_str_hash_null() {
        assert_eq!(str_hash(std::ptr::null()), 0);
    }

    // ========================================================================
    // str_contains tests
    // ========================================================================

    #[test]
    fn test_str_contains_found() {
        let s = make_str("hello world");
        let needle = make_str("world");
        assert_eq!(str_contains(s, needle), 1);
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    #[test]
    fn test_str_contains_not_found() {
        let s = make_str("hello world");
        let needle = make_str("xyz");
        assert_eq!(str_contains(s, needle), 0);
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    #[test]
    fn test_str_contains_null() {
        let s = make_str("hello");
        assert_eq!(str_contains(s, std::ptr::null()), 0);
        assert_eq!(str_contains(std::ptr::null(), s), 0);
        unsafe { cleanup(s) };
    }

    // ========================================================================
    // str_starts_with / str_ends_with tests
    // ========================================================================

    #[test]
    fn test_str_starts_with() {
        let s = make_str("hello world");
        let prefix = make_str("hello");
        let not_prefix = make_str("world");

        assert_eq!(str_starts_with(s, prefix), 1);
        assert_eq!(str_starts_with(s, not_prefix), 0);

        unsafe {
            cleanup(s);
            cleanup(prefix);
            cleanup(not_prefix);
        }
    }

    #[test]
    fn test_str_ends_with() {
        let s = make_str("hello world");
        let suffix = make_str("world");
        let not_suffix = make_str("hello");

        assert_eq!(str_ends_with(s, suffix), 1);
        assert_eq!(str_ends_with(s, not_suffix), 0);

        unsafe {
            cleanup(s);
            cleanup(suffix);
            cleanup(not_suffix);
        }
    }

    // ========================================================================
    // str_index_of tests
    // ========================================================================

    #[test]
    fn test_str_index_of_found() {
        let s = make_str("hello world");
        let needle = make_str("world");
        assert_eq!(str_index_of(s, needle), 6);
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    #[test]
    fn test_str_index_of_not_found() {
        let s = make_str("hello world");
        let needle = make_str("xyz");
        assert_eq!(str_index_of(s, needle), -1);
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    #[test]
    fn test_str_index_of_utf8_returns_char_index() {
        // "café au lait" - find "au"
        // byte index of "au" would be 6 (c=1, a=1, f=1, é=2, space=1)
        // character index is 5 (c=0, a=1, f=2, é=3, space=4, a=5)
        let s = make_str("café au lait");
        let needle = make_str("au");
        assert_eq!(str_index_of(s, needle), 5); // CHARACTER index, not byte!
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    #[test]
    fn test_str_index_of_emoji() {
        // "hi 👋 there" - find "there"
        // Character positions: h=0, i=1, space=2, 👋=3, space=4, t=5
        let s = make_str("hi 👋 there");
        let needle = make_str("there");
        assert_eq!(str_index_of(s, needle), 5); // CHARACTER index
        unsafe {
            cleanup(s);
            cleanup(needle);
        }
    }

    // ========================================================================
    // str_to_lower / str_to_upper tests
    // ========================================================================

    #[test]
    fn test_str_to_lower() {
        let s = make_str("Hello World");
        let result = str_to_lower(s);
        assert_eq!(unsafe { (*result).as_str() }, "hello world");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_to_upper() {
        let s = make_str("Hello World");
        let result = str_to_upper(s);
        assert_eq!(unsafe { (*result).as_str() }, "HELLO WORLD");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_to_lower_utf8() {
        let s = make_str("CAFÉ");
        let result = str_to_lower(s);
        assert_eq!(unsafe { (*result).as_str() }, "café");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    // ========================================================================
    // str_trim tests
    // ========================================================================

    #[test]
    fn test_str_trim() {
        let s = make_str("  hello world  ");
        let result = str_trim(s);
        assert_eq!(unsafe { (*result).as_str() }, "hello world");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_trim_start() {
        let s = make_str("  hello world  ");
        let result = str_trim_start(s);
        assert_eq!(unsafe { (*result).as_str() }, "hello world  ");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_trim_end() {
        let s = make_str("  hello world  ");
        let result = str_trim_end(s);
        assert_eq!(unsafe { (*result).as_str() }, "  hello world");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    // ========================================================================
    // str_substring tests
    // ========================================================================

    #[test]
    fn test_str_substring_basic() {
        let s = make_str("hello world");
        let result = str_substring(s, 0, 5);
        assert_eq!(unsafe { (*result).as_str() }, "hello");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_substring_to_end() {
        let s = make_str("hello world");
        let result = str_substring(s, 6, -1);
        assert_eq!(unsafe { (*result).as_str() }, "world");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_substring_utf8() {
        // "café au lait" - extract "café"
        // Using character indices: café is at positions 0-4
        let s = make_str("café au lait");
        let result = str_substring(s, 0, 4);
        assert_eq!(unsafe { (*result).as_str() }, "café");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_substring_emoji() {
        // "hi 👋 there" - extract "👋 there"
        // Character positions: h=0, i=1, space=2, 👋=3, space=4, t=5, h=6, e=7, r=8, e=9
        let s = make_str("hi 👋 there");
        let result = str_substring(s, 3, -1);
        assert_eq!(unsafe { (*result).as_str() }, "👋 there");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_substring_out_of_bounds() {
        let s = make_str("hello");
        let result = str_substring(s, 10, 20);
        assert_eq!(unsafe { (*result).as_str() }, "");
        unsafe {
            cleanup(s);
            cleanup(result);
        }
    }

    // ========================================================================
    // str_replace tests
    // ========================================================================

    #[test]
    fn test_str_replace_found() {
        let s = make_str("hello world");
        let old = make_str("world");
        let new = make_str("there");
        let result = str_replace(s, old, new);
        assert_eq!(unsafe { (*result).as_str() }, "hello there");
        unsafe {
            cleanup(s);
            cleanup(old);
            cleanup(new);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_replace_not_found() {
        let s = make_str("hello world");
        let old = make_str("xyz");
        let new = make_str("abc");
        let result = str_replace(s, old, new);
        assert_eq!(unsafe { (*result).as_str() }, "hello world");
        unsafe {
            cleanup(s);
            cleanup(old);
            cleanup(new);
            cleanup(result);
        }
    }

    #[test]
    fn test_str_replace_first_only() {
        // Should only replace first occurrence
        let s = make_str("hello hello hello");
        let old = make_str("hello");
        let new = make_str("hi");
        let result = str_replace(s, old, new);
        assert_eq!(unsafe { (*result).as_str() }, "hi hello hello");
        unsafe {
            cleanup(s);
            cleanup(old);
            cleanup(new);
            cleanup(result);
        }
    }

    // ========================================================================
    // Module registration test
    // ========================================================================

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("str_len").is_some());
        assert!(m.get("string_length").is_some()); // Alias
        assert!(m.get("str_equals").is_some());
        assert!(m.get("str_compare").is_some());
        assert!(m.get("str_hash").is_some());
        assert!(m.get("str_contains").is_some());
        assert!(m.get("string_contains").is_some()); // Alias
        assert!(m.get("str_starts_with").is_some());
        assert!(m.get("str_ends_with").is_some());
        assert!(m.get("str_index_of").is_some());
        assert!(m.get("str_to_lower").is_some());
        assert!(m.get("str_to_upper").is_some());
        assert!(m.get("str_trim").is_some());
        assert!(m.get("str_trim_start").is_some());
        assert!(m.get("str_trim_end").is_some());
        assert!(m.get("str_substring").is_some());
        assert!(m.get("str_replace").is_some());

        // Check signature of str_len
        let len_func = m.get("str_len").unwrap();
        assert_eq!(len_func.signature.params.len(), 1);
        assert_eq!(len_func.signature.params[0], NativeType::String);
        assert_eq!(len_func.signature.return_type, NativeType::I64);

        // Check signature of str_substring (3 params)
        let substr_func = m.get("str_substring").unwrap();
        assert_eq!(substr_func.signature.params.len(), 3);
        assert_eq!(substr_func.signature.params[0], NativeType::String);
        assert_eq!(substr_func.signature.params[1], NativeType::I32);
        assert_eq!(substr_func.signature.params[2], NativeType::I32);
        assert_eq!(substr_func.signature.return_type, NativeType::String);
    }
}

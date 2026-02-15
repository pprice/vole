use crate::string::RcString;

pub struct StringBuilder {
    buf: Vec<u8>,
}

/// Create a new StringBuilder with pre-allocated capacity.
#[unsafe(no_mangle)]
pub extern "C" fn vole_sb_new() -> *mut StringBuilder {
    let sb = Box::new(StringBuilder {
        buf: Vec::with_capacity(64),
    });
    Box::into_raw(sb)
}

/// Push a string onto the builder. Null pointers are safely ignored.
#[unsafe(no_mangle)]
pub extern "C" fn vole_sb_push_string(sb: *mut StringBuilder, s: *const RcString) {
    if sb.is_null() || s.is_null() {
        return;
    }
    unsafe {
        let builder = &mut *sb;
        let rc_string = &*s;
        let bytes = rc_string.data();
        builder.buf.extend_from_slice(bytes);
    }
}

/// Finish building, consuming the StringBuilder and returning a new RcString.
/// The caller owns the returned RcString (refcount=1).
#[unsafe(no_mangle)]
pub extern "C" fn vole_sb_finish(sb: *mut StringBuilder) -> *mut RcString {
    if sb.is_null() {
        return RcString::new("");
    }
    unsafe {
        let builder = Box::from_raw(sb);
        debug_assert!(
            std::str::from_utf8(&builder.buf).is_ok(),
            "StringBuilder buffer contains invalid UTF-8"
        );
        let s = std::str::from_utf8_unchecked(&builder.buf);
        RcString::new(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn empty_builder_produces_empty_string() {
        let sb = vole_sb_new();
        let result = vole_sb_finish(sb);
        unsafe {
            assert_eq!((*result).len, 0);
            assert_eq!((*result).as_str(), "");
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn single_push() {
        let sb = vole_sb_new();
        let s = RcString::new("hello");
        vole_sb_push_string(sb, s);
        let result = vole_sb_finish(sb);
        unsafe {
            assert_eq!((*result).as_str(), "hello");
            RcString::dec_ref(s);
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn multiple_pushes_concatenated() {
        let sb = vole_sb_new();
        let s1 = RcString::new("hello");
        let s2 = RcString::new(", ");
        let s3 = RcString::new("world!");
        vole_sb_push_string(sb, s1);
        vole_sb_push_string(sb, s2);
        vole_sb_push_string(sb, s3);
        let result = vole_sb_finish(sb);
        unsafe {
            assert_eq!((*result).as_str(), "hello, world!");
            RcString::dec_ref(s1);
            RcString::dec_ref(s2);
            RcString::dec_ref(s3);
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn null_push_does_not_crash() {
        let sb = vole_sb_new();
        vole_sb_push_string(sb, std::ptr::null());
        vole_sb_push_string(std::ptr::null_mut(), RcString::new("x"));
        let result = vole_sb_finish(sb);
        unsafe {
            assert_eq!((*result).as_str(), "");
            RcString::dec_ref(result);
        }
    }

    #[test]
    fn finished_string_has_refcount_one() {
        let sb = vole_sb_new();
        let s = RcString::new("test");
        vole_sb_push_string(sb, s);
        let result = vole_sb_finish(sb);
        unsafe {
            let rc = (*result).header.ref_count.load(Ordering::Relaxed);
            assert_eq!(rc, 1);
            RcString::dec_ref(s);
            RcString::dec_ref(result);
        }
    }
}

// src/runtime/assert.rs
//
// Runtime support for test assertions with longjmp-based failure handling.
// When running in a test context, assertion failures longjmp back to the test
// harness rather than aborting the process.

use std::cell::Cell;

// Platform-specific jmp_buf definition
// On x86_64 Linux, jmp_buf is typically an array of 8 longs (64 bytes)
// We use a larger size to be safe across platforms
#[repr(C)]
#[derive(Copy, Clone)]
pub struct JmpBuf {
    _data: [u8; 200], // Large enough for any platform's jmp_buf
}

impl JmpBuf {
    pub const fn zeroed() -> Self {
        JmpBuf { _data: [0; 200] }
    }
}

unsafe extern "C" {
    // sigsetjmp returns 0 on direct call, non-zero when returning via siglongjmp
    // Use __sigsetjmp on Linux which is the actual implementation
    #[cfg(target_os = "linux")]
    #[link_name = "__sigsetjmp"]
    fn sigsetjmp(buf: *mut JmpBuf, savemask: libc::c_int) -> libc::c_int;

    #[cfg(target_os = "macos")]
    fn sigsetjmp(buf: *mut JmpBuf, savemask: libc::c_int) -> libc::c_int;

    // siglongjmp jumps back to the sigsetjmp call point
    pub(crate) fn siglongjmp(buf: *mut JmpBuf, val: libc::c_int) -> !;
}

thread_local! {
    pub(crate) static ASSERT_JMP_BUF: Cell<*mut JmpBuf> = const { Cell::new(std::ptr::null_mut()) };
    pub(crate) static ASSERT_FAILURE: Cell<Option<AssertFailure>> = const { Cell::new(None) };
}

/// Information about an assertion failure
#[derive(Debug, Clone)]
pub struct AssertFailure {
    pub file: String,
    pub line: u32,
}

/// Set the jump buffer for test context.
/// When an assertion fails, it will longjmp to this buffer.
pub fn set_test_jmp_buf(buf: *mut JmpBuf) {
    ASSERT_JMP_BUF.with(|jb| jb.set(buf));
}

/// Clear the jump buffer when leaving test context.
pub fn clear_test_jmp_buf() {
    ASSERT_JMP_BUF.with(|jb| jb.set(std::ptr::null_mut()));
}

/// Take the recorded assertion failure info, if any.
pub fn take_assert_failure() -> Option<AssertFailure> {
    ASSERT_FAILURE.with(|f| f.take())
}

/// Call sigsetjmp on a JmpBuf, returns 0 on first call, non-zero on siglongjmp return.
///
/// # Safety
/// The caller must ensure the JmpBuf remains valid until siglongjmp or clear.
/// IMPORTANT: This must always be inlined - if called through a wrapper function,
/// the longjmp will return to a corrupted stack frame.
#[inline(always)]
pub unsafe fn call_setjmp(buf: *mut JmpBuf) -> i32 {
    unsafe { sigsetjmp(buf, 0) }
}

/// Runtime function called when a Vole `assert(...)` expression fails.
///
/// The JIT emits a call to this function when an assert condition is false,
/// passing the source file path (as raw UTF-8 bytes) and line number from
/// the AST.
///
/// If in test context (a jmp_buf has been set via `set_test_jmp_buf`), records
/// the failure location and longjmps back to the test harness. If not in test
/// context, prints an error to stderr and aborts the process.
///
/// # JIT contract
/// - `file` points to `file_len` bytes of valid UTF-8 (the source file path),
///   or is null.
/// - `line` is the 1-based line number from the source.
#[unsafe(no_mangle)]
pub extern "C" fn vole_assert_fail(file: *const u8, file_len: usize, line: u32) {
    let file_str = unsafe {
        if file.is_null() || file_len == 0 {
            "<unknown>"
        } else {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(file, file_len))
        }
    };

    ASSERT_JMP_BUF.with(|jb| {
        let buf = jb.get();
        if !buf.is_null() {
            // In test context - record failure and longjmp
            ASSERT_FAILURE.with(|f| {
                f.set(Some(AssertFailure {
                    file: file_str.to_string(),
                    line,
                }));
            });
            unsafe {
                siglongjmp(buf, 1);
            }
        } else {
            // Not in test context - abort
            eprintln!("assertion failed at {}:{}", file_str, line);
            std::process::abort();
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assert_failure_in_test_context() {
        let mut jmp_buf = JmpBuf::zeroed();

        let result = unsafe { call_setjmp(&mut jmp_buf) };

        if result == 0 {
            // First time - set up context and trigger failure
            set_test_jmp_buf(&mut jmp_buf);
            vole_assert_fail(b"test.vole".as_ptr(), 9, 42);
            // Should not reach here
            panic!("should have longjmp'd");
        } else {
            // Returned via longjmp
            clear_test_jmp_buf();
            let failure = take_assert_failure().expect("should have failure info");
            assert_eq!(failure.file, "test.vole");
            assert_eq!(failure.line, 42);
        }
    }

    #[test]
    fn test_take_clears_failure() {
        ASSERT_FAILURE.with(|f| {
            f.set(Some(AssertFailure {
                file: "test.vole".to_string(),
                line: 10,
            }));
        });

        let first = take_assert_failure();
        let second = take_assert_failure();

        assert!(first.is_some());
        assert!(second.is_none());
    }

    #[test]
    fn test_set_and_clear_jmp_buf() {
        let mut jmp_buf = JmpBuf::zeroed();

        // Initially null
        ASSERT_JMP_BUF.with(|jb| assert!(jb.get().is_null()));

        // Set it
        set_test_jmp_buf(&mut jmp_buf);
        ASSERT_JMP_BUF.with(|jb| assert!(!jb.get().is_null()));

        // Clear it
        clear_test_jmp_buf();
        ASSERT_JMP_BUF.with(|jb| assert!(jb.get().is_null()));
    }
}

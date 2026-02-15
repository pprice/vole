//! Coroutine runtime primitives via corosensei.
//!
//! `VoleCoroutine` is a Vole-specific wrapper around `corosensei::Coroutine`.
//! It is the shared primitive powering both generator iterators and the task scheduler.

use corosensei::stack::DefaultStack;
use corosensei::{Coroutine as RawCoroutine, CoroutineResult};

/// A Vole coroutine wrapping `corosensei::Coroutine`.
///
/// Communicates via `i64` values in both directions (yield and resume).
/// The coroutine body returns `()` when finished.
pub struct VoleCoroutine {
    inner: RawCoroutine<i64, i64, (), DefaultStack>,
    finished: bool,
}

impl VoleCoroutine {
    /// Create a new coroutine from a closure.
    ///
    /// The closure receives a yielder (for suspending) and the initial input value.
    pub fn new(f: impl FnOnce(&corosensei::Yielder<i64, i64>, i64) + 'static) -> Self {
        Self {
            inner: RawCoroutine::new(move |yielder, input| {
                f(yielder, input);
            }),
            finished: false,
        }
    }

    /// Resume the coroutine with the given input value.
    ///
    /// Returns `Some(value)` if the coroutine yielded, or `None` if it returned (finished).
    pub fn resume(&mut self, input: i64) -> Option<i64> {
        if self.finished {
            return None;
        }
        match self.inner.resume(input) {
            CoroutineResult::Yield(value) => Some(value),
            CoroutineResult::Return(()) => {
                self.finished = true;
                None
            }
        }
    }

    /// Returns `true` if the coroutine has finished executing.
    pub fn is_finished(&self) -> bool {
        self.finished
    }
}

// =============================================================================
// FFI functions
// =============================================================================

/// Create a new `VoleCoroutine` from a function pointer and closure pointer.
///
/// `func_ptr` is a `extern "C" fn(*const u8, *const u8) -> ()` where:
///   - arg1 = `closure_ptr` (opaque closure data)
///   - arg2 = yielder pointer (cast from `&Yielder<i64, i64>`)
///
/// Returns a heap-allocated `VoleCoroutine` pointer (caller owns it).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_coroutine_new(
    func_ptr: *const u8,
    closure_ptr: *const u8,
) -> *mut VoleCoroutine {
    // Safety: func_ptr and closure_ptr come from JIT-generated code and are always valid.
    let func: extern "C" fn(*const u8, *const u8) = unsafe { std::mem::transmute(func_ptr) };
    let closure = closure_ptr as usize; // capture as usize for Send safety

    let coro = VoleCoroutine::new(move |yielder, _input| {
        let yielder_ptr = yielder as *const corosensei::Yielder<i64, i64> as *const u8;
        func(closure as *const u8, yielder_ptr);
    });

    Box::into_raw(Box::new(coro))
}

/// Resume a `VoleCoroutine` with the given input.
///
/// Stores the yielded value in `*out` and returns `1` if the coroutine yielded.
/// Returns `0` if the coroutine is finished (does not write to `*out`).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_coroutine_resume(
    coro: *mut VoleCoroutine,
    input: i64,
    out: *mut i64,
) -> i64 {
    if coro.is_null() {
        return 0;
    }
    let coro = unsafe { &mut *coro };
    match coro.resume(input) {
        Some(value) => {
            unsafe { *out = value };
            1
        }
        None => 0,
    }
}

/// Free a heap-allocated `VoleCoroutine`.
///
/// # Safety
/// `coro` must be null or a valid pointer previously returned by `vole_coroutine_new`.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_coroutine_free(coro: *mut VoleCoroutine) {
    if !coro.is_null() {
        unsafe {
            drop(Box::from_raw(coro));
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn coroutine_yields_sequence() {
        let mut coro = VoleCoroutine::new(|yielder, _input| {
            yielder.suspend(1);
            yielder.suspend(2);
            yielder.suspend(3);
        });

        assert_eq!(coro.resume(0), Some(1));
        assert_eq!(coro.resume(0), Some(2));
        assert_eq!(coro.resume(0), Some(3));
        assert_eq!(coro.resume(0), None);
        // Repeated calls after finish should also return None
        assert_eq!(coro.resume(0), None);
    }

    #[test]
    fn coroutine_drop_before_finish() {
        // Create a coroutine and drop it before it finishes.
        // This tests that stack deallocation works correctly.
        let coro = VoleCoroutine::new(|yielder, _input| {
            yielder.suspend(10);
            yielder.suspend(20);
            yielder.suspend(30);
        });
        drop(coro);
        // If we get here without a crash, stack deallocation succeeded.
    }

    #[test]
    fn coroutine_is_finished_transitions() {
        let mut coro = VoleCoroutine::new(|yielder, _input| {
            yielder.suspend(42);
        });

        // Not finished yet
        assert!(!coro.is_finished());

        // Yield a value - still not finished
        assert_eq!(coro.resume(0), Some(42));
        assert!(!coro.is_finished());

        // Coroutine body returns - now finished
        assert_eq!(coro.resume(0), None);
        assert!(coro.is_finished());

        // Stays finished
        assert_eq!(coro.resume(0), None);
        assert!(coro.is_finished());
    }
}

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

impl Drop for VoleCoroutine {
    fn drop(&mut self) {
        // Skip `force_unwind` for suspended coroutines. Our generator bodies are
        // JIT-compiled and have no DWARF unwind tables, so the standard
        // `force_unwind` (which calls `resume_unwind`) would abort. Instead we
        // use `force_reset` which simply marks the coroutine as done so its
        // stack is deallocated without attempting to unwind through JIT frames.
        //
        // Safety: JIT generator bodies only have primitive/copy values on their
        // stacks — no Rust objects that require Drop — so skipping unwinding is
        // safe.
        if !self.inner.done() {
            unsafe {
                self.inner.force_reset();
            }
        }
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
    // Use `C-unwind` ABI because the body function may call vole_generator_yield
    // which performs a stack switch via corosensei::suspend().
    let func: extern "C-unwind" fn(*const u8, *const u8) = unsafe { std::mem::transmute(func_ptr) };
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
// Generator FFI helpers (coroutine-backed iterators)
// =============================================================================

/// Create a new coroutine-backed generator iterator.
///
/// `body_fn` is a JIT-compiled function with signature:
///   `extern "C" fn(closure_ptr: *const u8, yielder_ptr: *const u8) -> ()`
///
/// `closure_ptr` is the captured environment or null for non-capturing generators.
/// `elem_tag` is the runtime type tag for yielded elements.
///
/// Returns a new `RcIterator` with kind `Coroutine`.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_generator_new(
    body_fn: *const u8,
    closure_ptr: *const u8,
    elem_tag: u64,
) -> *mut crate::iterator::RcIterator {
    use crate::iterator::{CoroutineSource, IteratorKind, IteratorSource, RcIterator};

    // Safety: body_fn and closure_ptr come from JIT-generated code and are always valid.
    // Use `C-unwind` ABI because the body function calls vole_generator_yield which
    // performs a stack switch via corosensei::suspend(). The DWARF unwinder may
    // interpret this as unwinding, so the function pointer must allow it.
    let func: extern "C-unwind" fn(*const u8, *const u8) = unsafe { std::mem::transmute(body_fn) };
    let closure = closure_ptr as usize; // capture as usize for Send safety

    let coro = VoleCoroutine::new(move |yielder, _input| {
        let yielder_ptr = yielder as *const corosensei::Yielder<i64, i64> as *const u8;
        func(closure as *const u8, yielder_ptr);
    });

    let coro_ptr = Box::into_raw(Box::new(coro));

    let iter = RcIterator::new_with_tag(
        IteratorKind::Coroutine,
        IteratorSource {
            coroutine: CoroutineSource {
                coroutine: coro_ptr,
                closure: closure_ptr,
            },
        },
        elem_tag,
    );

    // Coroutine iterators produce owned values.
    if !iter.is_null() {
        unsafe {
            (*iter).produces_owned = true;
        }
    }

    iter
}

/// Yield a value from inside a generator coroutine.
///
/// `yielder_ptr` is the `corosensei::Yielder` passed to the generator body.
/// `value` is the `i64` value to yield.
///
/// Uses `C-unwind` because `suspend()` performs a stack switch via corosensei,
/// which the DWARF unwinder may interpret as unwinding. `extern "C"` would
/// abort on such "unwinds"; `C-unwind` lets them pass through safely.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn vole_generator_yield(yielder_ptr: *const u8, value: i64) {
    unsafe {
        let yielder = &*(yielder_ptr as *const corosensei::Yielder<i64, i64>);
        yielder.suspend(value);
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

    // =========================================================================
    // Generator FFI tests
    // =========================================================================

    /// Test body function: yields 1, 2, 3 via vole_generator_yield, then returns.
    extern "C" fn generator_body_123(_closure_ptr: *const u8, yielder_ptr: *const u8) {
        vole_generator_yield(yielder_ptr, 1);
        vole_generator_yield(yielder_ptr, 2);
        vole_generator_yield(yielder_ptr, 3);
    }

    #[test]
    fn generator_new_yields_sequence_through_iterator_dispatch() {
        use crate::iterator::vole_array_iter_next;
        use crate::value::rc_dec;

        let body_fn = generator_body_123 as extern "C" fn(*const u8, *const u8) as *const u8;
        let iter = vole_generator_new(body_fn, std::ptr::null(), 0);
        assert!(!iter.is_null());

        let mut value: i64 = 0;

        // First yield: 1
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 1);

        // Second yield: 2
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 2);

        // Third yield: 3
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 3);

        // Exhausted: done
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 0);

        // Repeated call after exhaustion still returns done
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 0);

        // Clean up
        rc_dec(iter as *mut u8);
    }

    #[test]
    fn generator_partial_consume_then_drop() {
        use crate::iterator::{
            CoroutineSource, IteratorKind, IteratorSource, RcIterator, vole_array_iter_next,
        };
        use crate::value::rc_dec;

        // Build a coroutine-backed iterator directly with a Rust closure body
        // (not extern "C") so that corosensei can force-unwind the stack on drop.
        // This tests the iterator drop machinery for partially-consumed generators.
        let coro = VoleCoroutine::new(|yielder, _input| {
            yielder.suspend(10);
            yielder.suspend(20);
            yielder.suspend(30);
        });
        let coro_ptr = Box::into_raw(Box::new(coro));

        let iter = RcIterator::new(
            IteratorKind::Coroutine,
            IteratorSource {
                coroutine: CoroutineSource {
                    coroutine: coro_ptr,
                    closure: std::ptr::null(),
                },
            },
        );
        assert!(!iter.is_null());

        let mut value: i64 = 0;

        // Consume only the first value
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 10);

        // Drop the iterator while the coroutine still has pending yields.
        // This must not crash or leak. The Rust closure body supports unwinding.
        rc_dec(iter as *mut u8);
    }

    #[test]
    fn generator_null_closure_ptr() {
        use crate::iterator::vole_array_iter_next;
        use crate::value::rc_dec;

        // Verify that a null closure pointer works correctly (non-capturing generator).
        let body_fn = generator_body_123 as extern "C" fn(*const u8, *const u8) as *const u8;
        let iter = vole_generator_new(body_fn, std::ptr::null(), 0);
        assert!(!iter.is_null());

        // Verify the iterator was created with the Coroutine kind
        unsafe {
            let kind = (*iter).iter.kind;
            assert_eq!(kind, crate::iterator::IteratorKind::Coroutine);
        }

        // Verify produces_owned is set
        unsafe {
            assert!((*iter).produces_owned);
        }

        // Verify the closure field in the source is null
        unsafe {
            assert!((*iter).iter.source.coroutine.closure.is_null());
        }

        let mut value: i64 = 0;

        // Consume all values to ensure the null closure doesn't cause issues
        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 1);

        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 2);

        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 1);
        assert_eq!(value, 3);

        let has = vole_array_iter_next(iter, &mut value);
        assert_eq!(has, 0);

        rc_dec(iter as *mut u8);
    }
}

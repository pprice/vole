//! Native task/channel functions for std:task module.
//!
//! Provides task and channel primitives exposed to Vole via `external("std:task")`.
//! Task and channel handles are opaque i64 pointers passed through the FFI
//! boundary, following the same pattern as `std:buffer`.

use crate::channel::{self, RcChannel};
use crate::closure::Closure;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::task::{self, RcTask};
use crate::value::{RuntimeTypeId, rc_inc};

/// Create the std:task native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // channel_new: (capacity: i64) -> i64 (opaque RcChannel pointer)
    m.register(
        "channel_new",
        channel_new_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // channel_send: (ch: i64, value: i64) -> i64 (0=ok, -1=closed)
    m.register(
        "channel_send",
        channel_send_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // channel_recv: (ch: i64) -> i64 (value or 0 if closed+empty)
    m.register(
        "channel_recv",
        channel_recv_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // channel_try_recv: (ch: i64) -> i64 (value, -1 if closed+empty)
    // Returns a packed result: tag in high bits? No -- for Phase 1,
    // recv returns the value as i64 and nil/0 when closed.
    // We use a separate "is_closed" check instead.

    // channel_close: (ch: i64) -> void
    m.register(
        "channel_close",
        channel_close_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // channel_is_closed: (ch: i64) -> i64 (1/0)
    m.register(
        "channel_is_closed",
        channel_is_closed_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // channel_iter: (ch: i64) -> i64 (opaque RcIterator pointer)
    m.register(
        "channel_iter",
        channel_iter_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // task_run: (closure: i64) -> i64 (opaque RcTask pointer)
    m.register(
        "task_run",
        task_run_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // task_join: (task: i64) -> i64 (result value)
    m.register(
        "task_join",
        task_join_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // task_cancel: (task: i64) -> void
    m.register(
        "task_cancel",
        task_cancel_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // task_is_done: (task: i64) -> i64 (1/0)
    m.register(
        "task_is_done",
        task_is_done_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    m
}

// =============================================================================
// Wrapper functions
// =============================================================================

/// Allocate a new channel. Returns opaque handle as i64.
#[unsafe(no_mangle)]
extern "C" fn channel_new_wrapper(capacity: i64) -> i64 {
    channel::vole_channel_new(capacity) as i64
}

/// Send a value on a channel. Phase 1: stores with I64 tag.
///
/// Returns 0 on success, -1 if channel is closed.
#[unsafe(no_mangle)]
extern "C" fn channel_send_wrapper(ch: i64, value: i64) -> i64 {
    let ch_ptr = ch as *mut RcChannel;
    channel::vole_channel_send(ch_ptr, RuntimeTypeId::I64 as i64, value)
}

/// Receive a value from a channel. Phase 1: returns raw i64 value.
///
/// Returns the value on success, 0 if the channel is closed and empty.
/// The caller must check `is_closed` separately to distinguish "received 0"
/// from "channel closed".
#[unsafe(no_mangle)]
extern "C" fn channel_recv_wrapper(ch: i64) -> i64 {
    let ch_ptr = ch as *mut RcChannel;
    let mut out = [0i64; 2]; // [tag, value]
    let tag = channel::vole_channel_recv(ch_ptr, out.as_mut_ptr());
    if tag == -1 {
        // Channel closed and empty -- return 0 (nil value for Phase 1).
        return 0;
    }
    out[1] // The raw value.
}

/// Close a channel.
#[unsafe(no_mangle)]
extern "C" fn channel_close_wrapper(ch: i64) {
    let ch_ptr = ch as *mut RcChannel;
    channel::vole_channel_close(ch_ptr);
}

/// Check if a channel is closed. Returns 1 if closed, 0 otherwise.
#[unsafe(no_mangle)]
extern "C" fn channel_is_closed_wrapper(ch: i64) -> i64 {
    let ch_ptr = ch as *const RcChannel;
    channel::vole_channel_is_closed(ch_ptr) as i64
}

/// Create an iterator over a channel. Returns opaque RcIterator handle.
#[unsafe(no_mangle)]
extern "C" fn channel_iter_wrapper(ch: i64) -> i64 {
    let ch_ptr = ch as *mut RcChannel;
    crate::iterator::vole_channel_iter(ch_ptr) as i64
}

// =============================================================================
// Task wrapper functions
// =============================================================================

/// Spawn a new task from a Vole closure. Returns opaque RcTask handle as i64.
///
/// Extracts the function pointer from the closure, rc_inc's the closure
/// (the task now owns a reference), and spawns it on the scheduler. The
/// closure reference is stored on the RcTask so it will be rc_dec'd when
/// the task handle is dropped.
#[unsafe(no_mangle)]
extern "C" fn task_run_wrapper(closure_ptr: i64) -> i64 {
    let closure = closure_ptr as *mut Closure;
    if closure.is_null() {
        return 0;
    }

    // Extract the function pointer from the Vole closure.
    let func_ptr = unsafe { Closure::get_func(closure) };

    // RC-inc the closure: the task now owns a reference.
    rc_inc(closure as *mut u8);

    // Spawn the task with the closure's function and closure pointer.
    let task_handle = task::vole_rctask_run(func_ptr, closure as *const u8);

    // Store the closure pointer on the task so it gets rc_dec'd on drop.
    RcTask::set_closure(task_handle, closure as *const u8);

    task_handle as i64
}

/// Join a task: block until it completes, return its result.
#[unsafe(no_mangle)]
extern "C" fn task_join_wrapper(task_handle: i64) -> i64 {
    let task_ptr = task_handle as *mut RcTask;
    task::vole_rctask_join(task_ptr)
}

/// Cancel a task.
#[unsafe(no_mangle)]
extern "C" fn task_cancel_wrapper(task_handle: i64) {
    let task_ptr = task_handle as *mut RcTask;
    task::vole_rctask_cancel(task_ptr);
}

/// Check if a task is done. Returns 1 if done, 0 otherwise.
#[unsafe(no_mangle)]
extern "C" fn task_is_done_wrapper(task_handle: i64) -> i64 {
    let task_ptr = task_handle as *const RcTask;
    task::vole_rctask_is_done(task_ptr)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_registration() {
        let m = module();

        assert!(m.get("channel_new").is_some());
        assert!(m.get("channel_send").is_some());
        assert!(m.get("channel_recv").is_some());
        assert!(m.get("channel_close").is_some());
        assert!(m.get("channel_is_closed").is_some());
        assert!(m.get("channel_iter").is_some());
        assert!(m.get("task_run").is_some());
        assert!(m.get("task_join").is_some());
        assert!(m.get("task_cancel").is_some());
        assert!(m.get("task_is_done").is_some());
    }

    #[test]
    fn channel_new_signature() {
        let m = module();
        let f = m.get("channel_new").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn channel_send_signature() {
        let m = module();
        let f = m.get("channel_send").unwrap();
        assert_eq!(f.signature.params.len(), 2);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.params[1], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn channel_recv_signature() {
        let m = module();
        let f = m.get("channel_recv").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn channel_close_signature() {
        let m = module();
        let f = m.get("channel_close").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::Nil);
    }

    #[test]
    fn channel_is_closed_signature() {
        let m = module();
        let f = m.get("channel_is_closed").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn channel_iter_signature() {
        let m = module();
        let f = m.get("channel_iter").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn task_run_signature() {
        let m = module();
        let f = m.get("task_run").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn task_join_signature() {
        let m = module();
        let f = m.get("task_join").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn task_cancel_signature() {
        let m = module();
        let f = m.get("task_cancel").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::Nil);
    }

    #[test]
    fn task_is_done_signature() {
        let m = module();
        let f = m.get("task_is_done").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn buffered_send_recv_roundtrip() {
        // Create a buffered channel, send, recv.
        let ch = channel_new_wrapper(4);
        assert!(ch != 0);

        assert_eq!(channel_send_wrapper(ch, 42), 0);
        assert_eq!(channel_send_wrapper(ch, 99), 0);

        assert_eq!(channel_recv_wrapper(ch), 42);
        assert_eq!(channel_recv_wrapper(ch), 99);

        // Close and verify.
        channel_close_wrapper(ch);
        assert_eq!(channel_is_closed_wrapper(ch), 1);

        // Recv on closed+empty returns 0.
        assert_eq!(channel_recv_wrapper(ch), 0);

        // Cleanup (rc_dec).
        crate::value::rc_dec(ch as *mut u8);
    }

    #[test]
    fn send_on_closed_returns_neg1() {
        let ch = channel_new_wrapper(4);
        channel_close_wrapper(ch);
        assert_eq!(channel_send_wrapper(ch, 42), -1);

        crate::value::rc_dec(ch as *mut u8);
    }
}

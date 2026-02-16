//! Native task/channel functions for std:task module.
//!
//! Provides task and channel primitives exposed to Vole via `external("std:task")`.
//! Task and channel handles are opaque i64 pointers passed through the FFI
//! boundary, following the same pattern as `std:buffer`.

use crate::channel::{self, RcChannel};
use crate::closure::Closure;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::scheduler;
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

    // task_select2: (ch1: i64, ch2: i64, timeout_nanos: i64) -> i64
    // Returns channel_index (0 or 1) on success, -1 on timeout.
    m.register(
        "task_select2",
        task_select2_wrapper as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // task_select3: (ch1: i64, ch2: i64, ch3: i64, timeout_nanos: i64) -> i64
    // Returns channel_index (0, 1, or 2) on success, -1 on timeout.
    m.register(
        "task_select3",
        task_select3_wrapper as *const u8,
        NativeSignature {
            params: vec![
                NativeType::I64,
                NativeType::I64,
                NativeType::I64,
                NativeType::I64,
            ],
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
// Select wrapper functions
// =============================================================================

/// Select on 2 channels with optional timeout.
///
/// Returns channel_index (0 or 1) if a channel becomes ready,
/// or -1 if the timeout expires. A timeout_nanos of 0 means no timeout.
#[unsafe(no_mangle)]
extern "C" fn task_select2_wrapper(ch1: i64, ch2: i64, timeout_nanos: i64) -> i64 {
    let channels = [ch1 as *mut RcChannel, ch2 as *mut RcChannel];
    task_select_impl(&channels, timeout_nanos)
}

/// Select on 3 channels with optional timeout.
///
/// Returns channel_index (0, 1, or 2) if a channel becomes ready,
/// or -1 if the timeout expires. A timeout_nanos of 0 means no timeout.
#[unsafe(no_mangle)]
extern "C" fn task_select3_wrapper(ch1: i64, ch2: i64, ch3: i64, timeout_nanos: i64) -> i64 {
    let channels = [
        ch1 as *mut RcChannel,
        ch2 as *mut RcChannel,
        ch3 as *mut RcChannel,
    ];
    task_select_impl(&channels, timeout_nanos)
}

/// Core select implementation shared by select2 and select3.
///
/// Follows the Phase 1 Semantics Contract (Section 5):
/// 1. Duplicate channel detection (panic on duplicates).
/// 2. Non-blocking poll phase (lowest-index tie-break).
/// 3. Blocking phase with select-waiter registration.
/// 4. Optional timeout via scheduler timer queue.
fn task_select_impl(channels: &[*mut RcChannel], timeout_nanos: i64) -> i64 {
    // Section 5.6: Reject duplicate channel arguments.
    check_duplicate_channels(channels);

    // Section 5.2: Non-blocking poll phase (lowest-index wins).
    for (i, ch) in channels.iter().enumerate() {
        if channel::channel_has_data(*ch) {
            return i as i64;
        }
    }

    // No channel is immediately ready. If we have no timeout, we must block.
    // If timeout_nanos > 0, we block with a timer.

    // Get current task ID for registering as select-waiter.
    let current_task_id =
        scheduler::with_scheduler(|sched| sched.current_task().map(|id| id.as_raw()));

    let Some(task_id_raw) = current_task_id else {
        // Called from main thread (no current task). Drive the scheduler
        // inline until a channel becomes ready, similar to main_thread_recv_loop.
        return main_thread_select_loop(channels, timeout_nanos);
    };

    // Register as select-waiter on all channels.
    for (i, ch) in channels.iter().enumerate() {
        channel::channel_add_select_waiter(*ch, task_id_raw, i);
    }

    // Block the current task with Select reason.
    scheduler::with_scheduler(|sched| {
        sched.block_current(scheduler::BlockReason::Select);
    });

    // Register timeout timer if specified.
    if timeout_nanos > 0 {
        let deadline =
            std::time::Instant::now() + std::time::Duration::from_nanos(timeout_nanos as u64);
        scheduler::with_scheduler(|sched| {
            sched.register_timer(scheduler::TaskId::from_raw(task_id_raw), deadline);
        });
    }

    // Yield the coroutine back to the scheduler.
    scheduler::yield_current_coroutine();

    // --- Resumed after wakeup ---

    // Read and clear the wakeup source.
    let wakeup = scheduler::with_scheduler(|sched| {
        sched.take_wakeup_source(scheduler::TaskId::from_raw(task_id_raw))
    });

    // Unregister from all channels.
    for ch in channels {
        channel::channel_remove_select_waiter(*ch, task_id_raw);
    }

    match wakeup {
        Some(scheduler::WakeupSource::Channel(index)) => index as i64,
        Some(scheduler::WakeupSource::Timeout) => -1,
        None => {
            // Shouldn't happen in Phase 1 (no spurious wakes), but
            // treat as timeout for safety.
            -1
        }
    }
}

/// Drive the scheduler from the main thread until a channel becomes ready.
///
/// Similar to `main_thread_recv_loop` in channel.rs. The main thread is not
/// a scheduler task, so it pumps the scheduler inline to let producer tasks
/// make progress.
fn main_thread_select_loop(channels: &[*mut RcChannel], timeout_nanos: i64) -> i64 {
    let deadline = if timeout_nanos > 0 {
        Some(std::time::Instant::now() + std::time::Duration::from_nanos(timeout_nanos as u64))
    } else {
        None
    };

    loop {
        // Run one scheduler step to let tasks make progress.
        let has_runnable = scheduler::with_scheduler(|sched| sched.pump_one());

        // Re-check channels after scheduler step.
        for (i, ch) in channels.iter().enumerate() {
            if channel::channel_has_data(*ch) {
                return i as i64;
            }
        }

        // Check timeout.
        if let Some(dl) = deadline
            && std::time::Instant::now() >= dl
        {
            return -1;
        }

        // No runnable tasks and no data: all tasks done or deadlocked.
        if !has_runnable {
            return -1;
        }
    }
}

/// Check for duplicate channel pointers and panic if found.
fn check_duplicate_channels(channels: &[*mut RcChannel]) {
    for i in 0..channels.len() {
        for j in (i + 1)..channels.len() {
            if std::ptr::eq(channels[i], channels[j]) {
                panic!("Task.select: duplicate channel at indices {} and {}", i, j);
            }
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
        assert!(m.get("task_select2").is_some());
        assert!(m.get("task_select3").is_some());
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
    fn task_select2_signature() {
        let m = module();
        let f = m.get("task_select2").unwrap();
        assert_eq!(f.signature.params.len(), 3);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn task_select3_signature() {
        let m = module();
        let f = m.get("task_select3").unwrap();
        assert_eq!(f.signature.params.len(), 4);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn select_poll_finds_buffered_data() {
        // Create two channels, put data in ch2.
        let ch1 = channel_new_wrapper(4);
        let ch2 = channel_new_wrapper(4);

        channel_send_wrapper(ch2, 42);

        // Poll should find ch2 (index 1).
        let result = task_select2_wrapper(ch1, ch2, 0);
        assert_eq!(result, 1);

        crate::value::rc_dec(ch1 as *mut u8);
        crate::value::rc_dec(ch2 as *mut u8);
    }

    #[test]
    fn select_poll_lowest_index_wins() {
        // Both channels have data -- index 0 should win.
        let ch1 = channel_new_wrapper(4);
        let ch2 = channel_new_wrapper(4);

        channel_send_wrapper(ch1, 10);
        channel_send_wrapper(ch2, 20);

        let result = task_select2_wrapper(ch1, ch2, 0);
        assert_eq!(result, 0);

        crate::value::rc_dec(ch1 as *mut u8);
        crate::value::rc_dec(ch2 as *mut u8);
    }

    #[test]
    fn select_poll_closed_channel_is_ready() {
        // A closed channel counts as "ready" (recv returns 0/nil).
        let ch1 = channel_new_wrapper(4);
        let ch2 = channel_new_wrapper(4);

        channel_close_wrapper(ch2);

        let result = task_select2_wrapper(ch1, ch2, 0);
        assert_eq!(result, 1);

        crate::value::rc_dec(ch1 as *mut u8);
        crate::value::rc_dec(ch2 as *mut u8);
    }

    #[test]
    fn select_no_data_returns_neg1_from_main_thread() {
        // From main thread (no current task), if no channel is ready,
        // select returns -1 immediately.
        let ch1 = channel_new_wrapper(4);
        let ch2 = channel_new_wrapper(4);

        let result = task_select2_wrapper(ch1, ch2, 0);
        assert_eq!(result, -1);

        crate::value::rc_dec(ch1 as *mut u8);
        crate::value::rc_dec(ch2 as *mut u8);
    }

    #[test]
    #[should_panic(expected = "duplicate channel")]
    fn select_rejects_duplicate_channels() {
        let ch = channel_new_wrapper(4);
        let channels = [ch as *mut RcChannel, ch as *mut RcChannel];
        check_duplicate_channels(&channels);
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

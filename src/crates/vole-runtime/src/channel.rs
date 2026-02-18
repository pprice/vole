//! RC-managed channel for inter-task communication.
//!
//! Follows the `RcHeader`-fronted allocation pattern used by `RcArray` and
//! `RcInstance`. Integrates with the M:1 scheduler for cooperative blocking
//! on send/recv when the buffer is full/empty.

use std::alloc::{Layout, alloc, dealloc};
use std::collections::VecDeque;
use std::ptr;

use crate::alloc_track;
use crate::scheduler::{self, BlockReason};
use crate::value::{RcHeader, RuntimeTypeId, TaggedValue};

// =============================================================================
// Types
// =============================================================================

/// A task waiting to send or receive on a channel.
#[derive(Debug)]
pub struct WaitingTask {
    /// The scheduler task ID (as u64).
    pub task_id: u64,
    /// For waiting senders: the value they want to send.
    /// For waiting receivers: None (they receive into the return value).
    pub value: Option<TaggedValue>,
}

/// A task waiting in a `select` call on this channel.
#[derive(Debug)]
pub struct SelectWaiter {
    /// The scheduler task ID (as u64).
    pub task_id: u64,
    /// The 0-based index of this channel in the select argument list.
    pub channel_index: usize,
}

/// Owned inner state, heap-allocated via `Box`. NOT `#[repr(C)]` -- only
/// accessed through FFI functions, never from JIT code directly.
pub struct ChannelInner {
    pub buffer: VecDeque<TaggedValue>,
    pub waiting_senders: VecDeque<WaitingTask>,
    pub waiting_receivers: VecDeque<WaitingTask>,
    /// Tasks blocked in `Task.select()` that include this channel.
    pub select_waiters: Vec<SelectWaiter>,
    pub closed: bool,
}

/// Reference-counted channel for inter-task communication.
///
/// `RcHeader` is at offset 0 so the unified RC machinery (`rc_inc`/`rc_dec`)
/// can manage this type. The inner state is heap-allocated via `Box` to keep
/// the outer struct `#[repr(C)]` and fixed-size.
#[repr(C)]
pub struct RcChannel {
    pub header: RcHeader,
    pub capacity: usize,
    pub inner: *mut ChannelInner,
}

// =============================================================================
// Allocation / Deallocation
// =============================================================================

impl RcChannel {
    /// Allocate a new channel.
    ///
    /// `capacity = 0` creates an unbuffered (rendezvous) channel.
    /// `capacity > 0` creates a buffered channel.
    pub fn new(capacity: usize) -> *mut Self {
        let layout = Layout::new::<RcChannel>();

        // SAFETY: `alloc` returns a valid pointer (null check follows). `ptr::write`
        // initializes each field exactly once on the fresh allocation; no double-free
        // or use-after-free.
        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let inner = Box::into_raw(Box::new(ChannelInner {
                buffer: VecDeque::with_capacity(capacity),
                waiting_senders: VecDeque::new(),
                waiting_receivers: VecDeque::new(),
                select_waiters: Vec::new(),
                closed: false,
            }));

            ptr::write(
                &mut (*ptr).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Channel as u32, channel_drop),
            );
            ptr::write(&mut (*ptr).capacity, capacity);
            ptr::write(&mut (*ptr).inner, inner);

            alloc_track::track_alloc(RuntimeTypeId::Channel as u32);
            ptr
        }
    }
}

/// Drop function for RcChannel, called by `rc_dec` when refcount reaches zero.
///
/// Decrements RC for all buffered `TaggedValue` items, drops the inner state
/// (which drops the VecDeques), and deallocates the struct.
///
/// # Safety
/// `ptr` must point to a valid `RcChannel` allocation with refcount already at zero.
unsafe extern "C" fn channel_drop(ptr: *mut u8) {
    alloc_track::track_dealloc(RuntimeTypeId::Channel as u32);
    // SAFETY: Caller (`rc_dec`) guarantees `ptr` is a valid `RcChannel` with refcount
    // zero. `Box::from_raw` reclaims the inner allocation; `dealloc` frees the outer struct.
    unsafe {
        let ch = ptr as *mut RcChannel;
        let inner = &mut *(*ch).inner;

        // Dec all buffered values that may hold RC pointers.
        for tv in inner.buffer.drain(..) {
            tv.rc_dec_if_needed();
        }

        // Dec values held by waiting senders (unbuffered rendezvous values).
        for waiter in inner.waiting_senders.drain(..) {
            if let Some(tv) = waiter.value {
                tv.rc_dec_if_needed();
            }
        }

        // Drop the inner state (VecDeques freed automatically).
        drop(Box::from_raw((*ch).inner));

        let layout = Layout::new::<RcChannel>();
        dealloc(ptr, layout);
    }
}

// =============================================================================
// Channel operations
// =============================================================================

/// Send a value on a buffered channel.
///
/// **Ownership**: the caller transfers ownership of `tv` to this function.
/// On success the channel (buffer, transfer slot, or waiting-sender queue)
/// takes over the reference. On failure (channel closed) this function
/// calls `rc_dec_if_needed` so the caller must NOT dec again.
///
/// Returns 0 on success, -1 if the channel is closed.
fn buffered_send(inner: &mut ChannelInner, capacity: usize, tv: TaggedValue) -> i64 {
    if inner.closed {
        // Ownership semantics: caller transferred ownership, we must dec.
        tv.rc_dec_if_needed();
        return -1;
    }

    // If a receiver is waiting, hand the value directly (fast path).
    if let Some(waiter) = inner.waiting_receivers.pop_front() {
        // Store value on the receiver's per-task transfer slot.
        let receiver_id = scheduler::TaskId::from_raw(waiter.task_id);
        scheduler::with_scheduler(|sched| {
            sched.set_transfer_value(receiver_id, tv);
            sched.unblock(receiver_id);
        });
        return 0;
    }

    // If buffer has room, enqueue.
    if inner.buffer.len() < capacity {
        inner.buffer.push_back(tv);
        // Notify any select-waiters that data is now available.
        notify_select_waiters(inner);
        return 0;
    }

    // Buffer full: block current task, enqueue as waiting sender.
    let task_id = scheduler::with_scheduler(|sched| {
        sched
            .block_current(BlockReason::ChannelSend)
            .map(|id| id.as_raw())
    });

    if let Some(tid) = task_id {
        inner.waiting_senders.push_back(WaitingTask {
            task_id: tid,
            value: Some(tv),
        });
        // Yield the coroutine back to the scheduler. When this task is
        // unblocked (a receiver consumes a value), it will resume here.
        scheduler::yield_current_coroutine();
    }

    0
}

/// Send a value on an unbuffered (rendezvous) channel.
///
/// **Ownership**: same contract as `buffered_send` — caller transfers
/// ownership; on failure the value is `rc_dec`'d here.
///
/// Returns 0 on success, -1 if the channel is closed.
fn unbuffered_send(inner: &mut ChannelInner, tv: TaggedValue) -> i64 {
    if inner.closed {
        tv.rc_dec_if_needed();
        return -1;
    }

    // If a receiver is waiting, hand value directly.
    if let Some(waiter) = inner.waiting_receivers.pop_front() {
        let receiver_id = scheduler::TaskId::from_raw(waiter.task_id);
        scheduler::with_scheduler(|sched| {
            sched.set_transfer_value(receiver_id, tv);
            sched.unblock(receiver_id);
        });
        return 0;
    }

    // No receiver: block current task, store value with the waiter.
    let task_id = scheduler::with_scheduler(|sched| {
        sched
            .block_current(BlockReason::ChannelSend)
            .map(|id| id.as_raw())
    });

    if let Some(tid) = task_id {
        inner.waiting_senders.push_back(WaitingTask {
            task_id: tid,
            value: Some(tv),
        });
        // Notify select-waiters: the sender's value is available for
        // rendezvous. When the select-woken task does recv, it will
        // find this waiting sender.
        notify_select_waiters(inner);
        // Yield the coroutine back to the scheduler.
        scheduler::yield_current_coroutine();
    }

    0
}

/// Receive a value from the channel.
///
/// **Ownership**: on success the caller receives ownership of the value
/// (transferred from the buffer, waiting sender, or transfer slot).
/// No `rc_inc` is performed — this is a move, not a copy. The caller
/// is responsible for eventually calling `rc_dec` when done with the value.
///
/// On success, writes the tag and value to `out_tag` and `out_value` and
/// returns the tag. Returns -1 if the channel is closed and empty.
fn channel_recv_impl(
    inner: &mut ChannelInner,
    capacity: usize,
    out_tag: &mut i64,
    out_value: &mut i64,
) -> i64 {
    // If buffer has data, pop it.
    if let Some(tv) = inner.buffer.pop_front() {
        // Wake one waiting sender if any (they can now fill the slot).
        wake_one_sender(inner);
        *out_tag = tv.tag as i64;
        *out_value = tv.value as i64;
        return tv.tag as i64;
    }

    // For unbuffered: check if a sender is waiting with a value.
    if capacity == 0
        && let Some(waiter) = inner.waiting_senders.pop_front()
        && let Some(tv) = waiter.value
    {
        *out_tag = tv.tag as i64;
        *out_value = tv.value as i64;
        // Wake the sender.
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
        return tv.tag as i64;
    }

    // Buffer empty: if closed, signal done.
    if inner.closed {
        return -1;
    }

    // Block current task as a waiting receiver.
    let task_id = scheduler::with_scheduler(|sched| {
        sched
            .block_current(BlockReason::ChannelRecv)
            .map(|id| id.as_raw())
    });

    if let Some(tid) = task_id {
        inner.waiting_receivers.push_back(WaitingTask {
            task_id: tid,
            value: None,
        });
        // Yield the coroutine back to the scheduler. When a sender provides
        // a value (or the channel closes), this task is unblocked and resumes.
        scheduler::yield_current_coroutine();
    }

    // After being woken, the value was placed in the current task's transfer slot.
    let tv = scheduler::with_scheduler(|sched| sched.take_current_transfer_value());
    if let Some(tv) = tv {
        *out_tag = tv.tag as i64;
        *out_value = tv.value as i64;
        tv.tag as i64
    } else {
        // Woken due to close -- no value available.
        -1
    }
}

/// Notify select-waiters that this channel has data available.
///
/// Called after a successful buffered send or unbuffered rendezvous that
/// leaves data for a select-waiter. Wakes select-waiters and sets their
/// `WakeupSource` to the channel's index in their select argument list.
fn notify_select_waiters(inner: &mut ChannelInner) {
    // Wake all select-waiters for this channel. Each select-waiter will
    // compete to recv; the scheduler's cooperative model ensures only one
    // actually gets the value, and the others will re-block or find
    // nothing and continue.
    // In practice, for Phase 1 M:1, there's typically at most one
    // select-waiter per channel.
    for waiter in inner.select_waiters.drain(..) {
        scheduler::with_scheduler(|sched| {
            sched.set_wakeup_source(
                scheduler::TaskId::from_raw(waiter.task_id),
                scheduler::WakeupSource::Channel(waiter.channel_index),
            );
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
    }
}

/// Wake one waiting sender and move its value into the buffer.
fn wake_one_sender(inner: &mut ChannelInner) {
    if let Some(waiter) = inner.waiting_senders.pop_front() {
        if let Some(tv) = waiter.value {
            inner.buffer.push_back(tv);
        }
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
    }
}

/// Close the channel: mark closed, wake all waiting tasks.
fn channel_close_impl(inner: &mut ChannelInner) {
    if inner.closed {
        return; // Double-close is no-op (Section 3.4).
    }
    inner.closed = true;

    // Wake all waiting receivers.
    let receivers: Vec<WaitingTask> = inner.waiting_receivers.drain(..).collect();
    for waiter in receivers {
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
    }

    // Wake all waiting senders (they will see closed and return -1).
    let senders: Vec<WaitingTask> = inner.waiting_senders.drain(..).collect();
    for waiter in senders {
        // Dec the value the sender was trying to send.
        if let Some(tv) = waiter.value {
            tv.rc_dec_if_needed();
        }
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
    }

    // Wake all select-waiters. They will see the channel is closed
    // and handle it accordingly (either recv remaining data or return).
    notify_select_waiters(inner);
}

// =============================================================================
// Select support
// =============================================================================

/// Check if a channel has data available for a non-blocking recv.
///
/// Returns `true` if the buffer is non-empty, or (for unbuffered channels)
/// if a sender is waiting with a value, or if the channel is closed.
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub fn channel_has_data(ch: *mut RcChannel) -> bool {
    // SAFETY: Caller guarantees `ch` is a valid, live `RcChannel` pointer.
    // Dereferencing `inner` for read-only access is safe while no mutable alias exists.
    unsafe {
        let inner = &*(*ch).inner;
        let capacity = (*ch).capacity;
        !inner.buffer.is_empty()
            || (capacity == 0 && !inner.waiting_senders.is_empty())
            || inner.closed
    }
}

/// Register a select-waiter on a channel.
///
/// The waiter will be notified (woken) when data becomes available
/// on this channel.
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub fn channel_add_select_waiter(ch: *mut RcChannel, task_id: u64, channel_index: usize) {
    // SAFETY: Caller guarantees `ch` is a valid, live `RcChannel` pointer. Exclusive
    // access to `inner` is safe as channel operations are single-threaded (cooperative scheduler).
    unsafe {
        let inner = &mut *(*ch).inner;
        inner.select_waiters.push(SelectWaiter {
            task_id,
            channel_index,
        });
    }
}

/// Remove a select-waiter from a channel.
///
/// Called by the select implementation after wakeup to unregister from
/// channels that were NOT the wakeup source.
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub fn channel_remove_select_waiter(ch: *mut RcChannel, task_id: u64) {
    // SAFETY: Caller guarantees `ch` is a valid, live `RcChannel` pointer. Exclusive
    // access to `inner` is safe as channel operations are single-threaded.
    unsafe {
        let inner = &mut *(*ch).inner;
        inner.select_waiters.retain(|w| w.task_id != task_id);
    }
}

// =============================================================================
// FFI functions
// =============================================================================

/// Allocate a new channel.
///
/// `capacity = 0` creates an unbuffered (rendezvous) channel.
/// `capacity > 0` creates a buffered channel.
#[unsafe(no_mangle)]
pub extern "C" fn vole_channel_new(capacity: i64) -> *mut RcChannel {
    RcChannel::new(capacity.max(0) as usize)
}

/// Send a tagged value on a channel.
///
/// Returns 0 on success, -1 if the channel is closed.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_send(ch: *mut RcChannel, tag: i64, value: i64) -> i64 {
    let tv = TaggedValue {
        tag: tag as u64,
        value: value as u64,
    };

    // SAFETY: JIT contract guarantees `ch` is a valid, live `RcChannel` pointer. Exclusive
    // access to `inner` is safe as channel operations run on the cooperative scheduler's
    // single thread.
    unsafe {
        let inner = &mut *(*ch).inner;
        let capacity = (*ch).capacity;

        if capacity == 0 {
            unbuffered_send(inner, tv)
        } else {
            buffered_send(inner, capacity, tv)
        }
    }
}

/// Receive a tagged value from a channel.
///
/// Writes the received value to the `out` buffer (2 x i64: [tag, value]).
/// Returns the tag on success, -1 if the channel is closed and empty.
///
/// When called from the main thread (no current task), drives the scheduler
/// in a loop until data is available or the channel is closed. This allows
/// patterns like `for v in ch.iter()` from the main thread to interleave
/// with producer tasks.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_recv(ch: *mut RcChannel, out: *mut i64) -> i64 {
    // SAFETY: JIT contract guarantees `ch` is a valid `RcChannel` and `out` points to a
    // 2-element i64 buffer. Exclusive `inner` access is safe under cooperative scheduling.
    unsafe {
        let inner = &mut *(*ch).inner;
        let capacity = (*ch).capacity;
        let out_tag = &mut *out;
        let out_value = &mut *out.add(1);

        // Fast path: buffer has data or we're within a task (cooperative blocking).
        let has_current_task = scheduler::with_scheduler(|sched| sched.current_task().is_some());
        if has_current_task || !inner.buffer.is_empty() || inner.closed {
            return channel_recv_impl(inner, capacity, out_tag, out_value);
        }

        // For unbuffered: check if a sender is waiting.
        if capacity == 0 && !inner.waiting_senders.is_empty() {
            return channel_recv_impl(inner, capacity, out_tag, out_value);
        }

        // Main-thread path: drive the scheduler until data arrives or channel closes.
        // Drop the inner reference before pumping the scheduler, then re-check.
        let _ = inner;
        main_thread_recv_loop(ch, out)
    }
}

/// Drive the scheduler from the main thread until the channel has data or closes.
///
/// This is analogous to `run_until_done` for task join: the main thread is not
/// a scheduler task, so it must pump the scheduler inline to let producer tasks
/// make progress.
fn main_thread_recv_loop(ch: *mut RcChannel, out: *mut i64) -> i64 {
    loop {
        // Run one scheduler step to let tasks make progress.
        let has_runnable = scheduler::with_scheduler(|sched| sched.pump_one());

        // Re-check channel state after scheduler step.
        // SAFETY: `ch` is a valid `RcChannel` (passed from `vole_channel_recv`). `out`
        // points to a 2-element i64 buffer. Re-borrowing `inner` after dropping the
        // previous reference is safe.
        unsafe {
            let inner = &mut *(*ch).inner;
            let capacity = (*ch).capacity;

            // Data available in buffer?
            if !inner.buffer.is_empty() {
                let out_tag = &mut *out;
                let out_value = &mut *out.add(1);
                return channel_recv_impl(inner, capacity, out_tag, out_value);
            }

            // Unbuffered with a waiting sender?
            if capacity == 0 && !inner.waiting_senders.is_empty() {
                let out_tag = &mut *out;
                let out_value = &mut *out.add(1);
                return channel_recv_impl(inner, capacity, out_tag, out_value);
            }

            // Channel closed?
            if inner.closed {
                return -1;
            }
        }

        // No runnable tasks and no data -- all tasks done or deadlocked.
        // pump_one already panics on deadlock, so if we get here with
        // !has_runnable, all tasks completed without producing data.
        if !has_runnable {
            return -1;
        }
    }
}

/// Close a channel. Wakes all waiting tasks.
///
/// Double-close is a no-op (Section 3.4).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_close(ch: *mut RcChannel) {
    // SAFETY: JIT contract guarantees `ch` is a valid, live `RcChannel` pointer. Exclusive
    // `inner` access is safe under cooperative scheduling.
    unsafe {
        let inner = &mut *(*ch).inner;
        channel_close_impl(inner);
    }
}

/// Check if a channel is closed.
///
/// Returns 1 if closed, 0 otherwise.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_is_closed(ch: *const RcChannel) -> i8 {
    // SAFETY: JIT contract guarantees `ch` is a valid, live `RcChannel` pointer. Read-only
    // access to `inner.closed` requires no exclusive borrow.
    unsafe {
        let inner = &*(*ch).inner;
        i8::from(inner.closed)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{rc_dec, rc_inc};
    use std::sync::Mutex;

    // Channel tests manipulate global alloc-tracking state; serialize them.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn buffered_send_recv_fifo() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            // Send 3 i64 values.
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            let tv1 = TaggedValue::from_i64(10);
            let tv2 = TaggedValue::from_i64(20);
            let tv3 = TaggedValue::from_i64(30);

            assert_eq!(buffered_send(inner, cap, tv1), 0);
            assert_eq!(buffered_send(inner, cap, tv2), 0);
            assert_eq!(buffered_send(inner, cap, tv3), 0);

            // Recv in FIFO order.
            let mut tag: i64 = 0;
            let mut val: i64 = 0;
            assert_eq!(
                channel_recv_impl(inner, cap, &mut tag, &mut val),
                RuntimeTypeId::I64 as i64
            );
            assert_eq!(val, 10);
            assert_eq!(
                channel_recv_impl(inner, cap, &mut tag, &mut val),
                RuntimeTypeId::I64 as i64
            );
            assert_eq!(val, 20);
            assert_eq!(
                channel_recv_impl(inner, cap, &mut tag, &mut val),
                RuntimeTypeId::I64 as i64
            );
            assert_eq!(val, 30);

            // Clean up.
            rc_dec(ch as *mut u8);
        }
    }

    #[test]
    fn send_on_closed_returns_neg1() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            channel_close_impl(inner);
            assert_eq!(buffered_send(inner, cap, TaggedValue::from_i64(42)), -1);

            rc_dec(ch as *mut u8);
        }
    }

    #[test]
    fn recv_on_closed_empty_returns_neg1() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            channel_close_impl(inner);

            let mut tag: i64 = 0;
            let mut val: i64 = 0;
            assert_eq!(channel_recv_impl(inner, cap, &mut tag, &mut val), -1);

            rc_dec(ch as *mut u8);
        }
    }

    #[test]
    fn recv_drains_before_neg1_on_close() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            // Send some values then close.
            buffered_send(inner, cap, TaggedValue::from_i64(1));
            buffered_send(inner, cap, TaggedValue::from_i64(2));
            channel_close_impl(inner);

            // Should still be able to recv the buffered values.
            let mut tag: i64 = 0;
            let mut val: i64 = 0;

            assert_eq!(
                channel_recv_impl(inner, cap, &mut tag, &mut val),
                RuntimeTypeId::I64 as i64
            );
            assert_eq!(val, 1);
            assert_eq!(
                channel_recv_impl(inner, cap, &mut tag, &mut val),
                RuntimeTypeId::I64 as i64
            );
            assert_eq!(val, 2);

            // Now empty + closed: -1.
            assert_eq!(channel_recv_impl(inner, cap, &mut tag, &mut val), -1);

            rc_dec(ch as *mut u8);
        }
    }

    #[test]
    fn double_close_is_noop() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            channel_close_impl(inner);
            channel_close_impl(inner); // Should not panic.
            assert!(inner.closed);

            rc_dec(ch as *mut u8);
        }
    }

    #[test]
    fn channel_is_closed_ffi() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        assert_eq!(vole_channel_is_closed(ch), 0);
        vole_channel_close(ch);
        assert_eq!(vole_channel_is_closed(ch), 1);

        rc_dec(ch as *mut u8);
    }

    #[test]
    fn alloc_tracking_balanced() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        alloc_track::enable_tracking();
        let before = alloc_track::count(RuntimeTypeId::Channel as u32);

        let ch = RcChannel::new(4);
        assert_eq!(
            alloc_track::count(RuntimeTypeId::Channel as u32) - before,
            1
        );

        rc_dec(ch as *mut u8);
        assert_eq!(
            alloc_track::count(RuntimeTypeId::Channel as u32) - before,
            0
        );
    }

    #[test]
    fn drop_cleanup_decs_buffered_values() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            // Create an RC value (a string), inc it, send it.
            let s = crate::string::RcString::new("hello");
            // s starts with refcount 1. Inc to 2 so we can track dec.
            rc_inc(s as *mut u8);

            let tv = TaggedValue::from_string(s);
            buffered_send(inner, cap, tv);

            // String refcount should be 2 (original + our inc).
            let header = &*(s as *const RcHeader);
            assert_eq!(
                header.ref_count.load(std::sync::atomic::Ordering::Relaxed),
                2
            );

            // Drop the channel -- should dec the buffered string.
            rc_dec(ch as *mut u8);

            // String refcount should now be 1 (our inc remains).
            assert_eq!(
                header.ref_count.load(std::sync::atomic::Ordering::Relaxed),
                1
            );

            // Final cleanup.
            rc_dec(s as *mut u8);
        }
    }

    #[test]
    fn ffi_new_returns_valid_channel() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = vole_channel_new(8);
        assert!(!ch.is_null());

        unsafe {
            assert_eq!((*ch).capacity, 8);
            let inner = &*(*ch).inner;
            assert!(!inner.closed);
            assert!(inner.buffer.is_empty());

            rc_dec(ch as *mut u8);
        }
    }

    /// Helper: create an RcString with an extra rc_inc so we can inspect
    /// the refcount after the channel operations dec it.
    unsafe fn make_tracked_string(s: &str) -> (*mut crate::string::RcString, *const RcHeader) {
        let ptr = crate::string::RcString::new(s);
        // Starts at refcount 1. Inc to 2 so we retain a "tracking" ref.
        rc_inc(ptr as *mut u8);
        let header = ptr as *const RcHeader;
        (ptr, header)
    }

    /// Read the current refcount of an RcHeader.
    unsafe fn refcount(header: *const RcHeader) -> u32 {
        unsafe {
            (*header)
                .ref_count
                .load(std::sync::atomic::Ordering::Relaxed)
        }
    }

    #[test]
    fn send_rc_on_closed_channel_decs_value() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;
            channel_close_impl(inner);

            let (s, hdr) = make_tracked_string("closed-send");
            assert_eq!(refcount(hdr), 2);

            // Send on closed channel should dec the value.
            let tv = TaggedValue::from_string(s);
            assert_eq!(buffered_send(inner, cap, tv), -1);

            // Channel consumed & dec'd its copy; our tracking ref remains.
            assert_eq!(refcount(hdr), 1);

            rc_dec(ch as *mut u8);
            rc_dec(s as *mut u8); // Drop our tracking ref.
        }
    }

    #[test]
    fn close_decs_waiting_sender_rc_values() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;

            // Simulate a waiting sender with an RC value (as if the
            // channel buffer were full and the sender blocked).
            let (s, hdr) = make_tracked_string("waiting-sender");
            assert_eq!(refcount(hdr), 2);

            inner.waiting_senders.push_back(WaitingTask {
                task_id: 999, // Fake task ID; close won't find it in
                // scheduler but that only means unblock is skipped.
                value: Some(TaggedValue::from_string(s)),
            });

            // Close should dec the waiting sender's value.
            channel_close_impl(inner);
            assert_eq!(refcount(hdr), 1);

            rc_dec(ch as *mut u8);
            rc_dec(s as *mut u8);
        }
    }

    #[test]
    fn buffered_send_recv_rc_roundtrip() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            let (s, hdr) = make_tracked_string("roundtrip");
            assert_eq!(refcount(hdr), 2);

            // Send transfers ownership into the buffer (no extra inc).
            buffered_send(inner, cap, TaggedValue::from_string(s));
            assert_eq!(refcount(hdr), 2);

            // Recv transfers ownership out of the buffer to the receiver.
            let mut tag: i64 = 0;
            let mut val: i64 = 0;
            let result_tag = channel_recv_impl(inner, cap, &mut tag, &mut val);
            assert_eq!(result_tag, RuntimeTypeId::String as i64);
            assert_eq!(val, s as i64);
            // Refcount unchanged — ownership transferred, not copied.
            assert_eq!(refcount(hdr), 2);

            // The receiver now owns the value. Dec it to simulate
            // the receiver's scope ending.
            rc_dec(val as *mut u8);
            assert_eq!(refcount(hdr), 1);

            rc_dec(ch as *mut u8);
            rc_dec(s as *mut u8);
        }
    }

    #[test]
    fn drop_decs_multiple_buffered_rc_values() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            let (s1, hdr1) = make_tracked_string("alpha");
            let (s2, hdr2) = make_tracked_string("beta");
            let (s3, hdr3) = make_tracked_string("gamma");

            buffered_send(inner, cap, TaggedValue::from_string(s1));
            buffered_send(inner, cap, TaggedValue::from_string(s2));
            buffered_send(inner, cap, TaggedValue::from_string(s3));

            assert_eq!(refcount(hdr1), 2);
            assert_eq!(refcount(hdr2), 2);
            assert_eq!(refcount(hdr3), 2);

            // Drop the channel — all three strings should be dec'd.
            rc_dec(ch as *mut u8);

            assert_eq!(refcount(hdr1), 1);
            assert_eq!(refcount(hdr2), 1);
            assert_eq!(refcount(hdr3), 1);

            rc_dec(s1 as *mut u8);
            rc_dec(s2 as *mut u8);
            rc_dec(s3 as *mut u8);
        }
    }

    #[test]
    fn recv_then_drop_no_double_dec() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(4);

        unsafe {
            let inner = &mut *(*ch).inner;
            let cap = (*ch).capacity;

            let (s, hdr) = make_tracked_string("no-double-dec");
            assert_eq!(refcount(hdr), 2);

            buffered_send(inner, cap, TaggedValue::from_string(s));

            // Recv the value (ownership transfer out of buffer).
            let mut tag: i64 = 0;
            let mut val: i64 = 0;
            channel_recv_impl(inner, cap, &mut tag, &mut val);
            assert_eq!(refcount(hdr), 2);

            // Drop channel — buffer is now empty, so no dec from channel.
            rc_dec(ch as *mut u8);
            // Refcount should still be 2: one from recv, one from tracking.
            assert_eq!(refcount(hdr), 2);

            // Clean up both refs.
            rc_dec(val as *mut u8);
            assert_eq!(refcount(hdr), 1);
            rc_dec(s as *mut u8);
        }
    }

    #[test]
    fn unbuffered_send_on_closed_decs_rc_value() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let ch = RcChannel::new(0); // unbuffered

        unsafe {
            let inner = &mut *(*ch).inner;
            channel_close_impl(inner);

            let (s, hdr) = make_tracked_string("unbuf-closed");
            assert_eq!(refcount(hdr), 2);

            let tv = TaggedValue::from_string(s);
            assert_eq!(unbuffered_send(inner, tv), -1);

            // Value should have been dec'd by the failed send.
            assert_eq!(refcount(hdr), 1);

            rc_dec(ch as *mut u8);
            rc_dec(s as *mut u8);
        }
    }
}

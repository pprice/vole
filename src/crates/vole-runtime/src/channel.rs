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

/// Owned inner state, heap-allocated via `Box`. NOT `#[repr(C)]` -- only
/// accessed through FFI functions, never from JIT code directly.
pub struct ChannelInner {
    pub buffer: VecDeque<TaggedValue>,
    pub waiting_senders: VecDeque<WaitingTask>,
    pub waiting_receivers: VecDeque<WaitingTask>,
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

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let inner = Box::into_raw(Box::new(ChannelInner {
                buffer: VecDeque::with_capacity(capacity),
                waiting_senders: VecDeque::new(),
                waiting_receivers: VecDeque::new(),
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
/// Returns 0 on success, -1 if the channel is closed.
fn buffered_send(inner: &mut ChannelInner, capacity: usize, tv: TaggedValue) -> i64 {
    if inner.closed {
        // Ownership semantics: caller transferred ownership, we must dec.
        tv.rc_dec_if_needed();
        return -1;
    }

    // If a receiver is waiting, hand the value directly (fast path).
    if let Some(waiter) = inner.waiting_receivers.pop_front() {
        // Store value in a thread-local for the receiver to pick up.
        set_transfer_value(tv);
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
        });
        return 0;
    }

    // If buffer has room, enqueue.
    if inner.buffer.len() < capacity {
        inner.buffer.push_back(tv);
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
    }

    0
}

/// Send a value on an unbuffered (rendezvous) channel.
///
/// Returns 0 on success, -1 if the channel is closed.
fn unbuffered_send(inner: &mut ChannelInner, tv: TaggedValue) -> i64 {
    if inner.closed {
        tv.rc_dec_if_needed();
        return -1;
    }

    // If a receiver is waiting, hand value directly.
    if let Some(waiter) = inner.waiting_receivers.pop_front() {
        set_transfer_value(tv);
        scheduler::with_scheduler(|sched| {
            sched.unblock(scheduler::TaskId::from_raw(waiter.task_id));
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
    }

    0
}

/// Receive a value from the channel.
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
    }

    // After being woken, the value was placed in the transfer slot.
    let tv = take_transfer_value();
    if let Some(tv) = tv {
        *out_tag = tv.tag as i64;
        *out_value = tv.value as i64;
        tv.tag as i64
    } else {
        // Woken due to close -- no value available.
        -1
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
}

// =============================================================================
// Transfer slot (thread-local)
// =============================================================================

use std::cell::RefCell;

thread_local! {
    /// Transfer slot for passing a value from sender to receiver when the
    /// receiver was blocked. Set by the sender, consumed by the receiver
    /// after being woken.
    static TRANSFER_VALUE: RefCell<Option<TaggedValue>> = const { RefCell::new(None) };
}

fn set_transfer_value(tv: TaggedValue) {
    TRANSFER_VALUE.with(|cell| {
        *cell.borrow_mut() = Some(tv);
    });
}

fn take_transfer_value() -> Option<TaggedValue> {
    TRANSFER_VALUE.with(|cell| cell.borrow_mut().take())
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
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_recv(ch: *mut RcChannel, out: *mut i64) -> i64 {
    unsafe {
        let inner = &mut *(*ch).inner;
        let capacity = (*ch).capacity;
        let out_tag = &mut *out;
        let out_value = &mut *out.add(1);
        channel_recv_impl(inner, capacity, out_tag, out_value)
    }
}

/// Close a channel. Wakes all waiting tasks.
///
/// Double-close is a no-op (Section 3.4).
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_channel_close(ch: *mut RcChannel) {
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
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
        let ch = RcChannel::new(4);

        assert_eq!(vole_channel_is_closed(ch), 0);
        vole_channel_close(ch);
        assert_eq!(vole_channel_is_closed(ch), 1);

        rc_dec(ch as *mut u8);
    }

    #[test]
    fn alloc_tracking_balanced() {
        let _guard = TEST_LOCK.lock().unwrap();
        alloc_track::enable_tracking();
        let snap = alloc_track::snapshot();

        let ch = RcChannel::new(4);
        assert_eq!(alloc_track::delta(snap), 1);

        rc_dec(ch as *mut u8);
        assert_eq!(alloc_track::delta(snap), 0);
    }

    #[test]
    fn drop_cleanup_decs_buffered_values() {
        let _guard = TEST_LOCK.lock().unwrap();
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
        let _guard = TEST_LOCK.lock().unwrap();
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
}

//! RC-managed task handle for green thread tasks.
//!
//! `RcTask` follows the `RcHeader`-fronted allocation pattern used by `RcArray`,
//! `RcChannel`, and other RC types. It wraps a scheduler `TaskId` and provides
//! a Vole-visible handle for join/cancel operations.

use std::alloc::{Layout, alloc, dealloc};
use std::cell::Cell;

use crate::alloc_track;
use crate::scheduler::{self, TaskId};
use crate::value::{RcHeader, RuntimeTypeId};

// =============================================================================
// Types
// =============================================================================

/// Reference-counted task handle.
///
/// `RcHeader` is at offset 0 so the unified RC machinery (`rc_inc`/`rc_dec`)
/// can manage this type. The task itself lives in the scheduler; this is just
/// a handle.
#[repr(C)]
pub struct RcTask {
    pub header: RcHeader,
    /// The scheduler task ID.
    pub task_id: Cell<u64>,
    /// Join result (all Phase 1 values fit i64, per vol-08mi).
    pub result: Cell<i64>,
    /// Whether the task has completed.
    pub completed: Cell<bool>,
}

// =============================================================================
// Allocation / Deallocation
// =============================================================================

impl RcTask {
    /// Allocate a new RcTask wrapping a scheduler task.
    pub fn new(task_id: TaskId) -> *mut Self {
        let layout = Layout::new::<RcTask>();
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        let task = ptr as *mut RcTask;
        unsafe {
            std::ptr::write(
                &raw mut (*task).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Task as u32, task_drop),
            );
            (*task).task_id = Cell::new(task_id.as_raw());
            (*task).result = Cell::new(0);
            (*task).completed = Cell::new(false);
        }

        alloc_track::track_alloc(RuntimeTypeId::Task as u32);
        task
    }
}

/// Drop function for `RcTask`.
///
/// Called when the reference count reaches zero. Cancels the underlying
/// scheduler task if it is still running, then frees the allocation.
extern "C" fn task_drop(ptr: *mut u8) {
    let task = ptr as *mut RcTask;

    // Cancel the underlying scheduler task if still running.
    let task_id = unsafe { (*task).task_id.get() };
    if !unsafe { (*task).completed.get() } {
        scheduler::with_scheduler(|sched| {
            let tid = TaskId::from_raw(task_id);
            if !sched.is_done(tid) {
                sched.cancel(tid);
            }
        });
    }

    // Free the allocation.
    let layout = Layout::new::<RcTask>();
    unsafe { dealloc(ptr, layout) };
    alloc_track::track_dealloc(RuntimeTypeId::Task as u32);
}

// =============================================================================
// FFI functions
// =============================================================================

/// Spawn a new task. Takes a closure pointer and function pointer.
///
/// Returns an `*mut RcTask` as i64 (opaque handle for Vole).
///
/// The closure_ptr should be the Vole closure pointer, and body_fn should
/// be the function pointer extracted from the closure.
#[unsafe(no_mangle)]
pub extern "C" fn vole_rctask_run(body_fn: *const u8, closure_ptr: *const u8) -> *mut RcTask {
    let task_id = scheduler::with_scheduler(|sched| sched.spawn(body_fn, closure_ptr));
    RcTask::new(task_id)
}

/// Join: block until the task completes, return its result.
///
/// If the task already completed, returns immediately.
/// If the task panicked, propagates the panic.
/// If the task was cancelled, panics with "joined task was cancelled".
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_rctask_join(task_ptr: *mut RcTask) -> i64 {
    if task_ptr.is_null() {
        return 0;
    }

    let task_id = unsafe { (*task_ptr).task_id.get() };
    let tid = TaskId::from_raw(task_id);

    let result = scheduler::with_scheduler(|sched| sched.join(tid));

    // Mark the handle as completed and cache the result.
    unsafe {
        (*task_ptr).completed.set(true);
        (*task_ptr).result.set(result);
    }

    result
}

/// Cancel a task.
///
/// If the task is already completed or cancelled, this is a no-op.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_rctask_cancel(task_ptr: *mut RcTask) {
    if task_ptr.is_null() {
        return;
    }

    let task_id = unsafe { (*task_ptr).task_id.get() };
    let tid = TaskId::from_raw(task_id);

    scheduler::with_scheduler(|sched| {
        sched.cancel(tid);
    });

    unsafe {
        (*task_ptr).completed.set(true);
    }
}

/// Check if a task is done (completed or cancelled).
///
/// Returns 1 if done, 0 otherwise.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_rctask_is_done(task_ptr: *const RcTask) -> i64 {
    if task_ptr.is_null() {
        return 1;
    }

    // Check cached completed flag first.
    if unsafe { (*task_ptr).completed.get() } {
        return 1;
    }

    // Check with the scheduler.
    let task_id = unsafe { (*task_ptr).task_id.get() };
    let done = scheduler::with_scheduler(|sched| sched.is_done(TaskId::from_raw(task_id)));

    if done {
        unsafe { (*task_ptr).completed.set(true) };
    }

    i64::from(done)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::rc_dec;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicI64, Ordering};

    // Task tests use the global alloc-tracking counters and the thread-local
    // scheduler singleton; serialize them to avoid cross-test pollution.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn rctask_creation_and_drop() {
        let _guard = TEST_LOCK.lock().unwrap();
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks from previous tests on this thread.
        scheduler::with_scheduler(|sched| sched.run());

        let snap = alloc_track::snapshot();

        let tid = scheduler::with_scheduler(|sched| {
            extern "C" fn body(_c: *const u8, _y: *const u8) {}
            sched.spawn(body as *const u8, std::ptr::null())
        });

        let task = RcTask::new(tid);
        assert!(!task.is_null());

        // Run scheduler to complete the task.
        scheduler::with_scheduler(|sched| sched.run());

        // Drop via rc_dec.
        rc_dec(task as *mut u8);
        assert_eq!(alloc_track::delta(snap), 0);
    }

    #[test]
    fn rctask_type_id() {
        assert_eq!(RuntimeTypeId::Task as u32, 10);
        assert_eq!(RuntimeTypeId::from_u32(10), Some(RuntimeTypeId::Task));
        assert_eq!(RuntimeTypeId::Task.name(), "Task");
    }

    #[test]
    fn vole_rctask_run_returns_handle() {
        let _guard = TEST_LOCK.lock().unwrap();
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        static FLAG: AtomicI64 = AtomicI64::new(0);
        FLAG.store(0, Ordering::SeqCst);

        extern "C" fn body(_c: *const u8, _y: *const u8) {
            FLAG.store(42, Ordering::SeqCst);
        }

        let task = vole_rctask_run(body as *const u8, std::ptr::null());
        assert!(!task.is_null());

        // Task hasn't run yet (scheduler not driven).
        assert_eq!(FLAG.load(Ordering::SeqCst), 0);

        // Drive the scheduler.
        scheduler::with_scheduler(|sched| sched.run());

        assert_eq!(FLAG.load(Ordering::SeqCst), 42);

        // Cleanup.
        rc_dec(task as *mut u8);
    }

    #[test]
    fn vole_rctask_cancel_handle() {
        let _guard = TEST_LOCK.lock().unwrap();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn body(_c: *const u8, _y: *const u8) {
            RAN.store(1, Ordering::SeqCst);
        }

        let task = vole_rctask_run(body as *const u8, std::ptr::null());
        vole_rctask_cancel(task);

        // Drive the scheduler.
        scheduler::with_scheduler(|sched| sched.run());

        // Task should not have run.
        assert_eq!(RAN.load(Ordering::SeqCst), 0);
        assert_eq!(vole_rctask_is_done(task), 1);

        rc_dec(task as *mut u8);
    }

    #[test]
    fn vole_rctask_is_done_before_and_after_run() {
        let _guard = TEST_LOCK.lock().unwrap();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        extern "C" fn body(_c: *const u8, _y: *const u8) {}

        let task = vole_rctask_run(body as *const u8, std::ptr::null());

        // Before run: not done.
        assert_eq!(vole_rctask_is_done(task), 0);

        // Run scheduler.
        scheduler::with_scheduler(|sched| sched.run());

        // After run: done.
        assert_eq!(vole_rctask_is_done(task), 1);

        rc_dec(task as *mut u8);
    }

    #[test]
    fn alloc_tracking_balanced() {
        let _guard = TEST_LOCK.lock().unwrap();
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        let snap = alloc_track::snapshot();

        extern "C" fn body(_c: *const u8, _y: *const u8) {}

        let tasks: Vec<*mut RcTask> = (0..5)
            .map(|_| vole_rctask_run(body as *const u8, std::ptr::null()))
            .collect();

        assert_eq!(alloc_track::delta(snap), 5);

        scheduler::with_scheduler(|sched| sched.run());

        for task in tasks {
            rc_dec(task as *mut u8);
        }

        assert_eq!(alloc_track::delta(snap), 0);
    }
}

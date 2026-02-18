//! RC-managed task handle for green thread tasks.
//!
//! `RcTask` follows the `RcHeader`-fronted allocation pattern used by `RcArray`,
//! `RcChannel`, and other RC types. It wraps a scheduler `TaskId` and provides
//! a Vole-visible handle for join/cancel operations.

use std::alloc::{Layout, alloc, dealloc};
use std::cell::Cell;

use crate::alloc_track;
use crate::scheduler::{self, TaskId};
use crate::value::{RcHeader, RuntimeTypeId, TaggedValue, rc_dec, rc_inc, tag_needs_rc};

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
    /// Whether the task has completed.
    pub completed: Cell<bool>,
    /// Optional closure pointer (RC-managed). Stored here so we can rc_dec
    /// it when the task handle is dropped, preventing closure leaks.
    pub closure_ptr: Cell<*const u8>,
}

// =============================================================================
// Allocation / Deallocation
// =============================================================================

impl RcTask {
    /// Allocate a new RcTask wrapping a scheduler task.
    pub fn new(task_id: TaskId) -> *mut Self {
        let layout = Layout::new::<RcTask>();
        // SAFETY: Layout::new::<RcTask>() is non-zero-sized; handle_alloc_error
        // is called if alloc returns null.
        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }

        let task = ptr as *mut RcTask;
        // SAFETY: `ptr` was just allocated with the correct layout and is non-null
        // (checked above). Writing header and Cell fields initializes the allocation.
        unsafe {
            std::ptr::write(
                &raw mut (*task).header,
                RcHeader::with_drop_fn(RuntimeTypeId::Task as u32, task_drop),
            );
            (*task).task_id = Cell::new(task_id.as_raw());
            (*task).completed = Cell::new(false);
            (*task).closure_ptr = Cell::new(std::ptr::null());
        }

        alloc_track::track_alloc(RuntimeTypeId::Task as u32);
        task
    }

    /// Set the closure pointer (RC-managed) that this task owns.
    ///
    /// The task will rc_dec this pointer when it is dropped.
    #[expect(clippy::not_unsafe_ptr_arg_deref)]
    pub fn set_closure(task: *mut Self, closure: *const u8) {
        // SAFETY: Caller guarantees `task` points to a valid RcTask allocation.
        // Cell::set is safe to call through a raw pointer dereference.
        unsafe {
            (*task).closure_ptr.set(closure);
        }
    }
}

/// Drop function for `RcTask`.
///
/// Called when the reference count reaches zero. Cancels the underlying
/// scheduler task if it is still running, rc_dec's the closure if present,
/// then frees the allocation.
extern "C" fn task_drop(ptr: *mut u8) {
    let task = ptr as *mut RcTask;

    // Cancel the underlying scheduler task if still running.
    // SAFETY: `task` points to a valid RcTask — called only by rc_dec when
    // refcount reaches zero, so the allocation is still live.
    let task_id = unsafe { (*task).task_id.get() };
    // SAFETY: Same valid RcTask pointer; reading the completed flag.
    if !unsafe { (*task).completed.get() } {
        scheduler::with_scheduler(|sched| {
            let tid = TaskId::from_raw(task_id);
            if !sched.is_done(tid) {
                sched.cancel(tid);
            }
        });
    }

    // RC-dec the closure if the task owns a reference.
    // SAFETY: Same valid RcTask pointer; reading the closure_ptr field.
    let closure = unsafe { (*task).closure_ptr.get() };
    if !closure.is_null() {
        rc_dec(closure as *mut u8);
    }

    // Take and RC-dec the scheduler-owned result value if it's an RC type.
    // This handles completed tasks that were never joined, and releases the
    // scheduler's owning reference after all join calls are done.
    let tid = TaskId::from_raw(task_id);
    scheduler::with_scheduler(|sched| {
        if let Some(tv) = sched.take_task_result(tid)
            && tv.value != 0
            && tag_needs_rc(tv.tag)
        {
            rc_dec(tv.value as *mut u8);
        }
    });

    // Free the allocation.
    let layout = Layout::new::<RcTask>();
    // SAFETY: `ptr` points to the start of the RcTask allocation with the
    // same layout used in `new`. All fields have been read; no further access.
    unsafe { dealloc(ptr, layout) };
    alloc_track::track_dealloc(RuntimeTypeId::Task as u32);
}

// =============================================================================
// FFI functions
// =============================================================================

/// Spawn a new task. Takes a function pointer, closure pointer, and return type tag.
///
/// Returns an `*mut RcTask` as i64 (opaque handle for Vole).
///
/// The closure_ptr should be the Vole closure pointer, and body_fn should
/// be the function pointer extracted from the closure. `return_tag` is the
/// `RuntimeTypeId` of the closure's return type, needed so the scheduler
/// calls the function with the correct ABI (f64 returns live in XMM0).
#[unsafe(no_mangle)]
pub extern "C" fn vole_rctask_run(
    body_fn: *const u8,
    closure_ptr: *const u8,
    return_tag: u64,
) -> *mut RcTask {
    let task_id = scheduler::with_scheduler(|sched| sched.spawn(body_fn, closure_ptr, return_tag));
    RcTask::new(task_id)
}

/// Join: block until the task completes, return its tagged result.
///
/// If called from the main thread (no current task), drives the scheduler
/// inline until the target completes. If called from within a task, blocks
/// the calling task until the target reaches a terminal state.
///
/// If the task already completed, returns immediately.
/// If the task panicked, propagates the panic.
/// If the task was cancelled, panics with "joined task was cancelled".
///
/// Returns a `TaggedValue` with the type tag and value. The FFI wrapper
/// (`task_join_wrapper`) converts this to a `JoinResult` struct for Vole.
#[unsafe(no_mangle)]
#[expect(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn vole_rctask_join(task_ptr: *mut RcTask) -> TaggedValue {
    if task_ptr.is_null() {
        return TaggedValue::from_i64(0);
    }

    // SAFETY: Null check above ensures `task_ptr` is valid. The RcTask
    // allocation is live because the caller holds an RC reference.
    let task_id = unsafe { (*task_ptr).task_id.get() };
    let tid = TaskId::from_raw(task_id);

    let tv = scheduler::with_scheduler(|sched| {
        if sched.current_task().is_some() {
            // Called from within a task: use cooperative join (blocks caller).
            sched.join(tid)
        } else {
            // Called from main thread: drive the scheduler until target is done.
            sched.run_until_done(tid);
            sched.join_result(tid)
        }
    });

    // Scheduler retains ownership of the stored result until task_drop.
    // For RC payloads, each join call returns an additional owned reference.
    if tv.value != 0 && tag_needs_rc(tv.tag) {
        rc_inc(tv.value as *mut u8);
    }

    // Mark the handle as completed.
    // SAFETY: `task_ptr` is non-null (checked above) and points to a live
    // RcTask. Setting the completed flag via Cell is a single-threaded update.
    unsafe {
        (*task_ptr).completed.set(true);
    }

    tv
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

    // SAFETY: Null check above ensures `task_ptr` is valid and live.
    let task_id = unsafe { (*task_ptr).task_id.get() };
    let tid = TaskId::from_raw(task_id);

    scheduler::with_scheduler(|sched| {
        sched.cancel(tid);
    });

    // SAFETY: `task_ptr` is non-null (checked above) and points to a live RcTask.
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
    // SAFETY: Null check above ensures `task_ptr` is valid and live.
    if unsafe { (*task_ptr).completed.get() } {
        return 1;
    }

    // Check with the scheduler.
    // SAFETY: `task_ptr` is non-null (checked above) and points to a live RcTask.
    let task_id = unsafe { (*task_ptr).task_id.get() };
    let done = scheduler::with_scheduler(|sched| sched.is_done(TaskId::from_raw(task_id)));

    if done {
        // SAFETY: `task_ptr` is non-null and live; updating the cached completed flag.
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
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks from previous tests on this thread.
        scheduler::with_scheduler(|sched| sched.run());

        let before = alloc_track::count(RuntimeTypeId::Task as u32);

        let tid = scheduler::with_scheduler(|sched| {
            extern "C" fn body(_c: *const u8, _y: *const u8) {}
            sched.spawn(
                body as *const u8,
                std::ptr::null(),
                RuntimeTypeId::I64 as u64,
            )
        });

        let task = RcTask::new(tid);
        assert!(!task.is_null());

        // Run scheduler to complete the task.
        scheduler::with_scheduler(|sched| sched.run());

        // Drop via rc_dec.
        rc_dec(task as *mut u8);
        assert_eq!(alloc_track::count(RuntimeTypeId::Task as u32) - before, 0);
    }

    #[test]
    fn rctask_type_id() {
        assert_eq!(RuntimeTypeId::Task as u32, 10);
        assert_eq!(RuntimeTypeId::from_u32(10), Some(RuntimeTypeId::Task));
        assert_eq!(RuntimeTypeId::Task.name(), "Task");
    }

    #[test]
    fn vole_rctask_run_returns_handle() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        static FLAG: AtomicI64 = AtomicI64::new(0);
        FLAG.store(0, Ordering::SeqCst);

        extern "C" fn body(_c: *const u8, _y: *const u8) {
            FLAG.store(42, Ordering::SeqCst);
        }

        let task = vole_rctask_run(
            body as *const u8,
            std::ptr::null(),
            RuntimeTypeId::I64 as u64,
        );
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
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn body(_c: *const u8, _y: *const u8) {
            RAN.store(1, Ordering::SeqCst);
        }

        let task = vole_rctask_run(
            body as *const u8,
            std::ptr::null(),
            RuntimeTypeId::I64 as u64,
        );
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
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        extern "C" fn body(_c: *const u8, _y: *const u8) {}

        let task = vole_rctask_run(
            body as *const u8,
            std::ptr::null(),
            RuntimeTypeId::I64 as u64,
        );

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
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        alloc_track::enable_tracking();

        // Drain any leftover scheduler tasks.
        scheduler::with_scheduler(|sched| sched.run());

        let before = alloc_track::count(RuntimeTypeId::Task as u32);

        extern "C" fn body(_c: *const u8, _y: *const u8) {}

        let tasks: Vec<*mut RcTask> = (0..5)
            .map(|_| {
                vole_rctask_run(
                    body as *const u8,
                    std::ptr::null(),
                    RuntimeTypeId::I64 as u64,
                )
            })
            .collect();

        assert_eq!(alloc_track::count(RuntimeTypeId::Task as u32) - before, 5);

        scheduler::with_scheduler(|sched| sched.run());

        for task in tasks {
            rc_dec(task as *mut u8);
        }

        assert_eq!(alloc_track::count(RuntimeTypeId::Task as u32) - before, 0);
    }
}

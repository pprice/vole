//! M:1 cooperative task scheduler for Vole green threads.
//!
//! All tasks run on a single OS thread, interleaving at explicit yield points
//! (Task.yield(), channel ops, join). Uses `VoleCoroutine` for stack switching.

use std::cell::{Cell, UnsafeCell};
use std::collections::{BinaryHeap, VecDeque};
use std::time::Instant;

use rustc_hash::FxHashMap;

use crate::coroutine::VoleCoroutine;

// Thread-local transfer slot for task return values. The coroutine body
// stores the return value here before exiting, and step_task reads it
// after the coroutine completes. This avoids re-entering with_scheduler
// from within a coroutine (which would cause a RefCell double-borrow).
thread_local! {
    static TASK_RESULT: Cell<i64> = const { Cell::new(0) };
}

// Thread-local pointer to the current task's yielder. Set by `step_task`
// before resuming a coroutine, cleared after. Channel operations use this
// to yield the current coroutine when they need to block (e.g., send on
// a full buffer, recv on an empty buffer).
thread_local! {
    static CURRENT_YIELDER: Cell<*const u8> = const { Cell::new(std::ptr::null()) };
}

/// Yield the current task's coroutine back to the scheduler.
///
/// Called by channel operations when they need to block. The caller must
/// have set the task state to `Blocked` via `block_current` before calling
/// this. After the task is unblocked and resumed, this function returns.
///
/// Returns `false` if there is no current yielder (main-thread context).
pub fn yield_current_coroutine() -> bool {
    let yielder_ptr = CURRENT_YIELDER.with(|cell| cell.get());
    if yielder_ptr.is_null() {
        return false;
    }
    // SAFETY: The yielder pointer is valid for the duration of the coroutine's
    // execution. We are inside that coroutine. The suspend call switches back
    // to step_task which will handle re-queueing or blocking.
    unsafe {
        let yielder = &*(yielder_ptr as *const corosensei::Yielder<i64, i64>);
        yielder.suspend(1); // Signal 1 = blocked yield (vs 0 = voluntary)
    }
    true
}

// =============================================================================
// Types
// =============================================================================

/// Unique task identifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TaskId(u64);

impl TaskId {
    /// Create a `TaskId` from a raw `u64` (used by channel operations).
    pub fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    /// Get the raw `u64` value (used by channel operations).
    pub fn as_raw(self) -> u64 {
        self.0
    }
}

/// Task lifecycle state.
///
/// See vol-u8zh Phase 1 Semantics Contract, Section 1.1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaskState {
    /// In the run queue, waiting to be scheduled.
    Pending,
    /// Currently executing on the OS thread (exactly one at a time in M:1).
    Running,
    /// Suspended, waiting for join/channel/timer.
    Blocked,
    /// Finished execution normally; result available.
    Completed,
    /// Cancellation was processed; will not execute further.
    Cancelled,
}

/// Why a task is blocked (for deadlock diagnostics).
#[derive(Clone, Copy, Debug)]
pub enum BlockReason {
    /// Blocked on `task.join(target)`.
    Join(TaskId),
    /// Blocked on a channel receive.
    ChannelRecv,
    /// Blocked on a channel send.
    ChannelSend,
    /// Blocked on `Task.select()`.
    Select,
}

/// Source that woke a task from a `select` wait.
///
/// Set by the channel (or timer) that unblocks the task, read by the
/// select implementation after the coroutine resumes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WakeupSource {
    /// Woken by channel at the given 0-based index in the select argument list.
    Channel(usize),
    /// Woken by timeout expiry.
    Timeout,
}

/// A single green thread.
pub struct Task {
    pub id: TaskId,
    pub state: TaskState,
    /// The coroutine providing the execution stack.
    /// Boxed to prevent HashMap resizing from moving the coroutine struct
    /// while it's being resumed (corosensei writes back to &mut self on yield).
    pub coroutine: Box<VoleCoroutine>,
    /// Result value (set when task completes). Stored as i64 (tagged pointer or value).
    pub result: Option<i64>,
    /// Tasks waiting for this task to complete (for join).
    pub join_waiters: Vec<TaskId>,
    /// Why this task is blocked (for deadlock diagnostics).
    pub block_reason: Option<BlockReason>,
    /// Whether this task panicked during execution.
    pub panicked: bool,
    /// Panic message, if the task panicked.
    pub panic_message: Option<String>,
    /// Cached yielder pointer for this task's coroutine. Set on first resume,
    /// restored by step_task on subsequent resumes so channel operations can yield.
    pub yielder_ptr: *const u8,
    /// Set by the wakeup source (channel send or timer) before unblocking
    /// a select-waiting task. Read by the `task_select` FFI after resume.
    pub wakeup_source: Option<WakeupSource>,
    /// Per-task transfer slot for channel receive. Set by a sender when
    /// handing a value directly to a blocked receiver, consumed by the
    /// receiver after being unblocked. Using a per-task slot (instead of
    /// a global thread-local) prevents value corruption when multiple
    /// sender-receiver handoffs interleave.
    pub transfer_value: Option<crate::value::TaggedValue>,
}

// =============================================================================
// Scheduler
// =============================================================================

/// Timer entry for select timeouts.
///
/// Stored in a min-heap (earliest deadline first).
struct TimerEntry {
    deadline: Instant,
    task_id: TaskId,
}

impl PartialEq for TimerEntry {
    fn eq(&self, other: &Self) -> bool {
        self.deadline == other.deadline
    }
}

impl Eq for TimerEntry {}

impl PartialOrd for TimerEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TimerEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reverse ordering: BinaryHeap is a max-heap, we want min-heap.
        other.deadline.cmp(&self.deadline)
    }
}

/// M:1 cooperative scheduler. All tasks share a single OS thread.
pub struct Scheduler {
    /// Monotonically increasing task ID counter.
    next_id: u64,
    /// Currently running task, if any.
    current: Option<TaskId>,
    /// FIFO queue of ready tasks.
    run_queue: VecDeque<TaskId>,
    /// All live tasks, indexed by TaskId.
    tasks: FxHashMap<TaskId, Task>,
    /// Timer queue for select timeouts (min-heap by deadline).
    timer_queue: BinaryHeap<TimerEntry>,
}

impl Default for Scheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            next_id: 1,
            current: None,
            run_queue: VecDeque::new(),
            tasks: FxHashMap::default(),
            timer_queue: BinaryHeap::new(),
        }
    }

    /// Spawn a new task. Returns its TaskId.
    #[expect(clippy::not_unsafe_ptr_arg_deref)]
    pub fn spawn(&mut self, body_fn: *const u8, closure_ptr: *const u8) -> TaskId {
        let id = TaskId(self.next_id);
        self.next_id += 1;

        // Safety: body_fn and closure_ptr come from JIT-generated code.
        // Use C-unwind ABI because the body may call vole_generator_yield
        // or other functions that perform stack switches via corosensei.
        // The Vole function returns i64 in RAX -- we capture it and store
        // it as the task's result via set_current_result.
        let func: extern "C-unwind" fn(*const u8, *const u8) -> i64 =
            unsafe { std::mem::transmute(body_fn) };
        let closure = closure_ptr as usize;

        let coro = VoleCoroutine::new(move |yielder, _input| {
            let yielder_ptr = yielder as *const corosensei::Yielder<i64, i64> as *const u8;
            // Set the yielder so channel operations can yield this coroutine.
            CURRENT_YIELDER.with(|cell| cell.set(yielder_ptr));
            let result = func(closure as *const u8, yielder_ptr);
            // Clear the yielder before exiting.
            CURRENT_YIELDER.with(|cell| cell.set(std::ptr::null()));
            // Store the task's return value in the thread-local transfer slot.
            // step_task reads it after the coroutine completes.
            TASK_RESULT.with(|cell| cell.set(result));
        });

        let task = Task {
            id,
            state: TaskState::Pending,
            coroutine: Box::new(coro),
            result: None,
            join_waiters: Vec::new(),
            block_reason: None,
            panicked: false,
            panic_message: None,
            yielder_ptr: std::ptr::null(),
            wakeup_source: None,
            transfer_value: None,
        };

        self.tasks.insert(id, task);
        self.run_queue.push_back(id);

        id
    }

    /// Yield the current task: move it to the back of the run queue, resume next.
    pub fn yield_current(&mut self) {
        if let Some(task_id) = self.current
            && let Some(task) = self.tasks.get_mut(&task_id)
            && task.state == TaskState::Running
        {
            task.state = TaskState::Pending;
            self.run_queue.push_back(task_id);
        }
    }

    /// Block the current task. It will be unblocked by another operation.
    pub fn block_current(&mut self, reason: BlockReason) -> Option<TaskId> {
        let task_id = self.current?;
        if let Some(task) = self.tasks.get_mut(&task_id) {
            task.state = TaskState::Blocked;
            task.block_reason = Some(reason);
        }
        Some(task_id)
    }

    /// Unblock a previously blocked task (move it to the run queue).
    pub fn unblock(&mut self, task_id: TaskId) {
        if let Some(task) = self.tasks.get_mut(&task_id)
            && task.state == TaskState::Blocked
        {
            task.state = TaskState::Pending;
            task.block_reason = None;
            self.run_queue.push_back(task_id);
        }
    }

    /// Join: block the current task until `target` completes or is cancelled.
    ///
    /// Returns the target's result value, or panics if the target was
    /// cancelled or panicked (see Semantics Contract Section 1.3).
    pub fn join(&mut self, target: TaskId) -> i64 {
        // Self-join detection (Section 4.3).
        if self.current == Some(target) {
            panic!("deadlock: task attempted to join itself");
        }

        // Check if target is already in a terminal state.
        if let Some(task) = self.tasks.get(&target) {
            match task.state {
                TaskState::Completed => {
                    if task.panicked {
                        let msg = task.panic_message.as_deref().unwrap_or("unknown");
                        panic!("joined task panicked: {msg}");
                    }
                    return task.result.unwrap_or(0);
                }
                TaskState::Cancelled => {
                    panic!("joined task was cancelled");
                }
                _ => {}
            }
        }

        // Target still running: register as a waiter and block.
        let current_id = self.current.expect("join called with no current task");
        if let Some(target_task) = self.tasks.get_mut(&target) {
            target_task.join_waiters.push(current_id);
        }
        self.block_current(BlockReason::Join(target));
        // Yield the coroutine back to the scheduler. When the target
        // completes or is cancelled, this task is unblocked and resumes.
        yield_current_coroutine();

        // After being woken: target is now in a terminal state.
        if let Some(task) = self.tasks.get(&target) {
            if task.panicked {
                let msg = task.panic_message.as_deref().unwrap_or("unknown");
                panic!("joined task panicked: {msg}");
            }
            if task.state == TaskState::Cancelled {
                panic!("joined task was cancelled");
            }
            task.result.unwrap_or(0)
        } else {
            0
        }
    }

    /// Cancel a task (Semantics Contract Section 1.2).
    pub fn cancel(&mut self, task_id: TaskId) {
        if let Some(task) = self.tasks.get_mut(&task_id) {
            match task.state {
                TaskState::Completed | TaskState::Cancelled => {
                    // No-op for terminal states.
                }
                TaskState::Blocked => {
                    // Immediately cancel blocked tasks.
                    task.state = TaskState::Cancelled;
                    task.block_reason = None;
                    // Wake join waiters so they see cancellation.
                    let waiters: Vec<TaskId> = task.join_waiters.drain(..).collect();
                    for waiter_id in waiters {
                        self.unblock(waiter_id);
                    }
                }
                TaskState::Pending => {
                    // Remove from run queue and cancel.
                    self.run_queue.retain(|id| *id != task_id);
                    task.state = TaskState::Cancelled;
                    let waiters: Vec<TaskId> = task.join_waiters.drain(..).collect();
                    for waiter_id in waiters {
                        self.unblock(waiter_id);
                    }
                }
                TaskState::Running => {
                    // Cooperative cancellation: set state, checked at next yield.
                    task.state = TaskState::Cancelled;
                    let waiters: Vec<TaskId> = task.join_waiters.drain(..).collect();
                    for waiter_id in waiters {
                        self.unblock(waiter_id);
                    }
                }
            }
        }
    }

    /// Run the scheduler loop until all tasks complete or deadlock.
    pub fn run(&mut self) {
        loop {
            self.fire_expired_timers();

            let task_id = match self.run_queue.pop_front() {
                Some(id) => id,
                None => {
                    // No ready tasks.
                    if self.has_blocked_tasks() && !self.has_pending_timers() {
                        self.panic_deadlock();
                    }
                    if self.has_pending_timers() {
                        // Timers pending but no ready tasks: busy-wait for timers.
                        std::thread::yield_now();
                        continue;
                    }
                    return; // All tasks done.
                }
            };

            self.step_task(task_id);
        }
    }

    /// Run the scheduler loop until a specific task reaches a terminal state.
    ///
    /// Used for main-thread join: the main thread is not a scheduler task,
    /// so it drives the scheduler loop directly until the target completes.
    pub fn run_until_done(&mut self, target: TaskId) {
        loop {
            // Check if target is done.
            if self.is_done(target) {
                return;
            }

            self.fire_expired_timers();

            let task_id = match self.run_queue.pop_front() {
                Some(id) => id,
                None => {
                    if self.has_blocked_tasks() && !self.has_pending_timers() {
                        self.panic_deadlock();
                    }
                    if self.has_pending_timers() {
                        std::thread::yield_now();
                        continue;
                    }
                    return; // All tasks done (target must be done too).
                }
            };

            self.step_task(task_id);
        }
    }

    /// Execute one step for a single task: resume its coroutine, handle
    /// yield/completion, update scheduler state.
    fn step_task(&mut self, task_id: TaskId) {
        // Cancellation check before resume (Section 1.2, point 1).
        if let Some(task) = self.tasks.get(&task_id)
            && task.state == TaskState::Cancelled
        {
            return;
        }

        // Resume the task's coroutine.
        self.current = Some(task_id);
        if let Some(task) = self.tasks.get_mut(&task_id) {
            task.state = TaskState::Running;
        }

        // Save the previous CURRENT_YIELDER and restore this task's yielder.
        // This ensures that when tasks interleave, each task's channel
        // operations use the correct yielder for suspension.
        let prev_yielder = CURRENT_YIELDER.with(|cell| cell.get());
        let task_yielder = self
            .tasks
            .get(&task_id)
            .map_or(std::ptr::null(), |t| t.yielder_ptr);
        CURRENT_YIELDER.with(|cell| cell.set(task_yielder));

        let resume_result = {
            let task = self.tasks.get_mut(&task_id).expect("task not found");
            task.coroutine.resume(0)
        };

        // After resume: the coroutine may have set CURRENT_YIELDER (on first
        // resume). Capture it back to the task for next time.
        let updated_yielder = CURRENT_YIELDER.with(|cell| cell.get());
        if let Some(task) = self.tasks.get_mut(&task_id) {
            task.yielder_ptr = updated_yielder;
        }
        // Restore the previous yielder.
        CURRENT_YIELDER.with(|cell| cell.set(prev_yielder));

        match resume_result {
            Some(_signal) => {
                // Task yielded. Check cancellation (Section 1.2, point 2).
                if let Some(task) = self.tasks.get_mut(&task_id) {
                    if task.state == TaskState::Cancelled {
                        // Already cancelled during execution.
                    } else if task.state == TaskState::Running {
                        // Voluntary yield: re-queue.
                        task.state = TaskState::Pending;
                        self.run_queue.push_back(task_id);
                    }
                    // If Blocked, it was set by block_current during resume.
                }
            }
            None => {
                // Task completed. Read the return value from the transfer slot.
                let result = TASK_RESULT.with(|cell| cell.get());
                if let Some(task) = self.tasks.get_mut(&task_id) {
                    task.state = TaskState::Completed;
                    task.result = Some(result);
                    // Wake join waiters.
                    let waiters: Vec<TaskId> = task.join_waiters.drain(..).collect();
                    for waiter_id in waiters {
                        self.unblock(waiter_id);
                    }
                }
            }
        }

        self.current = None;
    }

    /// Returns the currently running task's ID.
    pub fn current_task(&self) -> Option<TaskId> {
        self.current
    }

    /// Check if a task is done (completed or cancelled).
    pub fn is_done(&self, task_id: TaskId) -> bool {
        self.tasks
            .get(&task_id)
            .is_some_and(|t| matches!(t.state, TaskState::Completed | TaskState::Cancelled))
    }

    /// Get the result of a completed task.
    pub fn task_result(&self, task_id: TaskId) -> Option<i64> {
        self.tasks.get(&task_id).and_then(|t| t.result)
    }

    /// Get the result of a completed/cancelled task with join semantics.
    ///
    /// Panics if the task was cancelled or panicked (matching `join()` behavior).
    /// Returns the result value for normally completed tasks.
    pub fn join_result(&self, task_id: TaskId) -> i64 {
        if let Some(task) = self.tasks.get(&task_id) {
            if task.panicked {
                let msg = task.panic_message.as_deref().unwrap_or("unknown");
                panic!("joined task panicked: {msg}");
            }
            if task.state == TaskState::Cancelled {
                panic!("joined task was cancelled");
            }
            task.result.unwrap_or(0)
        } else {
            0
        }
    }

    /// Execute one scheduler step from the main thread: pop the next ready
    /// task and resume it. Returns `true` if a task was stepped, `false` if
    /// the run queue was empty.
    ///
    /// Used by main-thread channel recv to pump the scheduler inline.
    /// Panics on deadlock (blocked tasks with empty run queue).
    pub fn pump_one(&mut self) -> bool {
        self.fire_expired_timers();

        let task_id = match self.run_queue.pop_front() {
            Some(id) => id,
            None => {
                if self.has_blocked_tasks() && !self.has_pending_timers() {
                    self.panic_deadlock();
                }
                return false;
            }
        };
        self.step_task(task_id);
        true
    }

    /// Register a timer that will fire at the given deadline.
    ///
    /// When the timer fires (deadline reached), the task is woken with
    /// `WakeupSource::Timeout`.
    pub fn register_timer(&mut self, task_id: TaskId, deadline: Instant) {
        self.timer_queue.push(TimerEntry { deadline, task_id });
    }

    /// Fire all expired timers: unblock tasks whose deadlines have passed.
    ///
    /// Called at the start of each scheduler step (run/pump_one) to ensure
    /// timers are checked even when tasks are yielding.
    pub fn fire_expired_timers(&mut self) {
        let now = Instant::now();
        while let Some(entry) = self.timer_queue.peek() {
            if entry.deadline > now {
                break;
            }
            let entry = self.timer_queue.pop().unwrap();
            if let Some(task) = self.tasks.get_mut(&entry.task_id)
                && task.state == TaskState::Blocked
            {
                // Only set timeout wakeup if no channel has already woken it.
                if task.wakeup_source.is_none() {
                    task.wakeup_source = Some(WakeupSource::Timeout);
                }
                task.state = TaskState::Pending;
                task.block_reason = None;
                self.run_queue.push_back(entry.task_id);
            }
        }
    }

    /// Set the wakeup source for a task (used by channel select-wake).
    pub fn set_wakeup_source(&mut self, task_id: TaskId, source: WakeupSource) {
        if let Some(task) = self.tasks.get_mut(&task_id) {
            // First wake wins: don't overwrite an existing source.
            if task.wakeup_source.is_none() {
                task.wakeup_source = Some(source);
            }
        }
    }

    /// Read and clear the wakeup source for a task.
    pub fn take_wakeup_source(&mut self, task_id: TaskId) -> Option<WakeupSource> {
        self.tasks
            .get_mut(&task_id)
            .and_then(|t| t.wakeup_source.take())
    }

    /// Store a transfer value on a specific task (used by channel send
    /// when handing a value directly to a blocked receiver).
    pub fn set_transfer_value(&mut self, task_id: TaskId, tv: crate::value::TaggedValue) {
        if let Some(task) = self.tasks.get_mut(&task_id) {
            task.transfer_value = Some(tv);
        }
    }

    /// Take the transfer value from the current task (used by channel
    /// recv after being unblocked by a sender).
    pub fn take_current_transfer_value(&mut self) -> Option<crate::value::TaggedValue> {
        let task_id = self.current?;
        self.tasks
            .get_mut(&task_id)
            .and_then(|t| t.transfer_value.take())
    }

    /// Check whether there are any pending timers.
    pub fn has_pending_timers(&self) -> bool {
        !self.timer_queue.is_empty()
    }

    // ─── Private helpers ────────────────────────────────────────────

    fn has_blocked_tasks(&self) -> bool {
        self.tasks.values().any(|t| t.state == TaskState::Blocked)
    }

    /// Panic with deadlock diagnostic (Section 4.3).
    fn panic_deadlock(&self) -> ! {
        let blocked: Vec<_> = self
            .tasks
            .values()
            .filter(|t| t.state == TaskState::Blocked)
            .collect();

        let ready_count = self.run_queue.len();
        let mut msg = format!(
            "runtime error: deadlock detected\n  {} tasks blocked, {} tasks ready",
            blocked.len(),
            ready_count
        );

        for task in &blocked {
            let reason = match task.block_reason {
                Some(BlockReason::Join(target)) => format!("blocked on join(task #{})", target.0),
                Some(BlockReason::ChannelRecv) => "blocked on recv(channel)".to_string(),
                Some(BlockReason::ChannelSend) => "blocked on send(channel)".to_string(),
                Some(BlockReason::Select) => "blocked on select".to_string(),
                None => "blocked (unknown reason)".to_string(),
            };
            msg.push_str(&format!("\n  task #{}: {}", task.id.0, reason));
        }

        panic!("{msg}");
    }
}

// =============================================================================
// Thread-local singleton
// =============================================================================

thread_local! {
    static SCHEDULER: UnsafeCell<Option<Scheduler>> = const { UnsafeCell::new(None) };
}

/// Run a function with the thread-local scheduler, lazily initializing it.
///
/// # Safety
///
/// Uses `UnsafeCell` instead of `RefCell` to allow re-entrant access. This is
/// required because the M:1 scheduler resumes coroutines (via `step_task`),
/// and inside those coroutines, channel/task operations call `with_scheduler`
/// again. With `RefCell`, this would panic with "already borrowed".
///
/// Re-entrant mutable access is safe here because:
/// 1. The scheduler is thread-local (no cross-thread aliasing).
/// 2. Coroutine resume is a stack switch: the outer `with_scheduler` call is
///    suspended on the outer stack while the coroutine runs, so no two frames
///    access the scheduler simultaneously.
/// 3. When the coroutine yields/completes, we return to the outer frame.
pub fn with_scheduler<R>(f: impl FnOnce(&mut Scheduler) -> R) -> R {
    SCHEDULER.with(|cell| {
        // SAFETY: See function doc. Single-threaded, coroutine-switched access.
        let opt = unsafe { &mut *cell.get() };
        let sched = opt.get_or_insert_with(Scheduler::new);
        f(sched)
    })
}

// =============================================================================
// FFI functions
// =============================================================================

/// Spawn a new task. Returns a task handle (TaskId as i64).
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_spawn(body_fn: *const u8, closure_ptr: *const u8) -> i64 {
    with_scheduler(|sched| {
        let task_id = sched.spawn(body_fn, closure_ptr);
        task_id.0 as i64
    })
}

/// Yield the current task to the scheduler.
///
/// Uses `C-unwind` because `suspend()` performs a stack switch via corosensei.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn vole_task_yield() {
    // The actual yield happens by suspending the current coroutine.
    // The scheduler's run loop will handle re-queueing.
    // We need to call suspend on the yielder, but the yielder is only
    // accessible from within the coroutine body. Task.yield() is called
    // from within the task body, which has access to the yielder.
    //
    // For now, we use vole_generator_yield with signal 0 (voluntary yield).
    // The task body receives the yielder pointer and can call this.
    //
    // However, we need a different mechanism here: the task needs to
    // yield back to the scheduler. This is handled by the coroutine
    // infrastructure -- the task body calls yielder.suspend(0) to yield.
    //
    // This FFI function is provided for convenience but the actual
    // mechanism is that codegen emits a call to vole_generator_yield
    // with the yielder pointer.
}

/// Block the current task. Used internally by channel operations.
///
/// Returns the current TaskId as i64, or -1 if no current task.
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_block() -> i64 {
    with_scheduler(|sched| {
        sched
            .block_current(BlockReason::ChannelRecv)
            .map_or(-1, |id| id.0 as i64)
    })
}

/// Unblock a task by ID. Used internally by channel operations.
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_unblock(task_id: i64) {
    with_scheduler(|sched| {
        sched.unblock(TaskId(task_id as u64));
    })
}

/// Join: block until a task completes, return its result.
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_join(task_id: i64) -> i64 {
    with_scheduler(|sched| sched.join(TaskId(task_id as u64)))
}

/// Cancel a task.
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_cancel(task_id: i64) {
    with_scheduler(|sched| {
        sched.cancel(TaskId(task_id as u64));
    })
}

/// Check if a task is done (completed or cancelled).
#[unsafe(no_mangle)]
pub extern "C" fn vole_task_is_done(task_id: i64) -> i64 {
    with_scheduler(|sched| {
        if sched.is_done(TaskId(task_id as u64)) {
            1
        } else {
            0
        }
    })
}

/// Run the scheduler loop until all tasks complete.
///
/// Called at program exit to drain remaining tasks.
#[unsafe(no_mangle)]
pub extern "C" fn vole_scheduler_run() {
    with_scheduler(|sched| sched.run())
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicI64, Ordering};

    #[test]
    fn single_task_runs_to_completion() {
        let mut sched = Scheduler::new();

        static FLAG: AtomicI64 = AtomicI64::new(0);
        FLAG.store(0, Ordering::SeqCst);

        extern "C" fn body(_closure: *const u8, _yielder: *const u8) {
            FLAG.store(42, Ordering::SeqCst);
        }

        sched.spawn(body as *const u8, std::ptr::null());
        sched.run();

        assert_eq!(FLAG.load(Ordering::SeqCst), 42);
    }

    #[test]
    fn two_tasks_interleave() {
        let mut sched = Scheduler::new();

        static ORDER: AtomicI64 = AtomicI64::new(0);
        ORDER.store(0, Ordering::SeqCst);

        // Task A: sets ORDER to 1, yields, then checks ORDER == 2.
        extern "C-unwind" fn body_a(_closure: *const u8, yielder: *const u8) {
            ORDER.store(1, Ordering::SeqCst);
            // Yield back to scheduler.
            unsafe {
                let y = &*(yielder as *const corosensei::Yielder<i64, i64>);
                y.suspend(0);
            }
            // After resume, task B should have run.
            assert_eq!(ORDER.load(Ordering::SeqCst), 2);
            ORDER.store(3, Ordering::SeqCst);
        }

        // Task B: checks ORDER == 1, sets it to 2.
        extern "C" fn body_b(_closure: *const u8, _yielder: *const u8) {
            assert_eq!(ORDER.load(Ordering::SeqCst), 1);
            ORDER.store(2, Ordering::SeqCst);
        }

        sched.spawn(body_a as *const u8, std::ptr::null());
        sched.spawn(body_b as *const u8, std::ptr::null());
        sched.run();

        assert_eq!(ORDER.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn cancel_before_run() {
        let mut sched = Scheduler::new();

        static RAN: AtomicI64 = AtomicI64::new(0);
        RAN.store(0, Ordering::SeqCst);

        extern "C" fn body(_closure: *const u8, _yielder: *const u8) {
            RAN.store(1, Ordering::SeqCst);
        }

        let task_id = sched.spawn(body as *const u8, std::ptr::null());
        sched.cancel(task_id);
        sched.run();

        // Task should never have executed.
        assert_eq!(RAN.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn cancel_pending_wakes_joiners() {
        let mut sched = Scheduler::new();

        // Spawn a task, then cancel it. Any would-be joiners should
        // see Cancelled state.
        extern "C" fn body(_closure: *const u8, _yielder: *const u8) {}
        let task_id = sched.spawn(body as *const u8, std::ptr::null());
        sched.cancel(task_id);

        assert!(sched.is_done(task_id));
        let task = sched.tasks.get(&task_id).unwrap();
        assert_eq!(task.state, TaskState::Cancelled);
    }

    #[test]
    fn many_tasks_all_complete() {
        let mut sched = Scheduler::new();

        static COUNT: AtomicI64 = AtomicI64::new(0);
        COUNT.store(0, Ordering::SeqCst);

        extern "C-unwind" fn body(_closure: *const u8, yielder: *const u8) {
            COUNT.fetch_add(1, Ordering::SeqCst);
            // Yield once to test round-robin.
            unsafe {
                let y = &*(yielder as *const corosensei::Yielder<i64, i64>);
                y.suspend(0);
            }
            COUNT.fetch_add(1, Ordering::SeqCst);
        }

        for _ in 0..50 {
            sched.spawn(body as *const u8, std::ptr::null());
        }
        sched.run();

        // Each task increments twice.
        assert_eq!(COUNT.load(Ordering::SeqCst), 100);
    }

    #[test]
    #[should_panic(expected = "deadlock: task attempted to join itself")]
    fn self_join_panics() {
        let mut sched = Scheduler::new();
        sched.current = Some(TaskId(5));
        sched.join(TaskId(5));
    }

    #[test]
    fn deadlock_detection() {
        let mut sched = Scheduler::new();

        // Manually create two blocked tasks with no way to unblock.
        extern "C" fn body(_closure: *const u8, _yielder: *const u8) {}
        let id1 = sched.spawn(body as *const u8, std::ptr::null());
        let id2 = sched.spawn(body as *const u8, std::ptr::null());

        // Remove from run queue and set to blocked.
        sched.run_queue.clear();
        sched.tasks.get_mut(&id1).unwrap().state = TaskState::Blocked;
        sched.tasks.get_mut(&id1).unwrap().block_reason = Some(BlockReason::Join(id2));
        sched.tasks.get_mut(&id2).unwrap().state = TaskState::Blocked;
        sched.tasks.get_mut(&id2).unwrap().block_reason = Some(BlockReason::Join(id1));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            sched.run();
        }));

        assert!(result.is_err());
        let panic_msg = result
            .unwrap_err()
            .downcast::<String>()
            .map(|s| *s)
            .unwrap_or_default();
        assert!(
            panic_msg.contains("deadlock"),
            "expected deadlock message, got: {panic_msg}"
        );
    }

    #[test]
    fn completed_task_result() {
        let mut sched = Scheduler::new();

        extern "C" fn body(_closure: *const u8, _yielder: *const u8) {
            // Task completes without setting a result.
        }

        let id = sched.spawn(body as *const u8, std::ptr::null());
        sched.run();

        assert!(sched.is_done(id));
        assert_eq!(sched.tasks.get(&id).unwrap().state, TaskState::Completed);
    }

    #[test]
    fn scheduler_new_is_empty() {
        let sched = Scheduler::new();
        assert!(sched.run_queue.is_empty());
        assert!(sched.tasks.is_empty());
        assert!(sched.current.is_none());
    }
}

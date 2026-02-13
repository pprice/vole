// src/runtime/signal.rs
//
// Signal handling for segfault debugging and stack overflow recovery.
// Registers a SIGSEGV handler that:
// 1. Detects stack overflow (infinite recursion) and recovers gracefully
// 2. Dumps context info for other segfaults before dying
//
// Stack overflow recovery uses sigaltstack so the handler can run even
// when the main stack is exhausted. When in test context (jmp_buf is set),
// we longjmp back to the test harness. Otherwise, we print a clean error
// and exit.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Maximum context entries (stack depth)
const MAX_CONTEXT_DEPTH: usize = 8;
/// Maximum length of each context entry
const MAX_CONTEXT_LEN: usize = 256;

/// Context stack - each entry describes what we're doing
/// e.g., ["running foo.vole", "executing function main", "calling method bar"]
#[expect(clippy::declare_interior_mutable_const)]
static CONTEXT_STACK: [[std::sync::atomic::AtomicU8; MAX_CONTEXT_LEN]; MAX_CONTEXT_DEPTH] = {
    const INIT_BYTE: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);
    const INIT_ENTRY: [std::sync::atomic::AtomicU8; MAX_CONTEXT_LEN] = [INIT_BYTE; MAX_CONTEXT_LEN];
    [INIT_ENTRY; MAX_CONTEXT_DEPTH]
};
#[expect(clippy::declare_interior_mutable_const)]
static CONTEXT_LENS: [AtomicUsize; MAX_CONTEXT_DEPTH] = {
    const INIT: AtomicUsize = AtomicUsize::new(0);
    [INIT; MAX_CONTEXT_DEPTH]
};
static CONTEXT_DEPTH: AtomicUsize = AtomicUsize::new(0);

/// Whether signal handler has been installed
static HANDLER_INSTALLED: AtomicBool = AtomicBool::new(false);

/// Push a context entry onto the stack
/// Use this to describe what operation is starting
/// Example: push_context("compiling foo.vole")
pub fn push_context(ctx: &str) {
    let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
    if depth >= MAX_CONTEXT_DEPTH {
        return; // Stack full, ignore
    }

    let bytes = ctx.as_bytes();
    let len = bytes.len().min(MAX_CONTEXT_LEN - 1);

    for (i, &b) in bytes[..len].iter().enumerate() {
        CONTEXT_STACK[depth][i].store(b, Ordering::Release);
    }
    CONTEXT_STACK[depth][len].store(0, Ordering::Release);
    CONTEXT_LENS[depth].store(len, Ordering::Release);
    CONTEXT_DEPTH.store(depth + 1, Ordering::Release);
}

/// Pop the most recent context entry
/// Call this when an operation completes
pub fn pop_context() {
    let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
    if depth > 0 {
        CONTEXT_DEPTH.store(depth - 1, Ordering::Release);
    }
}

/// Replace the top context entry (more efficient than pop+push)
/// Use this when updating status within the same operation level
pub fn replace_context(ctx: &str) {
    let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
    if depth == 0 {
        push_context(ctx);
        return;
    }

    let idx = depth - 1;
    let bytes = ctx.as_bytes();
    let len = bytes.len().min(MAX_CONTEXT_LEN - 1);

    for (i, &b) in bytes[..len].iter().enumerate() {
        CONTEXT_STACK[idx][i].store(b, Ordering::Release);
    }
    CONTEXT_STACK[idx][len].store(0, Ordering::Release);
    CONTEXT_LENS[idx].store(len, Ordering::Release);
}

/// Clear all context (call at start of new operation)
pub fn clear_context() {
    CONTEXT_DEPTH.store(0, Ordering::Release);
}

// Legacy API for backward compatibility with test runner
pub fn set_current_file(file: &str) {
    clear_context();
    push_context(file);
}

pub fn set_current_test(name: &str) {
    // Replace second level if exists, otherwise push
    let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
    if depth >= 2 {
        // Replace the test name level
        let bytes = name.as_bytes();
        let len = bytes.len().min(MAX_CONTEXT_LEN - 1);
        for (i, &b) in bytes[..len].iter().enumerate() {
            CONTEXT_STACK[1][i].store(b, Ordering::Release);
        }
        CONTEXT_STACK[1][len].store(0, Ordering::Release);
        CONTEXT_LENS[1].store(len, Ordering::Release);
    } else if depth == 1 {
        push_context(name);
    } else {
        push_context("unknown file");
        push_context(name);
    }
}

pub fn clear_current_test() {
    let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
    if depth >= 2 {
        CONTEXT_DEPTH.store(depth - 1, Ordering::Release);
    }
}

/// Size of the alternate signal stack (64 KiB - generous for our handler)
const ALT_STACK_SIZE: usize = 64 * 1024;

/// Approximate stack top address, recorded at handler installation time.
/// Used by the signal handler to determine if a fault is a stack overflow.
static STACK_TOP: AtomicUsize = AtomicUsize::new(0);

/// Install the signal handler for SIGSEGV/SIGBUS
/// Safe to call multiple times - will only install once
/// Call this early in main() for any vole command
///
/// Sets up an alternate signal stack so that the handler can run even when
/// the main stack is exhausted (stack overflow from infinite recursion).
pub fn install_segfault_handler() {
    if HANDLER_INSTALLED.swap(true, Ordering::SeqCst) {
        return; // Already installed
    }

    // Record the approximate stack top. This function is called early in main()
    // on the main thread's stack, so a local variable address is a good estimate
    // of the stack top. The stack grows downward from here.
    let stack_var: usize = 0;
    let approx_stack_top = std::ptr::addr_of!(stack_var) as usize;
    STACK_TOP.store(approx_stack_top, Ordering::Release);

    unsafe {
        // Allocate and install an alternate signal stack.
        // This is required for handling stack overflow - when the main stack
        // is exhausted, the kernel can't deliver the signal on it. The alternate
        // stack gives the handler a place to run.
        let alt_stack_mem = libc::mmap(
            std::ptr::null_mut(),
            ALT_STACK_SIZE,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        );

        if alt_stack_mem != libc::MAP_FAILED {
            let mut ss: libc::stack_t = std::mem::zeroed();
            ss.ss_sp = alt_stack_mem;
            ss.ss_size = ALT_STACK_SIZE;
            ss.ss_flags = 0;
            libc::sigaltstack(&ss, std::ptr::null_mut());
            // Note: we intentionally never free this memory - it must remain
            // valid for the entire process lifetime since signals can arrive
            // at any time.
        }

        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = segfault_handler as usize;
        // SA_SIGINFO: receive siginfo_t with fault address
        // SA_ONSTACK: use the alternate signal stack we just set up
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;

        libc::sigaction(libc::SIGSEGV, &action, std::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &action, std::ptr::null_mut());
    }
}

/// Check if a fault address looks like a stack overflow.
///
/// On Linux, the stack grows downward and there's a guard page at the bottom.
/// When we hit the guard page, the fault address will be very close to (or just
/// below) the stack limit. We compute the expected stack bottom from the
/// stack top (recorded at init) and the stack size limit, then check if the
/// fault is within a generous margin.
fn is_stack_overflow(fault_addr: usize) -> bool {
    let stack_top = STACK_TOP.load(Ordering::Acquire);
    if stack_top == 0 {
        return false;
    }

    // Get the stack size limit
    let mut rlim: libc::rlimit = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrlimit(libc::RLIMIT_STACK, &mut rlim) } != 0 {
        return false;
    }

    let stack_size = rlim.rlim_cur as usize;

    // The stack grows downward from stack_top. The bottom of the stack
    // (where the guard page is) is approximately at stack_top - stack_size.
    let stack_bottom = stack_top.saturating_sub(stack_size);

    // Check if fault address is near the stack bottom (within 256 KiB).
    // This generous margin accounts for:
    // - Large stack frames in JIT code
    // - Guard page size variations
    // - Imprecision in our stack_top estimate
    let margin = 256 * 1024;
    let lower = stack_bottom.saturating_sub(margin);
    let upper = stack_bottom.saturating_add(margin);

    fault_addr >= lower && fault_addr <= upper
}

/// Signal handler - must be async-signal-safe
///
/// Detects stack overflow (infinite recursion) and either recovers via
/// longjmp (in test context) or exits cleanly (in non-test context).
/// For non-stack-overflow segfaults, prints context and re-raises.
extern "C" fn segfault_handler(
    sig: libc::c_int,
    info: *mut libc::siginfo_t,
    _ctx: *mut libc::c_void,
) {
    unsafe {
        let stderr = 2;

        // Get the fault address from siginfo
        let fault_addr = if !info.is_null() {
            (*info).si_addr() as usize
        } else {
            0
        };

        // Check if this is a stack overflow
        if sig == libc::SIGSEGV && fault_addr != 0 && is_stack_overflow(fault_addr) {
            // Stack overflow detected - try to recover gracefully

            // If we're in test context with a jmp_buf, longjmp back
            // to the test harness with a failure indication.
            use crate::assert::{ASSERT_FAILURE, ASSERT_JMP_BUF, AssertFailure, siglongjmp};

            let recovered = ASSERT_JMP_BUF.with(|jb| {
                let buf = jb.get();
                if !buf.is_null() {
                    // Record the stack overflow as a failure
                    ASSERT_FAILURE.with(|f| {
                        f.set(Some(AssertFailure {
                            file: String::new(), // signal-safe: minimal allocation
                            line: 0,
                        }));
                    });

                    // Set a flag so the test runner can report "stack overflow"
                    STACK_OVERFLOW_FLAG.store(true, Ordering::Release);

                    // Unblock SIGSEGV before longjmp. While inside this signal
                    // handler, SIGSEGV is blocked. Since sigsetjmp was called
                    // with savemask=0, siglongjmp won't restore the mask, so
                    // we must unblock it manually to allow future signals.
                    let mut sigset: libc::sigset_t = std::mem::zeroed();
                    libc::sigemptyset(&mut sigset);
                    libc::sigaddset(&mut sigset, libc::SIGSEGV);
                    libc::pthread_sigmask(libc::SIG_UNBLOCK, &sigset, std::ptr::null_mut());

                    // longjmp back to the test harness
                    siglongjmp(buf, 2); // value=2 distinguishes from assert failure
                }
                false
            });

            if !recovered {
                // Not in test context - print error and exit
                let msg = b"\n\x1b[31merror:\x1b[0m stack overflow";
                libc::write(stderr, msg.as_ptr() as *const _, msg.len());
                let msg2 = b" (infinite recursion)\n";
                libc::write(stderr, msg2.as_ptr() as *const _, msg2.len());

                // Write context
                write_context(stderr);

                libc::_exit(1);
            }
            return;
        }

        // Non-stack-overflow segfault: print context and re-raise

        // Write header with signal type
        let (sig_name, sig_len): (&[u8], usize) = if sig == libc::SIGSEGV {
            (b"\n\x1b[31mSEGFAULT\x1b[0m", 18)
        } else {
            (b"\n\x1b[31mBUS ERROR\x1b[0m", 19)
        };
        libc::write(stderr, sig_name.as_ptr() as *const libc::c_void, sig_len);

        // Write context stack
        write_context(stderr);

        libc::write(stderr, b"\n".as_ptr() as *const libc::c_void, 1);

        // Re-raise with default handler for core dump
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        libc::sigaction(sig, &action, std::ptr::null_mut());
        libc::raise(sig);
    }
}

/// Write the context stack to a file descriptor (async-signal-safe)
unsafe fn write_context(fd: libc::c_int) {
    unsafe {
        let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
        if depth > 0 {
            libc::write(fd, b" in ".as_ptr() as *const libc::c_void, 4);

            for i in 0..depth {
                if i > 0 {
                    libc::write(fd, b" :: ".as_ptr() as *const libc::c_void, 4);
                }

                let len = CONTEXT_LENS[i].load(Ordering::Acquire);
                if len > 0 {
                    let mut buf = [0u8; MAX_CONTEXT_LEN];
                    for j in 0..len {
                        buf[j] = CONTEXT_STACK[i][j].load(Ordering::Acquire);
                    }
                    libc::write(fd, buf.as_ptr() as *const libc::c_void, len);
                }
            }
        }
    }
}

/// Flag set by signal handler when a stack overflow is detected.
/// Checked by the test runner to produce a "stack overflow" message
/// instead of a generic assertion failure.
static STACK_OVERFLOW_FLAG: AtomicBool = AtomicBool::new(false);

/// Check and clear the stack overflow flag.
/// Call this from the test runner after a longjmp recovery to determine
/// if the failure was caused by a stack overflow.
pub fn take_stack_overflow() -> bool {
    STACK_OVERFLOW_FLAG.swap(false, Ordering::AcqRel)
}

/// Reset all global runtime state after siglongjmp recovery.
///
/// When a stack overflow triggers siglongjmp, Rust destructors are skipped
/// on the unwound stack. This can leave global locks permanently held
/// (e.g. the type registry's RwLock). This function force-resets all such
/// state so that subsequent JIT compilation and execution can proceed.
///
/// Call this after every siglongjmp recovery (both in the test runner and
/// in compile_and_run).
pub fn recover_from_signal() {
    crate::type_registry::force_unlock_type_registry();
}

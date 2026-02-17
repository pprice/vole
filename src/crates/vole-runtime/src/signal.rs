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

// --- Platform-specific signal handling (Unix only) ---
// The segfault handler, stack overflow detection, and signal recovery
// use Unix-specific APIs (mmap, sigaltstack, sigaction, rlimit).
// On non-Unix platforms, these are no-ops.

#[cfg(unix)]
mod platform {
    use super::*;

    /// Size of the alternate signal stack (64 KiB - generous for our handler)
    const ALT_STACK_SIZE: usize = 64 * 1024;

    /// Approximate stack top address, recorded at handler installation time.
    static STACK_TOP: AtomicUsize = AtomicUsize::new(0);

    /// Flag set by signal handler when a stack overflow is detected.
    static STACK_OVERFLOW_FLAG: AtomicBool = AtomicBool::new(false);

    pub fn install_segfault_handler() {
        if HANDLER_INSTALLED.swap(true, Ordering::SeqCst) {
            return;
        }

        let stack_var: usize = 0;
        let approx_stack_top = std::ptr::addr_of!(stack_var) as usize;
        STACK_TOP.store(approx_stack_top, Ordering::Release);

        unsafe {
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
            }

            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = segfault_handler as usize;
            action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;

            libc::sigaction(libc::SIGSEGV, &action, std::ptr::null_mut());
            libc::sigaction(libc::SIGBUS, &action, std::ptr::null_mut());
        }
    }

    fn is_stack_overflow(fault_addr: usize) -> bool {
        let stack_top = STACK_TOP.load(Ordering::Acquire);
        if stack_top == 0 {
            return false;
        }

        let mut rlim: libc::rlimit = unsafe { std::mem::zeroed() };
        if unsafe { libc::getrlimit(libc::RLIMIT_STACK, &mut rlim) } != 0 {
            return false;
        }

        let stack_size = rlim.rlim_cur as usize;
        let stack_bottom = stack_top.saturating_sub(stack_size);

        let margin = 256 * 1024;
        let lower = stack_bottom.saturating_sub(margin);
        let upper = stack_bottom.saturating_add(margin);

        fault_addr >= lower && fault_addr <= upper
    }

    extern "C" fn segfault_handler(
        sig: libc::c_int,
        info: *mut libc::siginfo_t,
        _ctx: *mut libc::c_void,
    ) {
        unsafe {
            let stderr = 2;

            let fault_addr = if !info.is_null() {
                (*info).si_addr() as usize
            } else {
                0
            };

            if sig == libc::SIGSEGV && fault_addr != 0 && is_stack_overflow(fault_addr) {
                use crate::assert::{ASSERT_FAILURE, ASSERT_JMP_BUF, AssertFailure, siglongjmp};

                let recovered = ASSERT_JMP_BUF.with(|jb| {
                    let buf = jb.get();
                    if !buf.is_null() {
                        ASSERT_FAILURE.with(|f| {
                            f.set(Some(AssertFailure {
                                file: String::new(),
                                line: 0,
                            }));
                        });

                        STACK_OVERFLOW_FLAG.store(true, Ordering::Release);

                        let mut sigset: libc::sigset_t = std::mem::zeroed();
                        libc::sigemptyset(&mut sigset);
                        libc::sigaddset(&mut sigset, libc::SIGSEGV);
                        libc::pthread_sigmask(libc::SIG_UNBLOCK, &sigset, std::ptr::null_mut());

                        siglongjmp(buf, 2);
                    }
                    false
                });

                if !recovered {
                    let msg = b"\n\x1b[31merror:\x1b[0m stack overflow";
                    libc::write(stderr, msg.as_ptr() as *const _, msg.len());
                    let msg2 = b" (infinite recursion)\n";
                    libc::write(stderr, msg2.as_ptr() as *const _, msg2.len());

                    write_context(stderr);

                    libc::_exit(1);
                }
                return;
            }

            let (sig_name, sig_len): (&[u8], usize) = if sig == libc::SIGSEGV {
                (b"\n\x1b[31mSEGFAULT\x1b[0m", 18)
            } else {
                (b"\n\x1b[31mBUS ERROR\x1b[0m", 19)
            };
            libc::write(stderr, sig_name.as_ptr() as *const libc::c_void, sig_len);

            write_context(stderr);

            libc::write(stderr, b"\n".as_ptr() as *const libc::c_void, 1);

            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = libc::SIG_DFL;
            libc::sigaction(sig, &action, std::ptr::null_mut());
            libc::raise(sig);
        }
    }

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

    pub fn take_stack_overflow() -> bool {
        STACK_OVERFLOW_FLAG.swap(false, Ordering::AcqRel)
    }

    pub fn recover_from_signal() {
        crate::type_registry::force_unlock_type_registry();
    }
}

#[cfg(not(unix))]
mod platform {
    pub fn install_segfault_handler() {
        // No signal handling on non-Unix platforms
    }

    pub fn take_stack_overflow() -> bool {
        false
    }

    pub fn recover_from_signal() {
        // No-op on non-Unix platforms
    }
}

pub fn install_segfault_handler() {
    platform::install_segfault_handler();
}

pub fn take_stack_overflow() -> bool {
    platform::take_stack_overflow()
}

pub fn recover_from_signal() {
    platform::recover_from_signal();
}

// src/runtime/signal.rs
//
// Signal handling for segfault debugging.
// Registers a SIGSEGV handler that dumps the current context before dying.
// Works for any vole command (test, run, check, etc.)

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Maximum context entries (stack depth)
const MAX_CONTEXT_DEPTH: usize = 8;
/// Maximum length of each context entry
const MAX_CONTEXT_LEN: usize = 256;

/// Context stack - each entry describes what we're doing
/// e.g., ["running foo.vole", "executing function main", "calling method bar"]
#[allow(clippy::declare_interior_mutable_const)]
static CONTEXT_STACK: [[std::sync::atomic::AtomicU8; MAX_CONTEXT_LEN]; MAX_CONTEXT_DEPTH] = {
    const INIT_BYTE: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);
    const INIT_ENTRY: [std::sync::atomic::AtomicU8; MAX_CONTEXT_LEN] = [INIT_BYTE; MAX_CONTEXT_LEN];
    [INIT_ENTRY; MAX_CONTEXT_DEPTH]
};
#[allow(clippy::declare_interior_mutable_const)]
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

/// Install the signal handler for SIGSEGV/SIGBUS
/// Safe to call multiple times - will only install once
/// Call this early in main() for any vole command
pub fn install_segfault_handler() {
    if HANDLER_INSTALLED.swap(true, Ordering::SeqCst) {
        return; // Already installed
    }

    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = segfault_handler as usize;
        action.sa_flags = libc::SA_SIGINFO;

        libc::sigaction(libc::SIGSEGV, &action, std::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &action, std::ptr::null_mut());
    }
}

/// Signal handler - must be async-signal-safe
extern "C" fn segfault_handler(
    sig: libc::c_int,
    _info: *mut libc::siginfo_t,
    _ctx: *mut libc::c_void,
) {
    unsafe {
        let stderr = 2;

        // Write header with signal type
        let (sig_name, sig_len): (&[u8], usize) = if sig == libc::SIGSEGV {
            (b"\n\x1b[31mSEGFAULT\x1b[0m", 18)
        } else {
            (b"\n\x1b[31mBUS ERROR\x1b[0m", 19)
        };
        libc::write(stderr, sig_name.as_ptr() as *const libc::c_void, sig_len);

        // Write context stack
        let depth = CONTEXT_DEPTH.load(Ordering::Acquire);
        if depth > 0 {
            libc::write(stderr, b" in ".as_ptr() as *const libc::c_void, 4);

            for i in 0..depth {
                if i > 0 {
                    libc::write(stderr, b" :: ".as_ptr() as *const libc::c_void, 4);
                }

                let len = CONTEXT_LENS[i].load(Ordering::Acquire);
                if len > 0 {
                    let mut buf = [0u8; MAX_CONTEXT_LEN];
                    for j in 0..len {
                        buf[j] = CONTEXT_STACK[i][j].load(Ordering::Acquire);
                    }
                    libc::write(stderr, buf.as_ptr() as *const libc::c_void, len);
                }
            }
        }

        libc::write(stderr, b"\n".as_ptr() as *const libc::c_void, 1);

        // Re-raise with default handler for core dump
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        libc::sigaction(sig, &action, std::ptr::null_mut());
        libc::raise(sig);
    }
}

//! Vole runtime: values, builtins, and standard library support.
//!
//! # Safety: Raw Pointer Arguments in FFI Functions
//!
//! This crate provides FFI functions called by JIT-compiled Vole code. These functions
//! receive raw pointers that are always valid when called through the Vole runtime because:
//! - The JIT compiler only passes pointers to live, properly-allocated Vole values
//! - Reference counting ensures objects remain valid for their lifetime
//! - The type system prevents null or dangling pointers from reaching runtime functions
//!
//! We allow `clippy::not_unsafe_ptr_arg_deref` per-function since marking every FFI function
//! as `unsafe` would add noise without improving safety (callers are generated code, not Rust).
pub mod alloc_track;
pub mod array;
pub mod assert;
pub mod builtins;
pub mod closure;
pub mod coroutine;
pub mod instance;
pub mod iterator;
pub(crate) mod iterator_abi;
pub(crate) mod iterator_core;
#[cfg(test)]
mod iterator_parity;
pub mod native_registry;
pub mod signal;
pub mod stdlib;
pub mod string;
pub mod string_builder;
pub mod type_registry;
pub mod value;

pub use assert::{
    AssertFailure, JmpBuf, call_setjmp, clear_test_jmp_buf, set_test_jmp_buf, take_assert_failure,
    vole_assert_fail,
};
pub use builtins::set_capture_mode;
pub use builtins::set_stderr_capture;
pub use builtins::set_stdout_capture;
pub use builtins::write_to_stderr_capture;
pub use instance::RcInstance;
pub use native_registry::{
    NativeFunction, NativeModule, NativeRegistry, NativeSignature, NativeType,
};
pub use signal::{
    clear_context, clear_current_test, install_segfault_handler, pop_context, push_context,
    recover_from_signal, replace_context, set_current_file, set_current_test, take_stack_overflow,
};
pub use string::{Fnv1aHasher, RcString, fnv1a_hash};
pub use value::{Context, RC_PINNED, RcHeader, RuntimeTypeId};

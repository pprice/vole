//! Vole runtime: values, builtins, and standard library support.
pub mod array;
pub mod assert;
pub mod builtins;
pub mod closure;
pub mod collections;
pub mod instance;
pub mod iterator;
pub mod native_registry;
pub mod signal;
pub mod stdlib;
pub mod string;
pub mod type_registry;
pub mod value;

pub use assert::{
    AssertFailure, JmpBuf, call_setjmp, clear_test_jmp_buf, set_test_jmp_buf, take_assert_failure,
    vole_assert_fail,
};
pub use builtins::set_stdout_capture;
pub use instance::RcInstance;
pub use native_registry::{
    NativeFunction, NativeModule, NativeRegistry, NativeSignature, NativeType,
};
pub use signal::{
    clear_context, clear_current_test, install_segfault_handler, pop_context, push_context,
    replace_context, set_current_file, set_current_test,
};
pub use string::RcString;
pub use value::{Context, RcHeader, TYPE_STRING};

// src/runtime/stdlib/builtins.rs
//! Native builtin functions for the vole:builtins module.
//!
//! Provides the low-level native functions that back Vole's built-in operations:
//! - `_print_string(s: string)` - print string without newline
//! - `_println_string(s: string)` - print string with newline
//! - `panic(message: string) -> !` - terminate execution with message

use crate::builtins::{vole_panic, vole_print_string, vole_println_string};
use crate::native_registry::{NativeModule, NativeSignature, NativeType};
use crate::string::RcString;

/// Create the vole:builtins native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // _print_string: (string) -> nil - print without newline
    m.register(
        "_print_string",
        vole_print_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Nil,
        },
    );

    // _println_string: (string) -> nil - print with newline
    m.register(
        "_println_string",
        vole_println_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Nil,
        },
    );

    // panic: (string) -> ! - terminate execution with message
    // Wraps vole_panic with a simplified single-argument interface
    m.register(
        "panic",
        builtins_panic as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::Nil,
        },
    );

    m
}

// =============================================================================
// Native function implementations
// =============================================================================

/// Simplified panic wrapper that takes only a message string.
/// Provides placeholder file/line info since the caller is a Vole builtin.
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn builtins_panic(msg: *const RcString) -> ! {
    static BUILTIN_FILE: &[u8] = b"<builtins>";
    vole_panic(msg, BUILTIN_FILE.as_ptr(), BUILTIN_FILE.len(), 0)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("_print_string").is_some());
        assert!(m.get("_println_string").is_some());
        assert!(m.get("panic").is_some());

        // Check _print_string signature
        let print_func = m.get("_print_string").unwrap();
        assert_eq!(print_func.signature.params.len(), 1);
        assert_eq!(print_func.signature.params[0], NativeType::String);
        assert_eq!(print_func.signature.return_type, NativeType::Nil);

        // Check _println_string signature
        let println_func = m.get("_println_string").unwrap();
        assert_eq!(println_func.signature.params.len(), 1);
        assert_eq!(println_func.signature.params[0], NativeType::String);
        assert_eq!(println_func.signature.return_type, NativeType::Nil);

        // Check panic signature
        let panic_func = m.get("panic").unwrap();
        assert_eq!(panic_func.signature.params.len(), 1);
        assert_eq!(panic_func.signature.params[0], NativeType::String);
        assert_eq!(panic_func.signature.return_type, NativeType::Nil);
    }
}

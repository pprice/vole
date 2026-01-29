// src/runtime/stdlib/builtins.rs
//! Native builtin functions for the vole:builtins module.
//!
//! Provides the low-level native functions that back Vole's built-in operations:
//! - `_print_string(s: string)` - print string without newline
//! - `_println_string(s: string)` - print string with newline

use crate::builtins::{vole_print_string, vole_println_string};
use crate::native_registry::{NativeModule, NativeSignature, NativeType};

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

    m
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
    }
}

// src/runtime/stdlib/buffer.rs
//! Native buffer functions for std:buffer module.
//!
//! Provides a reference-counted byte buffer for binary data manipulation.
//! Buffer handles are passed as opaque i64 pointers through the FFI boundary.

use crate::buffer;
use crate::native_registry::{NativeModule, NativeSignature, NativeType};

/// Create the std:buffer native module
pub fn module() -> NativeModule {
    let mut m = NativeModule::new();

    // new: () -> i64 (opaque RcBuffer pointer)
    m.register(
        "new",
        buffer::buffer_new as *const u8,
        NativeSignature {
            params: vec![],
            return_type: NativeType::I64,
        },
    );

    // with_capacity: (i64) -> i64 (opaque RcBuffer pointer)
    m.register(
        "with_capacity",
        buffer::buffer_with_capacity as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // len: (i64) -> i64
    m.register(
        "len",
        buffer::buffer_len as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // capacity: (i64) -> i64
    m.register(
        "capacity",
        buffer::buffer_capacity as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // append_byte: (i64, i64) -> void (returns nil)
    m.register(
        "append_byte",
        buffer::buffer_append_byte as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // append: (i64, i64) -> void (returns nil)
    m.register(
        "append",
        buffer::buffer_append as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // get: (i64, i64) -> i64
    m.register(
        "get",
        buffer::buffer_get as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // set: (i64, i64, i64) -> void (returns nil)
    m.register(
        "set",
        buffer::buffer_set as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // slice: (i64, i64, i64) -> i64 (new RcBuffer pointer)
    m.register(
        "slice",
        buffer::buffer_slice as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    // to_string: (i64) -> string
    m.register(
        "to_string",
        buffer::buffer_to_string as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::String,
        },
    );

    // from_string: (string) -> i64 (new RcBuffer pointer)
    m.register(
        "from_string",
        buffer::buffer_from_string as *const u8,
        NativeSignature {
            params: vec![NativeType::String],
            return_type: NativeType::I64,
        },
    );

    // clear: (i64) -> void (returns nil)
    m.register(
        "clear",
        buffer::buffer_clear as *const u8,
        NativeSignature {
            params: vec![NativeType::I64],
            return_type: NativeType::Nil,
        },
    );

    // equals: (i64, i64) -> i64 (1/0)
    m.register(
        "equals",
        buffer::buffer_equals as *const u8,
        NativeSignature {
            params: vec![NativeType::I64, NativeType::I64],
            return_type: NativeType::I64,
        },
    );

    m
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_module_registration() {
        let m = module();

        // Check all functions are registered
        assert!(m.get("new").is_some());
        assert!(m.get("with_capacity").is_some());
        assert!(m.get("len").is_some());
        assert!(m.get("capacity").is_some());
        assert!(m.get("append_byte").is_some());
        assert!(m.get("append").is_some());
        assert!(m.get("get").is_some());
        assert!(m.get("set").is_some());
        assert!(m.get("slice").is_some());
        assert!(m.get("to_string").is_some());
        assert!(m.get("from_string").is_some());
        assert!(m.get("clear").is_some());
        assert!(m.get("equals").is_some());
    }

    #[test]
    fn test_new_signature() {
        let m = module();
        let f = m.get("new").unwrap();
        assert!(f.signature.params.is_empty());
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn test_with_capacity_signature() {
        let m = module();
        let f = m.get("with_capacity").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn test_len_signature() {
        let m = module();
        let f = m.get("len").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn test_append_byte_signature() {
        let m = module();
        let f = m.get("append_byte").unwrap();
        assert_eq!(f.signature.params.len(), 2);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.params[1], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::Nil);
    }

    #[test]
    fn test_set_signature() {
        let m = module();
        let f = m.get("set").unwrap();
        assert_eq!(f.signature.params.len(), 3);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.params[1], NativeType::I64);
        assert_eq!(f.signature.params[2], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::Nil);
    }

    #[test]
    fn test_to_string_signature() {
        let m = module();
        let f = m.get("to_string").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::String);
    }

    #[test]
    fn test_from_string_signature() {
        let m = module();
        let f = m.get("from_string").unwrap();
        assert_eq!(f.signature.params.len(), 1);
        assert_eq!(f.signature.params[0], NativeType::String);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }

    #[test]
    fn test_slice_signature() {
        let m = module();
        let f = m.get("slice").unwrap();
        assert_eq!(f.signature.params.len(), 3);
        assert_eq!(f.signature.params[0], NativeType::I64);
        assert_eq!(f.signature.params[1], NativeType::I64);
        assert_eq!(f.signature.params[2], NativeType::I64);
        assert_eq!(f.signature.return_type, NativeType::I64);
    }
}

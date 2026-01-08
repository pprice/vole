// src/runtime/type_registry.rs
//
// Runtime type registry for field cleanup information.
// Populated at JIT compile time, used at runtime to properly clean up
// reference-counted fields when instances are freed.

use crate::runtime::value::{TYPE_ARRAY, TYPE_INSTANCE, TYPE_STRING};
use std::collections::HashMap;
use std::sync::RwLock;

/// Field type info for cleanup purposes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeTag {
    /// Non-reference type (i64, f64, bool, etc.) - no cleanup needed
    Value,
    /// String field - needs RcString::dec_ref
    String,
    /// Array field - needs RcArray::dec_ref
    Array,
    /// Instance field - needs RcInstance::dec_ref
    Instance,
}

impl FieldTypeTag {
    /// Convert from runtime type ID to field type tag
    pub fn from_type_id(type_id: u32) -> Self {
        match type_id {
            TYPE_STRING => FieldTypeTag::String,
            TYPE_ARRAY => FieldTypeTag::Array,
            TYPE_INSTANCE => FieldTypeTag::Instance,
            _ => FieldTypeTag::Value,
        }
    }

    /// Check if this field type needs reference count cleanup
    pub fn needs_cleanup(&self) -> bool {
        !matches!(self, FieldTypeTag::Value)
    }
}

/// Type info for an instance type (class or record)
#[derive(Debug, Clone)]
pub struct InstanceTypeInfo {
    /// Field types in slot order
    pub field_types: Vec<FieldTypeTag>,
}

impl InstanceTypeInfo {
    /// Check if any field needs cleanup
    pub fn needs_cleanup(&self) -> bool {
        self.field_types.iter().any(|t| t.needs_cleanup())
    }
}

/// Global type registry for field cleanup info
static TYPE_REGISTRY: RwLock<Option<HashMap<u32, InstanceTypeInfo>>> = RwLock::new(None);

/// Initialize the type registry (call once at startup)
pub fn init_type_registry() {
    let mut guard = TYPE_REGISTRY.write().unwrap();
    if guard.is_none() {
        *guard = Some(HashMap::new());
    }
}

/// Register field types for an instance type
/// Called from JIT compilation when a class/record is registered
pub fn register_instance_type(type_id: u32, field_types: Vec<FieldTypeTag>) {
    let mut guard = TYPE_REGISTRY.write().unwrap();
    let registry = guard.get_or_insert_with(HashMap::new);
    registry.insert(type_id, InstanceTypeInfo { field_types });
}

/// Get field types for an instance type
/// Returns None if type_id not registered (shouldn't happen in correct programs)
pub fn get_instance_type_info(type_id: u32) -> Option<InstanceTypeInfo> {
    let guard = TYPE_REGISTRY.read().unwrap();
    guard.as_ref()?.get(&type_id).cloned()
}

/// Clear the type registry (for testing or recompilation)
pub fn clear_type_registry() {
    let mut guard = TYPE_REGISTRY.write().unwrap();
    if let Some(ref mut registry) = *guard {
        registry.clear();
    }
}

// FFI functions for JIT-compiled code

/// Register field types for an instance type (FFI)
/// field_types is an array of u8 tags (0=Value, 1=String, 2=Array, 3=Instance)
#[allow(clippy::not_unsafe_ptr_arg_deref)]
#[unsafe(no_mangle)]
pub extern "C" fn vole_register_instance_type(
    type_id: u32,
    field_count: u32,
    field_types: *const u8,
) {
    if field_types.is_null() && field_count > 0 {
        return;
    }

    let types: Vec<FieldTypeTag> = if field_count == 0 {
        Vec::new()
    } else {
        unsafe {
            (0..field_count as usize)
                .map(|i| match *field_types.add(i) {
                    1 => FieldTypeTag::String,
                    2 => FieldTypeTag::Array,
                    3 => FieldTypeTag::Instance,
                    _ => FieldTypeTag::Value,
                })
                .collect()
        }
    };

    register_instance_type(type_id, types);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_field_type_tag_from_type_id() {
        assert_eq!(
            FieldTypeTag::from_type_id(TYPE_STRING),
            FieldTypeTag::String
        );
        assert_eq!(FieldTypeTag::from_type_id(TYPE_ARRAY), FieldTypeTag::Array);
        assert_eq!(
            FieldTypeTag::from_type_id(TYPE_INSTANCE),
            FieldTypeTag::Instance
        );
        assert_eq!(FieldTypeTag::from_type_id(0), FieldTypeTag::Value);
        assert_eq!(FieldTypeTag::from_type_id(2), FieldTypeTag::Value); // TYPE_I64
    }

    #[test]
    fn test_register_and_get() {
        init_type_registry();
        clear_type_registry();

        register_instance_type(
            42,
            vec![
                FieldTypeTag::Value,
                FieldTypeTag::String,
                FieldTypeTag::Instance,
            ],
        );

        let info = get_instance_type_info(42).unwrap();
        assert_eq!(info.field_types.len(), 3);
        assert_eq!(info.field_types[0], FieldTypeTag::Value);
        assert_eq!(info.field_types[1], FieldTypeTag::String);
        assert_eq!(info.field_types[2], FieldTypeTag::Instance);
        assert!(info.needs_cleanup());

        // Clean up
        clear_type_registry();
    }

    #[test]
    fn test_no_cleanup_needed() {
        init_type_registry();
        clear_type_registry();

        register_instance_type(99, vec![FieldTypeTag::Value, FieldTypeTag::Value]);

        let info = get_instance_type_info(99).unwrap();
        assert!(!info.needs_cleanup());

        clear_type_registry();
    }
}

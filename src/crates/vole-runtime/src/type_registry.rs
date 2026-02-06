// src/runtime/type_registry.rs
//
// Runtime type registry for field cleanup information.
// Populated at JIT compile time, used at runtime to properly clean up
// reference-counted fields when instances are freed.

use rustc_hash::FxHashMap;
use std::sync::RwLock;
use std::sync::atomic::{AtomicU32, Ordering};

/// Field type info for cleanup purposes.
///
/// With RcHeader v2, each RC allocation carries its own drop_fn,
/// so the type registry only needs to know Value vs Rc (needs rc_dec).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FieldTypeTag {
    /// Non-reference type (i64, f64, bool, etc.) - no cleanup needed
    Value,
    /// Reference-counted field (String, Array, Instance) - needs rc_dec
    Rc,
}

impl FieldTypeTag {
    /// Check if this field type needs reference count cleanup
    pub fn needs_cleanup(&self) -> bool {
        matches!(self, FieldTypeTag::Rc)
    }
}

/// Type info for an instance type (class or struct)
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
static TYPE_REGISTRY: RwLock<Option<FxHashMap<u32, InstanceTypeInfo>>> = RwLock::new(None);

/// Global counter for allocating unique runtime type IDs.
///
/// Each class instance needs a unique type_id so the runtime type registry
/// can look up field cleanup info during instance_drop. This counter is
/// global (not per-Compiler) to prevent type_id collisions when multiple
/// Compiler instances register classes from different modules.
static NEXT_TYPE_ID: AtomicU32 = AtomicU32::new(0);

/// Allocate a unique runtime type ID. Thread-safe and globally unique.
pub fn alloc_type_id() -> u32 {
    NEXT_TYPE_ID.fetch_add(1, Ordering::Relaxed)
}

/// Initialize the type registry (call once at startup)
pub fn init_type_registry() {
    let mut guard = TYPE_REGISTRY.write().unwrap();
    if guard.is_none() {
        *guard = Some(FxHashMap::default());
    }
}

/// Register field types for an instance type
/// Called from JIT compilation when a class is registered
pub fn register_instance_type(type_id: u32, field_types: Vec<FieldTypeTag>) {
    let mut guard = TYPE_REGISTRY.write().unwrap();
    let registry = guard.get_or_insert_with(FxHashMap::default);
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
/// field_types is an array of u8 tags (0=Value, 1=Rc)
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
                    1 => FieldTypeTag::Rc,
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
    fn test_field_type_tag_needs_cleanup() {
        assert!(!FieldTypeTag::Value.needs_cleanup());
        assert!(FieldTypeTag::Rc.needs_cleanup());
    }

    // Note: These tests use unique type IDs and don't clear the registry to
    // avoid race conditions when running tests in parallel. The global registry
    // is safe to share across tests as long as each test uses distinct IDs.

    #[test]
    fn test_register_and_get() {
        // Use a unique type ID for this test (0x1000_0001)
        let test_type_id = 0x1000_0001;
        init_type_registry();

        register_instance_type(
            test_type_id,
            vec![FieldTypeTag::Value, FieldTypeTag::Rc, FieldTypeTag::Rc],
        );

        let info = get_instance_type_info(test_type_id).unwrap();
        assert_eq!(info.field_types.len(), 3);
        assert_eq!(info.field_types[0], FieldTypeTag::Value);
        assert_eq!(info.field_types[1], FieldTypeTag::Rc);
        assert_eq!(info.field_types[2], FieldTypeTag::Rc);
        assert!(info.needs_cleanup());
    }

    #[test]
    fn test_no_cleanup_needed() {
        // Use a unique type ID for this test (0x1000_0002)
        let test_type_id = 0x1000_0002;
        init_type_registry();

        register_instance_type(test_type_id, vec![FieldTypeTag::Value, FieldTypeTag::Value]);

        let info = get_instance_type_info(test_type_id).unwrap();
        assert!(!info.needs_cleanup());
    }
}

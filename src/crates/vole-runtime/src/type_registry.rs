// src/runtime/type_registry.rs
//
// Runtime type registry for field cleanup information.
// Populated at JIT compile time, used at runtime to properly clean up
// reference-counted fields when instances are freed.
//
// Uses a custom atomic-based RwLock instead of std::sync::RwLock because
// siglongjmp-based recovery from stack overflow can skip Drop on lock guards,
// leaving a std RwLock permanently held. Our atomic lock can be force-reset
// after signal recovery via `force_unlock_type_registry()`.

use rustc_hash::FxHashMap;
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicI32, AtomicU32, Ordering};

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
    /// Union heap buffer field (e.g. `Person?` in a class) - needs union_heap_cleanup
    UnionHeap,
    /// Interface fat pointer field - heap-allocated [data_word, vtable_ptr].
    /// Cleanup must: rc_dec(data_word at offset 0), then free the 16-byte allocation.
    Interface,
}

impl FieldTypeTag {
    /// Check if this field type needs reference count cleanup
    pub fn needs_cleanup(&self) -> bool {
        matches!(
            self,
            FieldTypeTag::Rc | FieldTypeTag::UnionHeap | FieldTypeTag::Interface
        )
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

/// Atomic-based RwLock for the type registry.
///
/// State values:
///   0      = unlocked
///   N > 0  = N readers holding the lock
///   -1     = writer holding the lock
///
/// This lock can be force-reset to 0 via `force_unlock()` after siglongjmp
/// recovery, which std::sync::RwLock cannot do (it would be permanently stuck
/// or poisoned).
struct RegistryLock {
    state: AtomicI32,
    data: UnsafeCell<Option<FxHashMap<u32, InstanceTypeInfo>>>,
}

// Safety: the AtomicI32 synchronizes access to the UnsafeCell data
unsafe impl Sync for RegistryLock {}

impl RegistryLock {
    const fn new() -> Self {
        Self {
            state: AtomicI32::new(0),
            data: UnsafeCell::new(None),
        }
    }

    /// Acquire a read lock. Spins briefly, then yields.
    fn read<R>(&self, f: impl FnOnce(&FxHashMap<u32, InstanceTypeInfo>) -> R) -> R {
        loop {
            let s = self.state.load(Ordering::Acquire);
            if s >= 0
                && self
                    .state
                    .compare_exchange_weak(s, s + 1, Ordering::Acquire, Ordering::Relaxed)
                    .is_ok()
            {
                // Safety: we hold a read lock (state > 0), no writer active
                let data = unsafe { &*self.data.get() };
                let empty = FxHashMap::default();
                let map = data.as_ref().unwrap_or(&empty);
                let result = f(map);
                self.state.fetch_sub(1, Ordering::Release);
                return result;
            }
            std::hint::spin_loop();
        }
    }

    /// Acquire a write lock. Spins briefly, then yields.
    fn write<R>(&self, f: impl FnOnce(&mut FxHashMap<u32, InstanceTypeInfo>) -> R) -> R {
        loop {
            if self
                .state
                .compare_exchange_weak(0, -1, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                // Safety: we hold the write lock (state == -1), exclusive access
                let data = unsafe { &mut *self.data.get() };
                let map = data.get_or_insert_with(FxHashMap::default);
                let result = f(map);
                self.state.store(0, Ordering::Release);
                return result;
            }
            std::hint::spin_loop();
        }
    }

    /// Force-reset the lock to unlocked state.
    ///
    /// Called after siglongjmp recovery when a lock guard may have been
    /// abandoned on the unwound stack. The data is safe because:
    /// - A read was interrupted: data wasn't being modified
    /// - A write was interrupted: the insert may be partial, but the
    ///   HashMap is still valid (Rust's HashMap doesn't have torn writes
    ///   at the entry level, and we'll re-register the type anyway)
    fn force_unlock(&self) {
        self.state.store(0, Ordering::Release);
    }
}

static TYPE_REGISTRY: RegistryLock = RegistryLock::new();

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
    // No-op: the registry is initialized in the const constructor.
    // Kept for API compatibility.
}

/// Register field types for an instance type
/// Called from JIT compilation when a class is registered
pub fn register_instance_type(type_id: u32, field_types: Vec<FieldTypeTag>) {
    TYPE_REGISTRY.write(|registry| {
        registry.insert(type_id, InstanceTypeInfo { field_types });
    });
}

/// Get field types for an instance type
/// Returns None if type_id not registered (shouldn't happen in correct programs)
pub fn get_instance_type_info(type_id: u32) -> Option<InstanceTypeInfo> {
    TYPE_REGISTRY.read(|registry| registry.get(&type_id).cloned())
}

/// Clear the type registry (for testing or recompilation)
pub fn clear_type_registry() {
    TYPE_REGISTRY.write(|registry| {
        registry.clear();
    });
}

/// Force-unlock the type registry after signal recovery (siglongjmp).
///
/// When a stack overflow triggers siglongjmp, any lock guard on the type
/// registry is abandoned without Drop being called. This resets the lock
/// so subsequent operations don't deadlock.
pub fn force_unlock_type_registry() {
    TYPE_REGISTRY.force_unlock();
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
                    2 => FieldTypeTag::UnionHeap,
                    3 => FieldTypeTag::Interface,
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

    #[test]
    fn test_force_unlock_recovers_from_stuck_reader() {
        // Test force_unlock on a LOCAL lock to avoid poisoning the global
        // TYPE_REGISTRY for parallel tests.
        let lock = RegistryLock::new();

        // Pre-populate
        lock.write(|map| {
            map.insert(
                1,
                InstanceTypeInfo {
                    field_types: vec![FieldTypeTag::Rc],
                },
            );
        });

        // Simulate abandoned read lock (state = 1 means 1 reader held)
        lock.state.store(1, Ordering::Release);

        // Force unlock as recovery code would do after siglongjmp
        lock.force_unlock();

        // Verify write works after recovery (would deadlock without fix)
        lock.write(|map| {
            map.insert(
                2,
                InstanceTypeInfo {
                    field_types: vec![FieldTypeTag::Value, FieldTypeTag::Rc],
                },
            );
        });

        let info = lock.read(|map| map.get(&2).cloned()).unwrap();
        assert_eq!(info.field_types.len(), 2);

        // Verify old data is still accessible
        let old_info = lock.read(|map| map.get(&1).cloned()).unwrap();
        assert_eq!(old_info.field_types.len(), 1);
        assert_eq!(old_info.field_types[0], FieldTypeTag::Rc);
    }

    #[test]
    fn test_force_unlock_recovers_from_stuck_writer() {
        // Test force_unlock on a LOCAL lock to avoid poisoning the global
        // TYPE_REGISTRY for parallel tests.
        let lock = RegistryLock::new();

        // Pre-populate
        lock.write(|map| {
            map.insert(
                1,
                InstanceTypeInfo {
                    field_types: vec![FieldTypeTag::Value],
                },
            );
        });

        // Simulate abandoned write lock (state = -1)
        lock.state.store(-1, Ordering::Release);

        // Force unlock
        lock.force_unlock();

        // Verify read works after recovery
        let info = lock.read(|map| map.get(&1).cloned()).unwrap();
        assert_eq!(info.field_types[0], FieldTypeTag::Value);

        // Verify write works after recovery
        lock.write(|map| {
            map.insert(
                2,
                InstanceTypeInfo {
                    field_types: vec![FieldTypeTag::Rc, FieldTypeTag::Rc],
                },
            );
        });
        let info = lock.read(|map| map.get(&2).cloned()).unwrap();
        assert_eq!(info.field_types.len(), 2);
    }
}

// type_meta_cache.rs
//!
//! Per-type singleton cache for TypeMeta instances.
//!
//! TypeMeta is immutable and identical for a given type, so we cache it to
//! avoid rebuilding on every `.@meta` access. The cache is a simple Vec of
//! (runtime_type_id, TypeMeta_ptr) pairs with linear scan — there are few
//! distinct types accessed via `.@meta` in practice.
//!
//! The cache holds one RC reference per entry. `type_meta_cache_clear` releases
//! all references and is called between leak-checker tests to maintain a zero
//! allocation delta.

use std::cell::RefCell;

use crate::value::rc_dec;

thread_local! {
    static CACHE: RefCell<Vec<(u32, *mut u8)>> = const { RefCell::new(Vec::new()) };
}

/// Look up a cached TypeMeta pointer by runtime type_id.
/// Returns null if not cached.
#[unsafe(no_mangle)]
pub extern "C" fn type_meta_cache_get(type_id: u32) -> *mut u8 {
    CACHE.with(|c| {
        let cache = c.borrow();
        for &(id, ptr) in cache.iter() {
            if id == type_id {
                return ptr;
            }
        }
        std::ptr::null_mut()
    })
}

/// Store a TypeMeta pointer in the cache. The cache takes ownership of one
/// RC reference (the caller must have already rc_inc'd for itself).
#[unsafe(no_mangle)]
pub extern "C" fn type_meta_cache_store(type_id: u32, ptr: *mut u8) {
    CACHE.with(|c| {
        c.borrow_mut().push((type_id, ptr));
    });
}

/// Clear the cache, rc_dec'ing all entries.
/// Called between tests by the leak checker.
pub fn type_meta_cache_clear() {
    CACHE.with(|c| {
        let entries: Vec<(u32, *mut u8)> = c.borrow_mut().drain(..).collect();
        for (_, ptr) in entries {
            rc_dec(ptr);
        }
    });
}

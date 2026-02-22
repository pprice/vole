// src/runtime/alloc_track.rs
//! Allocation tracking for leak detection.
//!
//! When enabled, tracks per-type allocation counts using atomic counters.
//! Disabled by default; `enable_tracking()` turns it on (called by vole-leak).
//! When disabled, `track_alloc`/`track_dealloc` check the flag and return
//! immediately (branch-predicted no-op).

use std::sync::atomic::{AtomicBool, AtomicI64, Ordering};

/// Number of type slots. Must be greater than the highest RuntimeTypeId variant.
const NUM_TYPE_SLOTS: usize = 16;

/// Per-type allocation counters, indexed by RuntimeTypeId discriminant.
static TYPE_COUNTERS: [AtomicI64; NUM_TYPE_SLOTS] = {
    #[expect(clippy::declare_interior_mutable_const)]
    const ZERO: AtomicI64 = AtomicI64::new(0);
    [ZERO; NUM_TYPE_SLOTS]
};

/// Total live-allocation counter (sum of all per-type counters).
static TOTAL: AtomicI64 = AtomicI64::new(0);

/// Whether tracking is active. Default false.
static ENABLED: AtomicBool = AtomicBool::new(false);

/// Enable allocation tracking. Called once at startup by vole-leak.
pub fn enable_tracking() {
    ENABLED.store(true, Ordering::Relaxed);
}

/// Record an allocation of the given runtime type.
#[inline]
pub fn track_alloc(type_id: u32) {
    if !ENABLED.load(Ordering::Relaxed) {
        return;
    }
    TOTAL.fetch_add(1, Ordering::Relaxed);
    if let Some(counter) = TYPE_COUNTERS.get(type_id as usize) {
        counter.fetch_add(1, Ordering::Relaxed);
    }
}

/// Record a deallocation of the given runtime type.
#[inline]
pub fn track_dealloc(type_id: u32) {
    if !ENABLED.load(Ordering::Relaxed) {
        return;
    }
    TOTAL.fetch_sub(1, Ordering::Relaxed);
    if let Some(counter) = TYPE_COUNTERS.get(type_id as usize) {
        counter.fetch_sub(1, Ordering::Relaxed);
    }
}

/// Snapshot the current total allocation count.
pub fn snapshot() -> i64 {
    TOTAL.load(Ordering::Relaxed)
}

/// Return the difference between the current total and a previous snapshot.
pub fn delta(snap: i64) -> i64 {
    TOTAL.load(Ordering::Relaxed) - snap
}

/// Return non-zero per-type counts as `(type_id, count)` pairs.
pub fn report() -> Vec<(u32, i64)> {
    let mut result = Vec::new();
    for (i, counter) in TYPE_COUNTERS.iter().enumerate() {
        let count = counter.load(Ordering::Relaxed);
        if count != 0 {
            result.push((i as u32, count));
        }
    }
    result
}

/// Return a human-readable name for a runtime type ID.
pub fn type_name(type_id: u32) -> &'static str {
    use crate::value::RuntimeTypeId;
    RuntimeTypeId::from_u32(type_id)
        .map(|id| id.name())
        .unwrap_or("Unknown")
}

/// Return the current count for a specific type ID.
pub fn count(type_id: u32) -> i64 {
    TYPE_COUNTERS
        .get(type_id as usize)
        .map(|c| c.load(Ordering::Relaxed))
        .unwrap_or(0)
}

/// Reset all counters to zero.
pub fn reset() {
    TOTAL.store(0, Ordering::Relaxed);
    for counter in &TYPE_COUNTERS {
        counter.store(0, Ordering::Relaxed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::RuntimeTypeId;
    use std::sync::Mutex;

    // These tests manipulate global state (ENABLED flag, counters, reset) and must
    // not run in parallel. A static mutex ensures mutual exclusion.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    /// Read a specific type counter.
    fn type_count(type_id: u32) -> i64 {
        TYPE_COUNTERS[type_id as usize].load(Ordering::Relaxed)
    }

    #[test]
    fn test_disabled_mode_does_not_count() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        // Temporarily disable to test the disabled path.
        let was_enabled = ENABLED.load(Ordering::Relaxed);
        ENABLED.store(false, Ordering::Relaxed);
        let before = type_count(RuntimeTypeId::Rng as u32);

        track_alloc(RuntimeTypeId::Rng as u32);
        // RNG counter should not have changed when disabled
        assert_eq!(type_count(RuntimeTypeId::Rng as u32), before);

        // Restore previous state
        ENABLED.store(was_enabled, Ordering::Relaxed);
    }

    #[test]
    fn test_enable_tracking() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        assert!(ENABLED.load(Ordering::Relaxed));
    }

    #[test]
    fn test_track_alloc_increments_type_counter() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        let before = type_count(RuntimeTypeId::Iterator as u32);

        track_alloc(RuntimeTypeId::Iterator as u32);
        assert_eq!(type_count(RuntimeTypeId::Iterator as u32), before + 1);

        track_alloc(RuntimeTypeId::Iterator as u32);
        assert_eq!(type_count(RuntimeTypeId::Iterator as u32), before + 2);

        // Clean up
        track_dealloc(RuntimeTypeId::Iterator as u32);
        track_dealloc(RuntimeTypeId::Iterator as u32);
    }

    #[test]
    fn test_track_dealloc_decrements_type_counter() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        let before = type_count(RuntimeTypeId::Rng as u32);

        track_alloc(RuntimeTypeId::Rng as u32);
        track_alloc(RuntimeTypeId::Rng as u32);
        assert_eq!(type_count(RuntimeTypeId::Rng as u32), before + 2);

        track_dealloc(RuntimeTypeId::Rng as u32);
        assert_eq!(type_count(RuntimeTypeId::Rng as u32), before + 1);

        track_dealloc(RuntimeTypeId::Rng as u32);
        assert_eq!(type_count(RuntimeTypeId::Rng as u32), before);
    }

    #[test]
    fn test_snapshot_and_delta_on_type_counter() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        let before = type_count(RuntimeTypeId::Closure as u32);

        track_alloc(RuntimeTypeId::Closure as u32);
        track_alloc(RuntimeTypeId::Closure as u32);
        assert_eq!(type_count(RuntimeTypeId::Closure as u32), before + 2);

        track_dealloc(RuntimeTypeId::Closure as u32);
        assert_eq!(type_count(RuntimeTypeId::Closure as u32), before + 1);

        // Clean up
        track_dealloc(RuntimeTypeId::Closure as u32);
    }

    #[test]
    fn test_report_includes_tracked_types() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        let before = type_count(RuntimeTypeId::Iterator as u32);

        track_alloc(RuntimeTypeId::Iterator as u32);
        track_alloc(RuntimeTypeId::Iterator as u32);

        let r = report();
        let iter_count = TYPE_COUNTERS[RuntimeTypeId::Iterator as usize].load(Ordering::Relaxed);
        assert_eq!(iter_count - before, 2);
        assert!(
            r.iter()
                .any(|&(id, _)| id == RuntimeTypeId::Iterator as u32)
        );

        // Clean up
        track_dealloc(RuntimeTypeId::Iterator as u32);
        track_dealloc(RuntimeTypeId::Iterator as u32);
    }

    #[test]
    fn test_reset_zeros_type_counters() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();

        track_alloc(RuntimeTypeId::Rng as u32);
        assert!(type_count(RuntimeTypeId::Rng as u32) >= 1);

        reset();
        // After reset, individual type counters should be zero
        assert_eq!(type_count(RuntimeTypeId::Rng as u32), 0);
        assert_eq!(type_count(RuntimeTypeId::Iterator as u32), 0);
    }

    #[test]
    fn test_negative_on_double_free() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();
        let before = type_count(RuntimeTypeId::Iterator as u32);

        track_alloc(RuntimeTypeId::Iterator as u32);
        track_dealloc(RuntimeTypeId::Iterator as u32);
        track_dealloc(RuntimeTypeId::Iterator as u32); // double free
        assert_eq!(type_count(RuntimeTypeId::Iterator as u32), before - 1);

        // Clean up (add one back)
        track_alloc(RuntimeTypeId::Iterator as u32);
    }

    #[test]
    fn test_all_type_ids_tracked() {
        let _guard = TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        enable_tracking();

        let types = [
            RuntimeTypeId::String as u32,
            RuntimeTypeId::Array as u32,
            RuntimeTypeId::Closure as u32,
            RuntimeTypeId::Instance as u32,
            RuntimeTypeId::Rng as u32,
            RuntimeTypeId::Iterator as u32,
            RuntimeTypeId::Wide128 as u32,
        ];

        let before: Vec<i64> = types.iter().map(|&t| type_count(t)).collect();

        for &t in &types {
            track_alloc(t);
        }

        // Verify each per-type counter increased by exactly 1
        for (i, &t) in types.iter().enumerate() {
            assert_eq!(
                type_count(t) - before[i],
                1,
                "type {} should have incremented by 1",
                t
            );
        }

        // Clean up
        for &t in &types {
            track_dealloc(t);
        }
    }
}

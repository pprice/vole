// value.rs

use std::sync::atomic::{AtomicU32, Ordering};

/// Reference counting header for heap-allocated objects
///
/// Layout: [ref_count: u32] [type_id: u32] [drop_fn: Option<fn(*mut u8)>]
/// Total size: 16 bytes (4 + 4 + 8)
#[repr(C)]
pub struct RcHeader {
    pub ref_count: AtomicU32,
    pub type_id: u32,
    pub drop_fn: Option<unsafe extern "C" fn(*mut u8)>,
}

impl RcHeader {
    pub fn new(type_id: u32) -> Self {
        Self {
            ref_count: AtomicU32::new(1),
            type_id,
            drop_fn: None,
        }
    }

    pub fn with_drop_fn(type_id: u32, drop_fn: unsafe extern "C" fn(*mut u8)) -> Self {
        Self {
            ref_count: AtomicU32::new(1),
            type_id,
            drop_fn: Some(drop_fn),
        }
    }

    #[inline]
    pub fn inc(&self) {
        // Relaxed is correct here for the same reason Arc::clone uses Relaxed:
        // we already hold a live reference, so the count cannot reach zero while
        // we increment. The existing reference guarantees visibility of the
        // object's data. The critical ordering is on dec, which uses AcqRel to
        // ensure all modifications are visible before the final drop.
        self.ref_count.fetch_add(1, Ordering::Relaxed);
    }

    #[inline]
    pub fn dec(&self) -> u32 {
        self.ref_count.fetch_sub(1, Ordering::AcqRel)
    }
}

/// Increment the reference count of an RC-managed object.
///
/// # Safety
/// `ptr` must be null or point to a valid allocation starting with an `RcHeader`.
#[unsafe(no_mangle)]
pub extern "C" fn rc_inc(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        let header = &*(ptr as *const RcHeader);
        // Relaxed is fine for the pinned check: RC_PINNED is a permanent
        // sentinel that never transitions to or from any other value, so no
        // synchronization is needed to observe it correctly.
        if header.ref_count.load(Ordering::Relaxed) == RC_PINNED {
            return;
        }
        header.inc();
    }
}

/// Decrement the reference count of an RC-managed object.
/// If the count reaches zero, calls the `drop_fn` if one was set.
///
/// # Safety
/// `ptr` must be null or point to a valid allocation starting with an `RcHeader`.
#[unsafe(no_mangle)]
pub extern "C" fn rc_dec(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        let header = &*(ptr as *const RcHeader);
        // Relaxed is fine for the pinned check: see comment in rc_inc.
        if header.ref_count.load(Ordering::Relaxed) == RC_PINNED {
            return;
        }
        let prev = header.dec();
        if prev == 1 {
            // Refcount was 1, now 0 — time to drop
            let drop_fn = (*ptr.cast::<RcHeader>()).drop_fn;
            if let Some(f) = drop_fn {
                f(ptr);
            }
            // If drop_fn is None, the object has no type-specific cleanup.
        }
    }
}

/// Sentinel refcount for static/pinned objects — rc_inc/rc_dec are no-ops.
pub const RC_PINNED: u32 = u32::MAX;

/// Type IDs for runtime objects
pub const TYPE_STRING: u32 = 1;
pub const TYPE_I64: u32 = 2;
pub const TYPE_F64: u32 = 3;
pub const TYPE_BOOL: u32 = 4;
pub const TYPE_ARRAY: u32 = 5;
pub const TYPE_CLOSURE: u32 = 6;
pub const TYPE_INSTANCE: u32 = 7;
pub const TYPE_RNG: u32 = 8;
pub const TYPE_ITERATOR: u32 = 11;
/// Heap-allocated union buffer: `[tag: i8, is_rc: i8, pad(6), payload: i64]`.
/// Not RC-managed itself (no RcHeader), but may contain an RC payload.
/// When cleaned up: if `is_rc` byte (offset 1) is non-zero, `rc_dec` the payload
/// at offset 8, then free the 16-byte buffer.
pub const TYPE_UNION_HEAP: u32 = 12;

/// Check if a type tag represents an RC-managed (heap-allocated) type.
/// These types need rc_inc/rc_dec when ownership changes.
#[inline]
pub fn tag_needs_rc(tag: u64) -> bool {
    matches!(
        tag as u32,
        TYPE_STRING | TYPE_ARRAY | TYPE_CLOSURE | TYPE_INSTANCE | TYPE_RNG | TYPE_ITERATOR
    )
}

/// Tagged value for boxed/heterogeneous storage
/// Used in arrays, union types, and fallible returns
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct TaggedValue {
    pub tag: u64,
    pub value: u64,
}

impl TaggedValue {
    pub fn from_i64(v: i64) -> Self {
        Self {
            tag: TYPE_I64 as u64,
            value: v as u64,
        }
    }

    pub fn from_f64(v: f64) -> Self {
        Self {
            tag: TYPE_F64 as u64,
            value: v.to_bits(),
        }
    }

    pub fn from_bool(v: bool) -> Self {
        Self {
            tag: TYPE_BOOL as u64,
            value: v as u64,
        }
    }

    pub fn from_string(ptr: *mut crate::string::RcString) -> Self {
        Self {
            tag: TYPE_STRING as u64,
            value: ptr as u64,
        }
    }

    pub fn as_i64(&self) -> i64 {
        self.value as i64
    }

    pub fn as_f64(&self) -> f64 {
        f64::from_bits(self.value)
    }

    pub fn as_bool(&self) -> bool {
        self.value != 0
    }

    /// Check if this tagged value holds an RC-managed type.
    #[inline]
    pub fn needs_rc(&self) -> bool {
        tag_needs_rc(self.tag)
    }

    /// If this tagged value holds an RC type, decrement its reference count.
    /// Also handles union heap buffers: frees the buffer and conditionally
    /// rc_dec's the payload if the is_rc flag is set.
    #[inline]
    pub fn rc_dec_if_needed(&self) {
        if self.value == 0 {
            return;
        }
        if self.needs_rc() {
            rc_dec(self.value as *mut u8);
        } else if self.tag == TYPE_UNION_HEAP as u64 {
            union_heap_cleanup(self.value as *mut u8);
        }
    }

    /// If this tagged value holds an RC type, increment its reference count.
    #[inline]
    pub fn rc_inc_if_needed(&self) {
        if self.needs_rc() && self.value != 0 {
            rc_inc(self.value as *mut u8);
        }
    }
}

/// Clean up a heap-allocated union buffer.
///
/// Union heap buffer layout: `[tag: i8, is_rc: i8, pad(6), payload: i64]` = 16 bytes.
/// If `is_rc` (byte at offset 1) is non-zero, the payload at offset 8 is an RC pointer
/// that needs `rc_dec`. After handling the payload, the 16-byte buffer is freed.
///
/// # Safety
/// `ptr` must point to a valid union heap buffer allocated by `vole_heap_alloc(16)`.
pub fn union_heap_cleanup(ptr: *mut u8) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        let is_rc = *ptr.add(1);
        let payload = *(ptr.add(8) as *const u64);
        if is_rc != 0 && payload != 0 {
            rc_dec(payload as *mut u8);
        }
        // Free the 16-byte heap buffer
        const UNION_HEAP_LAYOUT: std::alloc::Layout =
            match std::alloc::Layout::from_size_align(16, 8) {
                Ok(l) => l,
                Err(_) => panic!("union heap layout"),
            };
        std::alloc::dealloc(ptr, UNION_HEAP_LAYOUT);
    }
}

/// Decrement refcount of an i64 value if it represents an RC pointer.
/// Used by collections that store raw i64 values and know their element types are RC.
#[inline]
pub fn rc_dec_raw(value: i64) {
    let ptr = value as *mut u8;
    if !ptr.is_null() {
        rc_dec(ptr);
    }
}

/// Increment refcount of an i64 value if it represents an RC pointer.
/// Used by collections that store raw i64 values and know their element types are RC.
#[inline]
pub fn rc_inc_raw(value: i64) {
    let ptr = value as *mut u8;
    if !ptr.is_null() {
        rc_inc(ptr);
    }
}

/// Runtime context passed to native functions
pub struct Context {
    // Placeholder for future allocator, GC roots, etc.
}

impl Context {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{Layout, alloc, dealloc};
    use std::sync::atomic::AtomicBool;

    #[test]
    fn rc_header_inc_dec() {
        let header = RcHeader::new(TYPE_STRING);
        assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);

        header.inc();
        assert_eq!(header.ref_count.load(Ordering::Relaxed), 2);

        let prev = header.dec();
        assert_eq!(prev, 2);
        assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn rc_header_layout_is_16_bytes() {
        assert_eq!(size_of::<RcHeader>(), 16);
        assert_eq!(align_of::<RcHeader>(), 8);
    }

    #[test]
    fn rc_header_with_drop_fn() {
        let header = RcHeader::with_drop_fn(TYPE_STRING, dummy_drop);
        assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);
        assert!(header.drop_fn.is_some());

        let header_none = RcHeader::new(TYPE_STRING);
        assert!(header_none.drop_fn.is_none());
    }

    #[test]
    fn rc_header_new_has_none_drop_fn() {
        let header = RcHeader::new(TYPE_ARRAY);
        assert!(header.drop_fn.is_none());
        assert_eq!(header.type_id, TYPE_ARRAY);
    }

    static DROP_CALLED: AtomicBool = AtomicBool::new(false);

    unsafe extern "C" fn dummy_drop(_ptr: *mut u8) {
        DROP_CALLED.store(true, Ordering::SeqCst);
    }

    /// Allocate an RcHeader on the heap so rc_inc/rc_dec can operate on it
    /// the same way they will in real usage (via raw pointer).
    unsafe fn alloc_rc_header(drop_fn: Option<unsafe extern "C" fn(*mut u8)>) -> *mut u8 {
        let layout = Layout::new::<RcHeader>();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null());
        let header = RcHeader {
            ref_count: AtomicU32::new(1),
            type_id: TYPE_STRING,
            drop_fn,
        };
        unsafe { std::ptr::write(ptr as *mut RcHeader, header) };
        ptr
    }

    #[test]
    fn rc_inc_dec_extern_c_basic() {
        unsafe {
            let ptr = alloc_rc_header(None);

            rc_inc(ptr);
            let header = &*(ptr as *const RcHeader);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 2);

            rc_dec(ptr);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), 1);

            // Final dec with no drop_fn — should not crash
            rc_dec(ptr);
            // Memory is now logically freed; don't access it
        }
    }

    #[test]
    fn rc_dec_calls_drop_fn_at_zero() {
        DROP_CALLED.store(false, Ordering::SeqCst);

        // We need a custom drop_fn that also deallocates, since rc_dec
        // delegates deallocation to the drop_fn.
        unsafe extern "C" fn test_drop(ptr: *mut u8) {
            DROP_CALLED.store(true, Ordering::SeqCst);
            let layout = Layout::new::<RcHeader>();
            unsafe { dealloc(ptr, layout) };
        }

        unsafe {
            let ptr = alloc_rc_header(Some(test_drop));

            rc_inc(ptr);
            assert_eq!(DROP_CALLED.load(Ordering::SeqCst), false);

            rc_dec(ptr);
            assert_eq!(DROP_CALLED.load(Ordering::SeqCst), false);

            rc_dec(ptr);
            assert_eq!(DROP_CALLED.load(Ordering::SeqCst), true);
        }
    }

    #[test]
    fn rc_inc_dec_null_is_noop() {
        // Should not crash
        rc_inc(std::ptr::null_mut());
        rc_dec(std::ptr::null_mut());
    }

    /// Allocate a pinned RcHeader (ref_count = RC_PINNED) on the heap.
    unsafe fn alloc_pinned_header(drop_fn: Option<unsafe extern "C" fn(*mut u8)>) -> *mut u8 {
        let layout = Layout::new::<RcHeader>();
        let ptr = unsafe { alloc(layout) };
        assert!(!ptr.is_null());
        let header = RcHeader {
            ref_count: AtomicU32::new(RC_PINNED),
            type_id: TYPE_STRING,
            drop_fn,
        };
        unsafe { std::ptr::write(ptr as *mut RcHeader, header) };
        ptr
    }

    #[test]
    fn rc_inc_is_noop_for_pinned() {
        unsafe {
            let ptr = alloc_pinned_header(None);
            rc_inc(ptr);
            let header = &*(ptr as *const RcHeader);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), RC_PINNED);
            dealloc(ptr, Layout::new::<RcHeader>());
        }
    }

    #[test]
    fn rc_dec_is_noop_for_pinned() {
        DROP_CALLED.store(false, Ordering::SeqCst);
        unsafe {
            let ptr = alloc_pinned_header(Some(dummy_drop));
            rc_dec(ptr);
            let header = &*(ptr as *const RcHeader);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), RC_PINNED);
            assert!(!DROP_CALLED.load(Ordering::SeqCst));
            dealloc(ptr, Layout::new::<RcHeader>());
        }
    }

    #[test]
    fn rc_inc_dec_repeated_on_pinned() {
        DROP_CALLED.store(false, Ordering::SeqCst);
        unsafe {
            let ptr = alloc_pinned_header(Some(dummy_drop));
            for _ in 0..10 {
                rc_inc(ptr);
                rc_dec(ptr);
            }
            let header = &*(ptr as *const RcHeader);
            assert_eq!(header.ref_count.load(Ordering::Relaxed), RC_PINNED);
            assert!(!DROP_CALLED.load(Ordering::SeqCst));
            dealloc(ptr, Layout::new::<RcHeader>());
        }
    }
}

// src/runtime/value.rs

use std::sync::atomic::{AtomicU32, Ordering};

/// Reference counting header for heap-allocated objects
#[repr(C)]
pub struct RcHeader {
    pub ref_count: AtomicU32,
    pub type_id: u32,
}

impl RcHeader {
    pub fn new(type_id: u32) -> Self {
        Self {
            ref_count: AtomicU32::new(1),
            type_id,
        }
    }

    pub fn inc(&self) {
        self.ref_count.fetch_add(1, Ordering::Relaxed);
    }

    pub fn dec(&self) -> u32 {
        self.ref_count.fetch_sub(1, Ordering::AcqRel)
    }
}

/// Type IDs for runtime objects
pub const TYPE_STRING: u32 = 1;

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
}

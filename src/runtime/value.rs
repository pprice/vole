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
pub const TYPE_I64: u32 = 2;
pub const TYPE_F64: u32 = 3;
pub const TYPE_BOOL: u32 = 4;
pub const TYPE_ARRAY: u32 = 5;
pub const TYPE_CLOSURE: u32 = 6;
pub const TYPE_INSTANCE: u32 = 7;

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

    pub fn from_string(ptr: *mut crate::runtime::string::RcString) -> Self {
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

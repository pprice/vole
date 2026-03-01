// vir_type_id.rs
//
// VirTypeId: post-monomorphization type handle for VIR nodes.

use std::fmt;

/// Concrete type identity in the VIR type table.
///
/// Unlike `TypeId` (which indexes into sema's `TypeArena`), `VirTypeId` indexes
/// into the post-monomorphization `VirTypeTable`.  All generic parameters have
/// been substituted, so every VirTypeId refers to a fully concrete type.
///
/// Reserved constants mirror the primitive slots in `TypeId` so that codegen can
/// match on well-known types without a table lookup.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct VirTypeId(u32);

impl VirTypeId {
    // ========================================================================
    // Reserved VirTypeIds for primitives and special types
    // Indices intentionally mirror TypeId so conversion is trivial.
    // ========================================================================

    /// Invalid / uninitialized placeholder (must be 0 for `is_invalid()` check).
    pub const INVALID: VirTypeId = VirTypeId(0);

    // Signed integers
    pub const I8: VirTypeId = VirTypeId(1);
    pub const I16: VirTypeId = VirTypeId(2);
    pub const I32: VirTypeId = VirTypeId(3);
    pub const I64: VirTypeId = VirTypeId(4);
    pub const I128: VirTypeId = VirTypeId(5);

    // Unsigned integers
    pub const U8: VirTypeId = VirTypeId(6);
    pub const U16: VirTypeId = VirTypeId(7);
    pub const U32: VirTypeId = VirTypeId(8);
    pub const U64: VirTypeId = VirTypeId(9);

    // Floating point
    pub const F32: VirTypeId = VirTypeId(10);
    pub const F64: VirTypeId = VirTypeId(11);
    pub const F128: VirTypeId = VirTypeId(12);

    // Other primitives
    pub const BOOL: VirTypeId = VirTypeId(13);
    pub const STRING: VirTypeId = VirTypeId(14);

    // Opaque handle type
    pub const HANDLE: VirTypeId = VirTypeId(15);

    // Special types
    pub const VOID: VirTypeId = VirTypeId(16);
    pub const NIL: VirTypeId = VirTypeId(17);
    pub const DONE: VirTypeId = VirTypeId(18);
    pub const RANGE: VirTypeId = VirTypeId(19);
    pub const METATYPE: VirTypeId = VirTypeId(20);

    // Top and bottom types
    pub const NEVER: VirTypeId = VirTypeId(21);
    pub const UNKNOWN: VirTypeId = VirTypeId(22);

    /// First non-reserved index (for dynamic / user-defined types).
    pub const FIRST_DYNAMIC: u32 = 23;

    /// High-bit flag for compat_ty-encoded VirTypeIds.
    ///
    /// During VIR lowering, types that `translate_type_id()` cannot resolve
    /// are encoded by `compat_ty()` as `VirTypeId(type_id.raw() | COMPAT_FLAG)`.
    /// This separates them from real VirTypeTable indices so the post-lowering
    /// sweep can safely grow the table via `intern()` without collisions.
    pub const COMPAT_FLAG: u32 = 0x8000_0000;

    /// Create a VirTypeId from a raw u32 index.
    pub fn from_raw(index: u32) -> Self {
        VirTypeId(index)
    }

    /// Get the underlying u32 index.
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Check if this is the invalid placeholder.
    #[inline]
    pub fn is_invalid(self) -> bool {
        self == Self::INVALID
    }

    /// Check if this VirTypeId was produced by `compat_ty()` (raw TypeId encoding).
    #[inline]
    pub fn is_compat(self) -> bool {
        self.0 & Self::COMPAT_FLAG != 0
    }

    /// Strip the compat flag to recover the original TypeId raw value.
    /// Only valid when `is_compat()` returns true.
    #[inline]
    pub fn compat_raw(self) -> u32 {
        self.0 & !Self::COMPAT_FLAG
    }
}

impl fmt::Display for VirTypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::INVALID => write!(f, "VirType(INVALID)"),
            Self::I8 => write!(f, "VirType(i8)"),
            Self::I16 => write!(f, "VirType(i16)"),
            Self::I32 => write!(f, "VirType(i32)"),
            Self::I64 => write!(f, "VirType(i64)"),
            Self::I128 => write!(f, "VirType(i128)"),
            Self::U8 => write!(f, "VirType(u8)"),
            Self::U16 => write!(f, "VirType(u16)"),
            Self::U32 => write!(f, "VirType(u32)"),
            Self::U64 => write!(f, "VirType(u64)"),
            Self::F32 => write!(f, "VirType(f32)"),
            Self::F64 => write!(f, "VirType(f64)"),
            Self::F128 => write!(f, "VirType(f128)"),
            Self::BOOL => write!(f, "VirType(bool)"),
            Self::STRING => write!(f, "VirType(string)"),
            Self::HANDLE => write!(f, "VirType(handle)"),
            Self::VOID => write!(f, "VirType(void)"),
            Self::NIL => write!(f, "VirType(nil)"),
            Self::DONE => write!(f, "VirType(done)"),
            Self::RANGE => write!(f, "VirType(range)"),
            Self::METATYPE => write!(f, "VirType(metatype)"),
            Self::NEVER => write!(f, "VirType(never)"),
            Self::UNKNOWN => write!(f, "VirType(unknown)"),
            other => write!(f, "VirType(#{})", other.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_is_zero() {
        assert_eq!(VirTypeId::INVALID.raw(), 0);
        assert!(VirTypeId::INVALID.is_invalid());
    }

    #[test]
    fn from_raw_round_trips() {
        for i in 0..=VirTypeId::FIRST_DYNAMIC {
            assert_eq!(VirTypeId::from_raw(i).raw(), i);
        }
    }

    #[test]
    fn reserved_constants_mirror_type_id_indices() {
        // These must stay in sync with TypeId constants.
        assert_eq!(VirTypeId::I64.raw(), 4);
        assert_eq!(VirTypeId::STRING.raw(), 14);
        assert_eq!(VirTypeId::BOOL.raw(), 13);
        assert_eq!(VirTypeId::VOID.raw(), 16);
        assert_eq!(VirTypeId::NEVER.raw(), 21);
        assert_eq!(VirTypeId::FIRST_DYNAMIC, 23);
    }

    #[test]
    fn display_primitives() {
        assert_eq!(VirTypeId::I64.to_string(), "VirType(i64)");
        assert_eq!(VirTypeId::STRING.to_string(), "VirType(string)");
        assert_eq!(VirTypeId::INVALID.to_string(), "VirType(INVALID)");
    }

    #[test]
    fn display_dynamic() {
        assert_eq!(VirTypeId::from_raw(42).to_string(), "VirType(#42)");
    }

    #[test]
    fn non_invalid_is_not_invalid() {
        assert!(!VirTypeId::I64.is_invalid());
        assert!(!VirTypeId::from_raw(100).is_invalid());
    }
}

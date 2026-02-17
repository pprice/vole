// type_arena/type_id.rs
//
// TypeId: interned type handle with reserved constants for primitives.

use smallvec::SmallVec;

/// Concrete type identity in the TypeArena.
///
/// Unlike `TypeDefId` (which identifies a type *definition* like `class Option<T>`),
/// `TypeId` identifies a concrete instantiated type (like `Option<i32>`).
///
/// - Primitives, arrays, unions: have TypeId, no TypeDefId
/// - Classes, structs, interfaces: have both (TypeId contains TypeDefId + type_args)
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct TypeId(u32);

impl TypeId {
    // ========================================================================
    // Reserved TypeIds for primitives and special types
    // These are guaranteed to be interned at these indices by TypeArena::new()
    // ========================================================================

    // Invalid type (must be 0 for is_invalid() check)
    pub const INVALID: TypeId = TypeId(0);

    // Signed integers
    pub const I8: TypeId = TypeId(1);
    pub const I16: TypeId = TypeId(2);
    pub const I32: TypeId = TypeId(3);
    pub const I64: TypeId = TypeId(4);
    pub const I128: TypeId = TypeId(5);

    // Unsigned integers
    pub const U8: TypeId = TypeId(6);
    pub const U16: TypeId = TypeId(7);
    pub const U32: TypeId = TypeId(8);
    pub const U64: TypeId = TypeId(9);

    // Floating point
    pub const F32: TypeId = TypeId(10);
    pub const F64: TypeId = TypeId(11);
    pub const F128: TypeId = TypeId(12);

    // Other primitives
    pub const BOOL: TypeId = TypeId(13);
    pub const STRING: TypeId = TypeId(14);

    // Opaque handle type
    pub const HANDLE: TypeId = TypeId(15);

    // Special types
    pub const VOID: TypeId = TypeId(16);
    pub const NIL: TypeId = TypeId(17);
    pub const DONE: TypeId = TypeId(18);
    pub const RANGE: TypeId = TypeId(19);
    pub const METATYPE: TypeId = TypeId(20);

    // Top and bottom types
    pub const NEVER: TypeId = TypeId(21);
    pub const UNKNOWN: TypeId = TypeId(22);

    /// First non-reserved TypeId index (for dynamic types)
    pub const FIRST_DYNAMIC: u32 = 23;

    /// Get the raw index (for debugging/serialization)
    pub fn index(self) -> u32 {
        self.0
    }

    /// Create a TypeId from a raw index (for internal use by TypeArena)
    pub(super) fn from_raw(index: u32) -> Self {
        TypeId(index)
    }

    /// Get the raw u32 value (for internal use by TypeArena)
    pub(super) fn raw(self) -> u32 {
        self.0
    }

    /// Check if this is the invalid type (no arena needed)
    #[inline]
    pub fn is_invalid(self) -> bool {
        self == Self::INVALID
    }

    /// Check if this is nil (no arena needed)
    #[inline]
    pub fn is_nil(self) -> bool {
        self == Self::NIL
    }

    /// Check if this is void (no arena needed)
    #[inline]
    pub fn is_void(self) -> bool {
        self == Self::VOID
    }

    /// Check if this is the never type (no arena needed)
    #[inline]
    pub fn is_never(self) -> bool {
        self == Self::NEVER
    }

    /// Check if this is the unknown type (no arena needed)
    #[inline]
    pub fn is_unknown(self) -> bool {
        self == Self::UNKNOWN
    }

    /// Check if this is a signed integer type (no arena needed)
    #[inline]
    pub fn is_signed_int(self) -> bool {
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128
        )
    }

    /// Check if this is an unsigned integer type (no arena needed)
    #[inline]
    pub fn is_unsigned_int(self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    /// Check if this is any integer type (no arena needed)
    #[inline]
    pub fn is_integer(self) -> bool {
        self.is_signed_int() || self.is_unsigned_int()
    }

    /// Check if this is the bool type (no arena needed)
    #[inline]
    pub fn is_bool(self) -> bool {
        self == Self::BOOL
    }

    /// Check if this is a floating point type (no arena needed)
    #[inline]
    pub fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64 | Self::F128)
    }

    /// Check if this is a numeric type (no arena needed)
    #[inline]
    pub fn is_numeric(self) -> bool {
        self.is_integer() || self.is_float()
    }

    /// Check if this is a primitive type (no arena needed)
    #[inline]
    pub fn is_primitive(self) -> bool {
        // Primitives are indices 1-14 (i8 through string)
        self.0 >= Self::I8.0 && self.0 <= Self::STRING.0
    }

    /// Check if an integer literal value fits within this type's range (primitives only).
    /// For unions, use TypeArena::literal_fits_id instead.
    #[inline]
    pub fn fits_literal(self, value: i64) -> bool {
        match self {
            Self::I8 => value >= i8::MIN as i64 && value <= i8::MAX as i64,
            Self::I16 => value >= i16::MIN as i64 && value <= i16::MAX as i64,
            Self::I32 => value >= i32::MIN as i64 && value <= i32::MAX as i64,
            Self::I64 => true,
            Self::I128 => true, // i64 always fits in i128
            Self::U8 => value >= 0 && value <= u8::MAX as i64,
            Self::U16 => value >= 0 && value <= u16::MAX as i64,
            Self::U32 => value >= 0 && value <= u32::MAX as i64,
            Self::U64 => value >= 0,       // i64 positive values fit
            Self::F32 | Self::F64 | Self::F128 => true, // Integers can become floats
            _ => false,
        }
    }

    /// Get the bit width of this integer type (no arena needed).
    /// Returns u16::MAX for non-integer types (so they sort last).
    #[inline]
    pub fn integer_bit_width(self) -> u16 {
        match self {
            Self::I8 | Self::U8 => 8,
            Self::I16 | Self::U16 => 16,
            Self::I32 | Self::U32 => 32,
            Self::I64 | Self::U64 => 64,
            Self::I128 => 128,
            _ => u16::MAX,
        }
    }
}

/// SmallVec for type children - inline up to 4 (covers most unions, tuples, params)
pub type TypeIdVec = SmallVec<[TypeId; 4]>;

/// Nominal type kind for Class/Struct/Interface/Error discrimination
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NominalKind {
    Class,
    Struct,
    Interface,
    Error,
}

impl NominalKind {
    /// Convert to the corresponding TypeDefKind.
    pub fn to_type_def_kind(self) -> crate::entity_defs::TypeDefKind {
        use crate::entity_defs::TypeDefKind;
        match self {
            NominalKind::Class => TypeDefKind::Class,
            NominalKind::Struct => TypeDefKind::Struct,
            NominalKind::Interface => TypeDefKind::Interface,
            NominalKind::Error => TypeDefKind::ErrorType,
        }
    }

    /// Check if this is a class or struct (types with fields).
    pub fn is_class_or_struct(self) -> bool {
        matches!(self, NominalKind::Class | NominalKind::Struct)
    }
}

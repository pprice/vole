// src/sema/type_arena.rs
//
// Interned type system using TypeId handles for O(1) equality and minimal allocations.
//
// This module provides the canonical type representation for Vole's semantic analysis:
// - TypeId: u32 handle to an interned type (Copy, trivial Eq/Hash)
// - TypeArena: per-compilation storage with automatic deduplication
// - SemaType: the canonical type representation using TypeId for child types

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::types::{ConstantValue, PlaceholderKind, PrimitiveType};
use vole_identity::{ModuleId, NameId, TypeDefId, TypeParamId};

/// Concrete type identity in the TypeArena.
///
/// Unlike `TypeDefId` (which identifies a type *definition* like `class Option<T>`),
/// `TypeId` identifies a concrete instantiated type (like `Option<i32>`).
///
/// - Primitives, arrays, unions: have TypeId, no TypeDefId
/// - Classes, records, interfaces: have both (TypeId contains TypeDefId + type_args)
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

    // Other primitives
    pub const BOOL: TypeId = TypeId(12);
    pub const STRING: TypeId = TypeId(13);

    // Special types
    pub const VOID: TypeId = TypeId(14);
    pub const NIL: TypeId = TypeId(15);
    pub const DONE: TypeId = TypeId(16);
    pub const RANGE: TypeId = TypeId(17);
    pub const METATYPE: TypeId = TypeId(18);

    // Top and bottom types
    pub const NEVER: TypeId = TypeId(19);
    pub const UNKNOWN: TypeId = TypeId(20);

    /// First non-reserved TypeId index (for dynamic types)
    pub const FIRST_DYNAMIC: u32 = 21;

    /// Get the raw index (for debugging/serialization)
    pub fn index(self) -> u32 {
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

    /// Check if this is a floating point type (no arena needed)
    #[inline]
    pub fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    /// Check if this is a numeric type (no arena needed)
    #[inline]
    pub fn is_numeric(self) -> bool {
        self.is_integer() || self.is_float()
    }

    /// Check if this is a primitive type (no arena needed)
    #[inline]
    pub fn is_primitive(self) -> bool {
        // Primitives are indices 1-13 (i8 through string)
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
            Self::F32 | Self::F64 => true, // Integers can become floats
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

/// Nominal type kind for Class/Record/Interface/Error discrimination
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NominalKind {
    Class,
    Record,
    Interface,
    Error,
}

impl NominalKind {
    /// Convert to the corresponding TypeDefKind.
    pub fn to_type_def_kind(self) -> crate::entity_defs::TypeDefKind {
        use crate::entity_defs::TypeDefKind;
        match self {
            NominalKind::Class => TypeDefKind::Class,
            NominalKind::Record => TypeDefKind::Record,
            NominalKind::Interface => TypeDefKind::Interface,
            NominalKind::Error => TypeDefKind::ErrorType,
        }
    }

    /// Check if this is a class or record (types with fields).
    pub fn is_class_or_record(self) -> bool {
        matches!(self, NominalKind::Class | NominalKind::Record)
    }
}

/// Interned representation of a structural method
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedStructuralMethod {
    pub name: NameId,
    pub params: TypeIdVec,
    pub return_type: TypeId,
}

/// Interned representation of a structural type (duck typing constraint)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedStructural {
    pub fields: SmallVec<[(NameId, TypeId); 4]>,
    pub methods: SmallVec<[InternedStructuralMethod; 2]>,
}

/// Interned representation of a module type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedModule {
    pub module_id: ModuleId,
    /// Exports as (name, type) pairs - part of the module's type signature
    pub exports: SmallVec<[(NameId, TypeId); 8]>,
}

/// Module metadata stored separately from the type.
///
/// This contains codegen-relevant data that isn't part of the module's type identity.
/// The type identity is just (module_id, exports) - this is the "extra" data.
///
/// FUTURE OPTIMIZATION:
/// - `constants`: Can be eliminated with constant folding during analysis.
///   Instead of storing constant values here, fold them directly into the AST.
/// - `external_funcs`: Can be eliminated by treating external funcs as regular funcs.
///   The "external" distinction is a codegen detail, not a type system concept.
#[derive(Debug, Clone, Default)]
pub struct ModuleMetadata {
    /// Compile-time constant values (e.g., math.PI = 3.14159...)
    pub constants: FxHashMap<NameId, ConstantValue>,
    /// Functions implemented via FFI rather than Vole code
    pub external_funcs: FxHashSet<NameId>,
}

/// The canonical type representation in Vole.
///
/// This is an interned type stored in the TypeArena. Use TypeId handles
/// for O(1) equality and pass-by-copy. Access the SemaType via arena.get(id).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SemaType {
    // Primitives
    Primitive(PrimitiveType),

    // Special types
    Void,
    Nil,
    Done,
    Range,
    MetaType, // metatype - the type of types

    // Top and bottom types
    Never, // Bottom type - the type of expressions that never return (e.g., unreachable, panic)
    Unknown, // Top type - the type that includes all values (used for inference/gradual typing)

    // Error/invalid type
    Invalid {
        kind: &'static str,
    },

    // Compound types with TypeId children
    Union(TypeIdVec),
    Tuple(TypeIdVec),
    Array(TypeId),
    FixedArray {
        element: TypeId,
        size: usize,
    },
    RuntimeIterator(TypeId),

    // Function type
    Function {
        params: TypeIdVec,
        ret: TypeId,
        is_closure: bool,
    },

    // Nominal types (class, record, interface, error)
    Class {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Record {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Interface {
        type_def_id: TypeDefId,
        type_args: TypeIdVec,
    },
    Error {
        type_def_id: TypeDefId,
    },

    // Type parameters
    TypeParam(NameId),
    TypeParamRef(TypeParamId),

    // Module type - exports are part of the type identity
    // Note: Boxed to keep SemaType size small
    Module(Box<InternedModule>),

    // Fallible type: fallible(T, E) - result-like type
    Fallible {
        success: TypeId,
        error: TypeId,
    },

    // Structural type: duck typing constraint
    // e.g., { name: string, func greet() -> string }
    // Note: Boxed to keep SemaType size small
    Structural(Box<InternedStructural>),

    // Placeholder for inference (if we decide to intern these)
    Placeholder(PlaceholderKind),
}

/// Pre-interned primitive and common types for O(1) access
#[derive(Debug, Clone, Copy)]
pub struct PrimitiveTypes {
    // Signed integers
    pub i8: TypeId,
    pub i16: TypeId,
    pub i32: TypeId,
    pub i64: TypeId,
    pub i128: TypeId,
    // Unsigned integers
    pub u8: TypeId,
    pub u16: TypeId,
    pub u32: TypeId,
    pub u64: TypeId,
    // Floating point
    pub f32: TypeId,
    pub f64: TypeId,
    // Other primitives
    pub bool: TypeId,
    pub string: TypeId,
    // Special types
    pub void: TypeId,
    pub nil: TypeId,
    pub done: TypeId,
    pub range: TypeId,
    pub metatype: TypeId,
    pub invalid: TypeId,
}

/// Per-compilation type arena with automatic interning/deduplication.
#[derive(Clone)]
pub struct TypeArena {
    /// Interned types, indexed by TypeId
    types: Vec<SemaType>,
    /// Deduplication map - FxHashMap for better perf with small keys
    intern_map: FxHashMap<SemaType, TypeId>,
    /// Pre-interned primitives for O(1) access
    pub primitives: PrimitiveTypes,
    /// Module metadata (constants, external_funcs) keyed by ModuleId.
    /// This data is not part of the type identity, but needed by codegen.
    module_metadata: FxHashMap<ModuleId, ModuleMetadata>,
}

impl std::fmt::Debug for TypeArena {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeArena")
            .field("types_count", &self.types.len())
            .finish_non_exhaustive()
    }
}

impl TypeArena {
    /// Create a new TypeArena with pre-interned primitive types
    pub fn new() -> Self {
        let mut arena = Self {
            types: Vec::new(),
            intern_map: FxHashMap::default(),
            module_metadata: FxHashMap::default(),
            primitives: PrimitiveTypes {
                // Temporary placeholders - will be filled in below
                i8: TypeId(0),
                i16: TypeId(0),
                i32: TypeId(0),
                i64: TypeId(0),
                i128: TypeId(0),
                u8: TypeId(0),
                u16: TypeId(0),
                u32: TypeId(0),
                u64: TypeId(0),
                f32: TypeId(0),
                f64: TypeId(0),
                bool: TypeId(0),
                string: TypeId(0),
                void: TypeId(0),
                nil: TypeId(0),
                done: TypeId(0),
                range: TypeId(0),
                metatype: TypeId(0),
                invalid: TypeId(0),
            },
        };

        // Pre-intern all primitive types in the order defined by TypeId constants.
        // The debug_asserts verify the constants match the actual interned indices.
        arena.primitives.invalid = arena.intern(SemaType::Invalid { kind: "invalid" });
        debug_assert_eq!(arena.primitives.invalid, TypeId::INVALID);

        arena.primitives.i8 = arena.intern(SemaType::Primitive(PrimitiveType::I8));
        debug_assert_eq!(arena.primitives.i8, TypeId::I8);
        arena.primitives.i16 = arena.intern(SemaType::Primitive(PrimitiveType::I16));
        debug_assert_eq!(arena.primitives.i16, TypeId::I16);
        arena.primitives.i32 = arena.intern(SemaType::Primitive(PrimitiveType::I32));
        debug_assert_eq!(arena.primitives.i32, TypeId::I32);
        arena.primitives.i64 = arena.intern(SemaType::Primitive(PrimitiveType::I64));
        debug_assert_eq!(arena.primitives.i64, TypeId::I64);
        arena.primitives.i128 = arena.intern(SemaType::Primitive(PrimitiveType::I128));
        debug_assert_eq!(arena.primitives.i128, TypeId::I128);

        arena.primitives.u8 = arena.intern(SemaType::Primitive(PrimitiveType::U8));
        debug_assert_eq!(arena.primitives.u8, TypeId::U8);
        arena.primitives.u16 = arena.intern(SemaType::Primitive(PrimitiveType::U16));
        debug_assert_eq!(arena.primitives.u16, TypeId::U16);
        arena.primitives.u32 = arena.intern(SemaType::Primitive(PrimitiveType::U32));
        debug_assert_eq!(arena.primitives.u32, TypeId::U32);
        arena.primitives.u64 = arena.intern(SemaType::Primitive(PrimitiveType::U64));
        debug_assert_eq!(arena.primitives.u64, TypeId::U64);

        arena.primitives.f32 = arena.intern(SemaType::Primitive(PrimitiveType::F32));
        debug_assert_eq!(arena.primitives.f32, TypeId::F32);
        arena.primitives.f64 = arena.intern(SemaType::Primitive(PrimitiveType::F64));
        debug_assert_eq!(arena.primitives.f64, TypeId::F64);

        arena.primitives.bool = arena.intern(SemaType::Primitive(PrimitiveType::Bool));
        debug_assert_eq!(arena.primitives.bool, TypeId::BOOL);
        arena.primitives.string = arena.intern(SemaType::Primitive(PrimitiveType::String));
        debug_assert_eq!(arena.primitives.string, TypeId::STRING);

        arena.primitives.void = arena.intern(SemaType::Void);
        debug_assert_eq!(arena.primitives.void, TypeId::VOID);
        arena.primitives.nil = arena.intern(SemaType::Nil);
        debug_assert_eq!(arena.primitives.nil, TypeId::NIL);
        arena.primitives.done = arena.intern(SemaType::Done);
        debug_assert_eq!(arena.primitives.done, TypeId::DONE);
        arena.primitives.range = arena.intern(SemaType::Range);
        debug_assert_eq!(arena.primitives.range, TypeId::RANGE);
        arena.primitives.metatype = arena.intern(SemaType::MetaType);
        debug_assert_eq!(arena.primitives.metatype, TypeId::METATYPE);

        // Top and bottom types
        let never = arena.intern(SemaType::Never);
        debug_assert_eq!(never, TypeId::NEVER);
        let unknown = arena.intern(SemaType::Unknown);
        debug_assert_eq!(unknown, TypeId::UNKNOWN);

        arena
    }

    /// Intern a type, returning existing TypeId if already interned
    fn intern(&mut self, ty: SemaType) -> TypeId {
        let next_id = TypeId(self.types.len() as u32);
        *self.intern_map.entry(ty.clone()).or_insert_with(|| {
            self.types.push(ty);
            next_id
        })
    }

    /// Get the SemaType for a TypeId
    pub fn get(&self, id: TypeId) -> &SemaType {
        &self.types[id.0 as usize]
    }

    /// Check if a TypeId is the invalid type
    #[inline]
    pub fn is_invalid(&self, id: TypeId) -> bool {
        id == TypeId::INVALID
    }

    /// Check if a TypeId represents a SelfType placeholder (used in interface signatures)
    #[inline]
    pub fn is_self_type(&self, id: TypeId) -> bool {
        matches!(
            self.get(id),
            SemaType::Placeholder(PlaceholderKind::SelfType)
        )
    }

    // ========================================================================
    // Primitive accessors - O(1) lookup from pre-cached table
    // ========================================================================

    pub fn i8(&self) -> TypeId {
        self.primitives.i8
    }
    pub fn i16(&self) -> TypeId {
        self.primitives.i16
    }
    pub fn i32(&self) -> TypeId {
        self.primitives.i32
    }
    pub fn i64(&self) -> TypeId {
        self.primitives.i64
    }
    pub fn i128(&self) -> TypeId {
        self.primitives.i128
    }
    pub fn u8(&self) -> TypeId {
        self.primitives.u8
    }
    pub fn u16(&self) -> TypeId {
        self.primitives.u16
    }
    pub fn u32(&self) -> TypeId {
        self.primitives.u32
    }
    pub fn u64(&self) -> TypeId {
        self.primitives.u64
    }
    pub fn f32(&self) -> TypeId {
        self.primitives.f32
    }
    pub fn f64(&self) -> TypeId {
        self.primitives.f64
    }
    pub fn bool(&self) -> TypeId {
        self.primitives.bool
    }
    pub fn string(&self) -> TypeId {
        self.primitives.string
    }
    pub fn void(&self) -> TypeId {
        self.primitives.void
    }
    pub fn nil(&self) -> TypeId {
        self.primitives.nil
    }
    pub fn done(&self) -> TypeId {
        self.primitives.done
    }
    pub fn range(&self) -> TypeId {
        self.primitives.range
    }
    pub fn metatype(&self) -> TypeId {
        self.primitives.metatype
    }
    pub fn invalid(&self) -> TypeId {
        self.primitives.invalid
    }
    pub fn never(&self) -> TypeId {
        TypeId::NEVER
    }
    pub fn unknown(&self) -> TypeId {
        TypeId::UNKNOWN
    }

    /// Get TypeId for a PrimitiveType
    pub fn primitive(&self, p: PrimitiveType) -> TypeId {
        match p {
            PrimitiveType::I8 => self.primitives.i8,
            PrimitiveType::I16 => self.primitives.i16,
            PrimitiveType::I32 => self.primitives.i32,
            PrimitiveType::I64 => self.primitives.i64,
            PrimitiveType::I128 => self.primitives.i128,
            PrimitiveType::U8 => self.primitives.u8,
            PrimitiveType::U16 => self.primitives.u16,
            PrimitiveType::U32 => self.primitives.u32,
            PrimitiveType::U64 => self.primitives.u64,
            PrimitiveType::F32 => self.primitives.f32,
            PrimitiveType::F64 => self.primitives.f64,
            PrimitiveType::Bool => self.primitives.bool,
            PrimitiveType::String => self.primitives.string,
        }
    }

    // ========================================================================
    // Compound type builders - intern on construction
    // ========================================================================

    /// Create a union type from variants.
    /// Normalizes: flattens nested unions, sorts descending (value types before sentinels), dedupes.
    pub fn union(&mut self, variants: impl Into<TypeIdVec>) -> TypeId {
        let variants = variants.into();
        // Propagate invalid
        if variants.iter().any(|&v| self.is_invalid(v)) {
            return self.invalid();
        }

        // Empty union is invalid
        if variants.is_empty() {
            return self.invalid();
        }

        // Flatten nested unions
        let mut flattened: Vec<TypeId> = Vec::new();
        for &v in variants.iter() {
            if let SemaType::Union(inner) = self.get(v) {
                flattened.extend(inner.iter().copied());
            } else {
                flattened.push(v);
            }
        }

        // Sort descending by Debug string - puts value types before sentinels
        // e.g., "Primitive(I64)" > "Nil" > "Done" alphabetically reversed
        flattened.sort_by_cached_key(|&v| std::cmp::Reverse(format!("{:?}", self.get(v))));

        // Dedupe
        flattened.dedup();

        // Unwrap single-element union
        if flattened.len() == 1 {
            flattened[0]
        } else {
            self.intern(SemaType::Union(flattened.into()))
        }
    }

    /// Create a tuple type from elements
    pub fn tuple(&mut self, elements: impl Into<TypeIdVec>) -> TypeId {
        let elements = elements.into();
        if elements.iter().any(|&e| self.is_invalid(e)) {
            return self.invalid();
        }
        self.intern(SemaType::Tuple(elements))
    }

    /// Create an array type
    pub fn array(&mut self, element: TypeId) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(SemaType::Array(element))
    }

    /// Create a fixed-size array type
    pub fn fixed_array(&mut self, element: TypeId, size: usize) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(SemaType::FixedArray { element, size })
    }

    /// Create a runtime iterator type
    pub fn runtime_iterator(&mut self, element: TypeId) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(SemaType::RuntimeIterator(element))
    }

    /// Create a function type.
    /// Returns Invalid if any param or the return type is Invalid.
    pub fn function(
        &mut self,
        params: impl Into<TypeIdVec>,
        ret: TypeId,
        is_closure: bool,
    ) -> TypeId {
        let params = params.into();
        // Propagate invalid through function types
        if params.iter().any(|p| self.is_invalid(*p)) || self.is_invalid(ret) {
            return self.invalid();
        }
        self.intern(SemaType::Function {
            params,
            ret,
            is_closure,
        })
    }

    /// Create an optional type (T | nil)
    pub fn optional(&mut self, inner: TypeId) -> TypeId {
        if self.is_invalid(inner) {
            return self.invalid();
        }
        let nil = self.nil();
        self.union(smallvec::smallvec![inner, nil])
    }

    /// Create a class type
    pub fn class(&mut self, type_def_id: TypeDefId, type_args: impl Into<TypeIdVec>) -> TypeId {
        let type_args = type_args.into();
        if type_args.iter().any(|&a| self.is_invalid(a)) {
            return self.invalid();
        }
        self.intern(SemaType::Class {
            type_def_id,
            type_args,
        })
    }

    /// Create a record type
    pub fn record(&mut self, type_def_id: TypeDefId, type_args: impl Into<TypeIdVec>) -> TypeId {
        let type_args = type_args.into();
        if type_args.iter().any(|&a| self.is_invalid(a)) {
            return self.invalid();
        }
        self.intern(SemaType::Record {
            type_def_id,
            type_args,
        })
    }

    /// Create an interface type
    pub fn interface(&mut self, type_def_id: TypeDefId, type_args: impl Into<TypeIdVec>) -> TypeId {
        let type_args = type_args.into();
        if type_args.iter().any(|&a| self.is_invalid(a)) {
            return self.invalid();
        }
        self.intern(SemaType::Interface {
            type_def_id,
            type_args,
        })
    }

    /// Create an error type
    pub fn error_type(&mut self, type_def_id: TypeDefId) -> TypeId {
        self.intern(SemaType::Error { type_def_id })
    }

    /// Create a type parameter placeholder
    pub fn type_param(&mut self, name_id: NameId) -> TypeId {
        self.intern(SemaType::TypeParam(name_id))
    }

    /// Create a type parameter reference
    pub fn type_param_ref(&mut self, type_param_id: TypeParamId) -> TypeId {
        self.intern(SemaType::TypeParamRef(type_param_id))
    }

    /// Create a module type with its exports
    pub fn module(
        &mut self,
        module_id: ModuleId,
        exports: SmallVec<[(NameId, TypeId); 8]>,
    ) -> TypeId {
        self.intern(SemaType::Module(Box::new(InternedModule {
            module_id,
            exports,
        })))
    }

    /// Register module metadata (constants, external_funcs) for codegen
    pub fn register_module_metadata(&mut self, module_id: ModuleId, metadata: ModuleMetadata) {
        self.module_metadata.insert(module_id, metadata);
    }

    /// Get module metadata for codegen
    pub fn module_metadata(&self, module_id: ModuleId) -> Option<&ModuleMetadata> {
        self.module_metadata.get(&module_id)
    }

    /// Create a fallible type: fallible(success, error)
    pub fn fallible(&mut self, success: TypeId, error: TypeId) -> TypeId {
        if self.is_invalid(success) || self.is_invalid(error) {
            return self.invalid();
        }
        self.intern(SemaType::Fallible { success, error })
    }

    /// Create a structural type (duck typing constraint)
    pub fn structural(
        &mut self,
        fields: SmallVec<[(NameId, TypeId); 4]>,
        methods: SmallVec<[InternedStructuralMethod; 2]>,
    ) -> TypeId {
        // Check for invalid types in fields or methods
        if fields.iter().any(|(_, ty)| self.is_invalid(*ty)) {
            return self.invalid();
        }
        if methods
            .iter()
            .any(|m| self.is_invalid(m.return_type) || m.params.iter().any(|&p| self.is_invalid(p)))
        {
            return self.invalid();
        }
        self.intern(SemaType::Structural(Box::new(InternedStructural {
            fields,
            methods,
        })))
    }

    /// Create a placeholder type (for inference)
    pub fn placeholder(&mut self, kind: PlaceholderKind) -> TypeId {
        self.intern(SemaType::Placeholder(kind))
    }

    // ========================================================================
    // Query methods - predicates and unwrap helpers
    // ========================================================================

    /// Check if this is a numeric type (can do arithmetic)
    #[inline]
    pub fn is_numeric(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive numerics
        id.is_numeric()
    }

    /// Check if this is an integer type
    #[inline]
    pub fn is_integer(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive integers
        id.is_integer()
    }

    /// Check if this is a floating point type
    #[inline]
    pub fn is_float(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all primitive floats
        id.is_float()
    }

    /// Check if this is a signed integer type
    #[inline]
    pub fn is_signed(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all signed integers
        id.is_signed_int()
    }

    /// Check if this is an unsigned integer type
    #[inline]
    pub fn is_unsigned(&self, id: TypeId) -> bool {
        // Short-circuit: TypeId knows all unsigned integers
        id.is_unsigned_int()
    }

    /// Check if this is an optional type (union containing nil)
    pub fn is_optional(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Union(variants) => variants.contains(&self.nil()),
            _ => false,
        }
    }

    /// Unwrap an array type, returning the element type
    pub fn unwrap_array(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::Array(elem) => Some(*elem),
            _ => None,
        }
    }

    /// Unwrap an optional type, returning the non-nil type
    pub fn unwrap_optional(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::Union(variants) => {
                let nil = self.nil();
                let non_nil: TypeIdVec = variants.iter().copied().filter(|&v| v != nil).collect();
                if non_nil.len() == 1 {
                    Some(non_nil[0])
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Unwrap a function type, returning (params, return_type, is_closure)
    pub fn unwrap_function(&self, id: TypeId) -> Option<(&TypeIdVec, TypeId, bool)> {
        match self.get(id) {
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => Some((params, *ret, *is_closure)),
            _ => None,
        }
    }

    /// Unwrap a tuple type, returning the element types
    pub fn unwrap_tuple(&self, id: TypeId) -> Option<&TypeIdVec> {
        match self.get(id) {
            SemaType::Tuple(elements) => Some(elements),
            _ => None,
        }
    }

    /// Unwrap a fixed array type, returning (element, size)
    pub fn unwrap_fixed_array(&self, id: TypeId) -> Option<(TypeId, usize)> {
        match self.get(id) {
            SemaType::FixedArray { element, size } => Some((*element, *size)),
            _ => None,
        }
    }

    /// Get TypeDefId for nominal types (class, record, interface, error)
    pub fn type_def_id(&self, id: TypeId) -> Option<TypeDefId> {
        match self.get(id) {
            SemaType::Class { type_def_id, .. } => Some(*type_def_id),
            SemaType::Record { type_def_id, .. } => Some(*type_def_id),
            SemaType::Interface { type_def_id, .. } => Some(*type_def_id),
            SemaType::Error { type_def_id } => Some(*type_def_id),
            _ => None,
        }
    }

    /// Get type arguments for generic types
    pub fn type_args(&self, id: TypeId) -> &[TypeId] {
        match self.get(id) {
            SemaType::Class { type_args, .. } => type_args,
            SemaType::Record { type_args, .. } => type_args,
            SemaType::Interface { type_args, .. } => type_args,
            _ => &[],
        }
    }

    /// Assert this type is valid. Panics with context if invalid.
    /// Use in codegen where invalid types indicate a compiler bug.
    #[track_caller]
    pub fn expect_valid(&self, id: TypeId, context: &str) -> TypeId {
        if self.is_invalid(id) {
            panic!(
                "INTERNAL ERROR: Invalid type in codegen\n\
                 Context: {}\n\
                 Location: {}",
                context,
                std::panic::Location::caller()
            );
        }
        id
    }

    // =========================================================================
    // Type predicates for codegen pattern matching
    // =========================================================================

    /// Check if this is an array type
    pub fn is_array(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Array(_))
    }

    /// Check if this is a function type
    pub fn is_function(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Function { .. })
    }

    /// Check if this is a class type
    pub fn is_class(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Class { .. })
    }

    /// Check if this is a record type
    pub fn is_record(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Record { .. })
    }

    /// Check if this is an interface type
    pub fn is_interface(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Interface { .. })
    }

    /// Check if this is an error type
    pub fn is_error(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Error { .. })
    }

    /// Check if this is a union type
    pub fn is_union(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Union(_))
    }

    /// Check if this is the string primitive
    #[inline]
    pub fn is_string(&self, id: TypeId) -> bool {
        id == TypeId::STRING
    }

    /// Check if this is nil
    #[inline]
    pub fn is_nil(&self, id: TypeId) -> bool {
        id.is_nil()
    }

    /// Check if this is void
    #[inline]
    pub fn is_void(&self, id: TypeId) -> bool {
        id.is_void()
    }

    /// Check if this is the never type (bottom type)
    #[inline]
    pub fn is_never(&self, id: TypeId) -> bool {
        id.is_never()
    }

    /// Check if this is the unknown type (top type)
    #[inline]
    pub fn is_unknown(&self, id: TypeId) -> bool {
        id.is_unknown()
    }

    /// Check if this is a runtime iterator type
    pub fn is_runtime_iterator(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::RuntimeIterator(_))
    }

    /// Check if an integer literal value fits within a type (handles unions)
    pub fn literal_fits_id(&self, value: i64, id: TypeId) -> bool {
        // Check primitive types directly
        if id.fits_literal(value) {
            return true;
        }
        // For unions, check if literal fits any numeric variant
        if let Some(variants) = self.unwrap_union(id) {
            return variants.iter().any(|&v| v.fits_literal(value));
        }
        false
    }

    // =========================================================================
    // Unwrap helpers for codegen
    // =========================================================================

    /// Unwrap a class type, returning (type_def_id, type_args)
    pub fn unwrap_class(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        match self.get(id) {
            SemaType::Class {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap a record type, returning (type_def_id, type_args)
    pub fn unwrap_record(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        match self.get(id) {
            SemaType::Record {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap an interface type, returning (type_def_id, type_args)
    pub fn unwrap_interface(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec)> {
        match self.get(id) {
            SemaType::Interface {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args)),
            _ => None,
        }
    }

    /// Unwrap any nominal type (class, record, or interface), returning (type_def_id, type_args, kind).
    ///
    /// This is a convenience helper that combines unwrap_class, unwrap_record, and unwrap_interface
    /// into a single call. Use this when you need to handle all three nominal types uniformly.
    pub fn unwrap_nominal(&self, id: TypeId) -> Option<(TypeDefId, &TypeIdVec, NominalKind)> {
        match self.get(id) {
            SemaType::Class {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Class)),
            SemaType::Record {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Record)),
            SemaType::Interface {
                type_def_id,
                type_args,
            } => Some((*type_def_id, type_args, NominalKind::Interface)),
            _ => None,
        }
    }

    /// Unwrap an error type, returning type_def_id
    pub fn unwrap_error(&self, id: TypeId) -> Option<TypeDefId> {
        match self.get(id) {
            SemaType::Error { type_def_id } => Some(*type_def_id),
            _ => None,
        }
    }

    /// Unwrap a union type, returning the variants
    pub fn unwrap_union(&self, id: TypeId) -> Option<&TypeIdVec> {
        match self.get(id) {
            SemaType::Union(variants) => Some(variants),
            _ => None,
        }
    }

    /// Unwrap a runtime iterator type, returning the element type
    pub fn unwrap_runtime_iterator(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            SemaType::RuntimeIterator(elem) => Some(*elem),
            _ => None,
        }
    }

    /// Look up an existing RuntimeIterator type by element type (read-only).
    /// Returns None if the type doesn't exist in the arena.
    pub fn lookup_runtime_iterator(&self, element: TypeId) -> Option<TypeId> {
        let ty = SemaType::RuntimeIterator(element);
        self.intern_map.get(&ty).copied()
    }

    /// Unwrap a fallible type, returning (success, error)
    pub fn unwrap_fallible(&self, id: TypeId) -> Option<(TypeId, TypeId)> {
        match self.get(id) {
            SemaType::Fallible { success, error } => Some((*success, *error)),
            _ => None,
        }
    }

    /// Unwrap a module type, returning the InternedModule
    pub fn unwrap_module(&self, id: TypeId) -> Option<&InternedModule> {
        match self.get(id) {
            SemaType::Module(m) => Some(m.as_ref()),
            _ => None,
        }
    }

    /// Unwrap a type parameter, returning its NameId
    pub fn unwrap_type_param(&self, id: TypeId) -> Option<NameId> {
        match self.get(id) {
            SemaType::TypeParam(name_id) => Some(*name_id),
            _ => None,
        }
    }

    /// Unwrap a type parameter reference, returning its TypeParamId
    pub fn unwrap_type_param_ref(&self, id: TypeId) -> Option<TypeParamId> {
        match self.get(id) {
            SemaType::TypeParamRef(id) => Some(*id),
            _ => None,
        }
    }

    /// Unwrap a structural type, returning its fields and methods
    pub fn unwrap_structural(&self, id: TypeId) -> Option<&InternedStructural> {
        match self.get(id) {
            SemaType::Structural(s) => Some(s),
            _ => None,
        }
    }

    /// Display a type for error messages (basic version without name resolution)
    pub fn display_basic(&self, id: TypeId) -> String {
        match self.get(id) {
            SemaType::Primitive(p) => p.name().to_string(),
            SemaType::Void => "void".to_string(),
            SemaType::Nil => "nil".to_string(),
            SemaType::Done => "Done".to_string(),
            SemaType::Range => "range".to_string(),
            SemaType::MetaType => "type".to_string(),
            SemaType::Never => "never".to_string(),
            SemaType::Unknown => "unknown".to_string(),
            SemaType::Invalid { kind } => format!("<invalid: {}>", kind),
            SemaType::Union(variants) => {
                let parts: Vec<String> = variants.iter().map(|&v| self.display_basic(v)).collect();
                parts.join(" | ")
            }
            SemaType::Tuple(elements) => {
                let parts: Vec<String> = elements.iter().map(|&e| self.display_basic(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            SemaType::Array(elem) => format!("[{}]", self.display_basic(*elem)),
            SemaType::FixedArray { element, size } => {
                format!("[{}; {}]", self.display_basic(*element), size)
            }
            SemaType::RuntimeIterator(elem) => {
                format!("Iterator<{}>", self.display_basic(*elem))
            }
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let param_str: Vec<String> =
                    params.iter().map(|&p| self.display_basic(p)).collect();
                let closure_marker = if *is_closure { "closure " } else { "" };
                format!(
                    "{}({}) -> {}",
                    closure_marker,
                    param_str.join(", "),
                    self.display_basic(*ret)
                )
            }
            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("class#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("class#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Record {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("record#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("record#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                if type_args.is_empty() {
                    format!("interface#{}", type_def_id.index())
                } else {
                    let args: Vec<String> =
                        type_args.iter().map(|&a| self.display_basic(a)).collect();
                    format!("interface#{}<{}>", type_def_id.index(), args.join(", "))
                }
            }
            SemaType::Error { type_def_id } => format!("error#{}", type_def_id.index()),
            SemaType::TypeParam(name_id) => format!("TypeParam({:?})", name_id),
            SemaType::TypeParamRef(id) => format!("TypeParamRef#{}", id.index()),
            SemaType::Module(m) => format!("module#{}", m.module_id.index()),
            SemaType::Fallible { success, error } => {
                format!(
                    "fallible({}, {})",
                    self.display_basic(*success),
                    self.display_basic(*error)
                )
            }
            SemaType::Structural(st) => {
                let field_strs: Vec<String> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| format!("{:?}: {}", name, self.display_basic(*ty)))
                    .collect();
                let method_strs: Vec<String> = st
                    .methods
                    .iter()
                    .map(|m| {
                        let params: Vec<String> =
                            m.params.iter().map(|&p| self.display_basic(p)).collect();
                        format!(
                            "{:?}({}) -> {}",
                            m.name,
                            params.join(", "),
                            self.display_basic(m.return_type)
                        )
                    })
                    .collect();
                format!(
                    "{{ {} | {} }}",
                    field_strs.join(", "),
                    method_strs.join(", ")
                )
            }
            SemaType::Placeholder(kind) => format!("{}", kind),
        }
    }

    // ========================================================================
    // Type substitution
    // ========================================================================

    /// Substitute type parameters with concrete types.
    ///
    /// This is the core operation for generic type instantiation. Given a map
    /// from type parameter NameIds to concrete TypeIds, returns a new TypeId with
    /// all type parameters replaced.
    ///
    /// Automatically cached via interning: same input produces same TypeId.
    pub fn substitute(&mut self, ty: TypeId, subs: &FxHashMap<NameId, TypeId>) -> TypeId {
        // Early exit if no substitutions
        if subs.is_empty() {
            return ty;
        }

        // Clone the interned type to release the borrow
        match self.get(ty).clone() {
            // Direct substitution for type parameters
            SemaType::TypeParam(name_id) => subs.get(&name_id).copied().unwrap_or(ty),

            // TypeParamRef doesn't substitute based on NameId
            SemaType::TypeParamRef(_) => ty,

            // Recursive substitution for compound types
            SemaType::Array(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.array(new_elem)
            }

            SemaType::Union(variants) => {
                let new_variants: TypeIdVec =
                    variants.iter().map(|&v| self.substitute(v, subs)).collect();
                self.union(new_variants)
            }

            SemaType::Tuple(elements) => {
                let new_elements: TypeIdVec =
                    elements.iter().map(|&e| self.substitute(e, subs)).collect();
                self.tuple(new_elements)
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec =
                    params.iter().map(|&p| self.substitute(p, subs)).collect();
                let new_ret = self.substitute(ret, subs);
                self.function(new_params, new_ret, is_closure)
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.class(type_def_id, new_args)
            }

            SemaType::Record {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.record(type_def_id, new_args)
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.runtime_iterator(new_elem)
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.substitute(element, subs);
                self.fixed_array(new_elem, size)
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.substitute(success, subs);
                let new_error = self.substitute(error, subs);
                self.fallible(new_success, new_error)
            }

            SemaType::Structural(st) => {
                let new_fields: SmallVec<[(NameId, TypeId); 4]> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| (*name, self.substitute(*ty, subs)))
                    .collect();
                let new_methods: SmallVec<[InternedStructuralMethod; 2]> = st
                    .methods
                    .iter()
                    .map(|m| InternedStructuralMethod {
                        name: m.name,
                        params: m.params.iter().map(|&p| self.substitute(p, subs)).collect(),
                        return_type: self.substitute(m.return_type, subs),
                    })
                    .collect();
                self.structural(new_fields, new_methods)
            }

            // Types without nested type parameters - return unchanged
            SemaType::Primitive(_)
            | SemaType::Void
            | SemaType::Nil
            | SemaType::Done
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(_) => ty,
        }
    }

    /// Look up a substituted type without creating new types.
    ///
    /// This is the read-only version of `substitute`. Returns `Some(type_id)` if
    /// the substituted type already exists in the arena, `None` if any intermediate
    /// or final type would need to be created.
    ///
    /// Use this in codegen where all types should already be fully instantiated.
    pub fn lookup_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
    ) -> Option<TypeId> {
        // Early exit if no substitutions
        if subs.is_empty() {
            return Some(ty);
        }

        match self.get(ty) {
            // Direct substitution for type parameters
            SemaType::TypeParam(name_id) => subs.get(name_id).copied(),

            // TypeParamRef doesn't substitute based on NameId
            SemaType::TypeParamRef(_) => Some(ty),

            // Recursive lookup for compound types
            SemaType::Array(elem) => {
                let new_elem = self.lookup_substitute(*elem, subs)?;
                if new_elem == *elem {
                    return Some(ty);
                }
                let result_ty = SemaType::Array(new_elem);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Union(variants) => {
                let new_variants: Option<TypeIdVec> = variants
                    .iter()
                    .map(|&v| self.lookup_substitute(v, subs))
                    .collect();
                let new_variants = new_variants?;
                if new_variants == *variants {
                    return Some(ty);
                }
                // For unions, we need to look up the normalized result
                // Since union normalization is complex, we look up the exact union structure
                let result_ty = SemaType::Union(new_variants);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Tuple(elements) => {
                let new_elements: Option<TypeIdVec> = elements
                    .iter()
                    .map(|&e| self.lookup_substitute(e, subs))
                    .collect();
                let new_elements = new_elements?;
                if new_elements == *elements {
                    return Some(ty);
                }
                let result_ty = SemaType::Tuple(new_elements);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: Option<TypeIdVec> = params
                    .iter()
                    .map(|&p| self.lookup_substitute(p, subs))
                    .collect();
                let new_params = new_params?;
                let new_ret = self.lookup_substitute(*ret, subs)?;
                if new_params == *params && new_ret == *ret {
                    return Some(ty);
                }
                let result_ty = SemaType::Function {
                    params: new_params,
                    ret: new_ret,
                    is_closure: *is_closure,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: Option<TypeIdVec> = type_args
                    .iter()
                    .map(|&a| self.lookup_substitute(a, subs))
                    .collect();
                let new_args = new_args?;
                if new_args == *type_args {
                    return Some(ty);
                }
                let result_ty = SemaType::Class {
                    type_def_id: *type_def_id,
                    type_args: new_args,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Record {
                type_def_id,
                type_args,
            } => {
                let new_args: Option<TypeIdVec> = type_args
                    .iter()
                    .map(|&a| self.lookup_substitute(a, subs))
                    .collect();
                let new_args = new_args?;
                if new_args == *type_args {
                    return Some(ty);
                }
                let result_ty = SemaType::Record {
                    type_def_id: *type_def_id,
                    type_args: new_args,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: Option<TypeIdVec> = type_args
                    .iter()
                    .map(|&a| self.lookup_substitute(a, subs))
                    .collect();
                let new_args = new_args?;
                if new_args == *type_args {
                    return Some(ty);
                }
                let result_ty = SemaType::Interface {
                    type_def_id: *type_def_id,
                    type_args: new_args,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.lookup_substitute(*elem, subs)?;
                if new_elem == *elem {
                    return Some(ty);
                }
                let result_ty = SemaType::RuntimeIterator(new_elem);
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.lookup_substitute(*element, subs)?;
                if new_elem == *element {
                    return Some(ty);
                }
                let result_ty = SemaType::FixedArray {
                    element: new_elem,
                    size: *size,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.lookup_substitute(*success, subs)?;
                let new_error = self.lookup_substitute(*error, subs)?;
                if new_success == *success && new_error == *error {
                    return Some(ty);
                }
                let result_ty = SemaType::Fallible {
                    success: new_success,
                    error: new_error,
                };
                self.intern_map.get(&result_ty).copied()
            }

            SemaType::Structural(st) => {
                let new_fields: Option<SmallVec<[(NameId, TypeId); 4]>> = st
                    .fields
                    .iter()
                    .map(|(name, ty)| Some((*name, self.lookup_substitute(*ty, subs)?)))
                    .collect();
                let new_fields = new_fields?;
                let new_methods: Option<SmallVec<[InternedStructuralMethod; 2]>> = st
                    .methods
                    .iter()
                    .map(|m| {
                        let new_params: Option<TypeIdVec> = m
                            .params
                            .iter()
                            .map(|&p| self.lookup_substitute(p, subs))
                            .collect();
                        Some(InternedStructuralMethod {
                            name: m.name,
                            params: new_params?,
                            return_type: self.lookup_substitute(m.return_type, subs)?,
                        })
                    })
                    .collect();
                let new_methods = new_methods?;
                if new_fields == st.fields && new_methods == st.methods {
                    return Some(ty);
                }
                let result_ty = SemaType::Structural(Box::new(InternedStructural {
                    fields: new_fields,
                    methods: new_methods,
                }));
                self.intern_map.get(&result_ty).copied()
            }

            // Types without nested type parameters - return unchanged
            SemaType::Primitive(_)
            | SemaType::Void
            | SemaType::Nil
            | SemaType::Done
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(_) => Some(ty),
        }
    }

    /// Look up a substituted type, panicking if it doesn't exist.
    ///
    /// This is a helper for codegen where all types should be fully instantiated.
    /// Panics with a detailed error message if the lookup fails.
    #[track_caller]
    pub fn expect_substitute(
        &self,
        ty: TypeId,
        subs: &FxHashMap<NameId, TypeId>,
        context: &str,
    ) -> TypeId {
        self.lookup_substitute(ty, subs).unwrap_or_else(|| {
            panic!(
                "INTERNAL ERROR: Type not found after substitution\n\
                 Context: {}\n\
                 Original type: {}\n\
                 Location: {}",
                context,
                self.display_basic(ty),
                std::panic::Location::caller()
            )
        })
    }

    /// Substitute SelfType placeholders with a concrete type.
    ///
    /// Used when resolving interface method signatures on type parameters:
    /// the interface's `Self` type should be replaced with the receiver type.
    pub fn substitute_self(&mut self, ty: TypeId, self_type: TypeId) -> TypeId {
        // Clone the interned type to release the borrow
        match self.get(ty).clone() {
            // Substitute SelfType placeholder
            SemaType::Placeholder(PlaceholderKind::SelfType) => self_type,

            // Recursive substitution for compound types
            SemaType::Array(elem) => {
                let new_elem = self.substitute_self(elem, self_type);
                self.array(new_elem)
            }

            SemaType::Union(variants) => {
                let new_variants: TypeIdVec = variants
                    .iter()
                    .map(|&v| self.substitute_self(v, self_type))
                    .collect();
                self.union(new_variants)
            }

            SemaType::Tuple(elements) => {
                let new_elements: TypeIdVec = elements
                    .iter()
                    .map(|&e| self.substitute_self(e, self_type))
                    .collect();
                self.tuple(new_elements)
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec = params
                    .iter()
                    .map(|&p| self.substitute_self(p, self_type))
                    .collect();
                let new_ret = self.substitute_self(ret, self_type);
                self.function(new_params, new_ret, is_closure)
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_self(a, self_type))
                    .collect();
                self.class(type_def_id, new_args)
            }

            SemaType::Record {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_self(a, self_type))
                    .collect();
                self.record(type_def_id, new_args)
            }

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute_self(a, self_type))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            SemaType::RuntimeIterator(elem) => {
                let new_elem = self.substitute_self(elem, self_type);
                self.runtime_iterator(new_elem)
            }

            SemaType::FixedArray { element, size } => {
                let new_elem = self.substitute_self(element, self_type);
                self.fixed_array(new_elem, size)
            }

            SemaType::Fallible { success, error } => {
                let new_success = self.substitute_self(success, self_type);
                let new_error = self.substitute_self(error, self_type);
                self.fallible(new_success, new_error)
            }

            // Types that don't contain SelfType placeholders
            SemaType::Primitive(_)
            | SemaType::TypeParam(_)
            | SemaType::TypeParamRef(_)
            | SemaType::Void
            | SemaType::Nil
            | SemaType::Done
            | SemaType::Range
            | SemaType::MetaType
            | SemaType::Never
            | SemaType::Unknown
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(PlaceholderKind::Inference)
            | SemaType::Placeholder(PlaceholderKind::TypeParam(_))
            | SemaType::Structural(_) => ty,
        }
    }
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_id_is_copy() {
        let id = TypeId(42);
        let id2 = id; // Copy
        assert_eq!(id, id2);
    }

    #[test]
    fn type_id_vec_inline_capacity() {
        let vec: TypeIdVec = smallvec::smallvec![TypeId(1), TypeId(2), TypeId(3), TypeId(4)];
        assert!(!vec.spilled()); // Should be inline
    }

    #[test]
    fn type_id_vec_spills_beyond_4() {
        let vec: TypeIdVec =
            smallvec::smallvec![TypeId(1), TypeId(2), TypeId(3), TypeId(4), TypeId(5)];
        assert!(vec.spilled()); // Should spill to heap
    }

    #[test]
    fn interned_type_size() {
        // Verify SemaType is reasonably sized
        let size = size_of::<SemaType>();
        assert!(size <= 48, "SemaType is {} bytes, expected <= 48", size);
    }

    #[test]
    fn type_id_size() {
        assert_eq!(size_of::<TypeId>(), 4);
    }

    #[test]
    fn primitives_preallocated() {
        let arena = TypeArena::new();
        // All primitives should have stable, distinct IDs
        assert_ne!(arena.primitives.i32, arena.primitives.string);
        assert_ne!(arena.primitives.i32, arena.primitives.i64);
        assert_ne!(arena.primitives.nil, arena.primitives.void);
    }

    #[test]
    fn invalid_is_at_index_zero() {
        let arena = TypeArena::new();
        assert_eq!(arena.primitives.invalid.0, 0);
        assert!(arena.is_invalid(arena.primitives.invalid));
        assert!(!arena.is_invalid(arena.primitives.i32));
    }

    // ========================================================================
    // Phase 1.2 tests: Interning and builder methods
    // ========================================================================

    #[test]
    fn interning_deduplicates() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let nil_id = arena.nil();
        let a = arena.union(smallvec::smallvec![i32_id, nil_id]);
        let b = arena.union(smallvec::smallvec![i32_id, nil_id]);
        assert_eq!(a, b); // Same TypeId
    }

    #[test]
    fn different_types_different_ids() {
        let mut arena = TypeArena::new();
        let a = arena.array(arena.i32());
        let b = arena.array(arena.string());
        assert_ne!(a, b);
    }

    #[test]
    fn optional_is_union_with_nil() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let opt = arena.optional(i32_id);
        match arena.get(opt) {
            SemaType::Union(variants) => {
                assert_eq!(variants.len(), 2);
                assert!(variants.contains(&arena.nil()));
                assert!(variants.contains(&arena.i32()));
            }
            _ => panic!("optional should be union"),
        }
    }

    #[test]
    fn primitive_accessor_matches_enum() {
        let arena = TypeArena::new();
        assert_eq!(arena.primitive(PrimitiveType::I32), arena.i32());
        assert_eq!(arena.primitive(PrimitiveType::String), arena.string());
        assert_eq!(arena.primitive(PrimitiveType::Bool), arena.bool());
    }

    #[test]
    fn array_builder() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        match arena.get(arr) {
            SemaType::Array(elem) => {
                assert_eq!(*elem, arena.i32());
            }
            _ => panic!("expected array type"),
        }
    }

    #[test]
    fn function_builder() {
        let mut arena = TypeArena::new();
        let i32_id = arena.i32();
        let string_id = arena.string();
        let func = arena.function(smallvec::smallvec![i32_id, string_id], arena.bool(), false);
        match arena.get(func) {
            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                assert_eq!(params.len(), 2);
                assert_eq!(params[0], i32_id);
                assert_eq!(params[1], string_id);
                assert_eq!(*ret, arena.bool());
                assert!(!is_closure);
            }
            _ => panic!("expected function type"),
        }
    }

    #[test]
    fn tuple_builder() {
        let mut arena = TypeArena::new();
        let tup = arena.tuple(smallvec::smallvec![
            arena.i32(),
            arena.string(),
            arena.bool()
        ]);
        match arena.get(tup) {
            SemaType::Tuple(elements) => {
                assert_eq!(elements.len(), 3);
            }
            _ => panic!("expected tuple type"),
        }
    }

    #[test]
    fn class_builder() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(type_def_id, smallvec::smallvec![arena.i32()]);
        match arena.get(cls) {
            SemaType::Class {
                type_def_id: tid,
                type_args,
            } => {
                assert_eq!(*tid, type_def_id);
                assert_eq!(type_args.len(), 1);
                assert_eq!(type_args[0], arena.i32());
            }
            _ => panic!("expected class type"),
        }
    }

    #[test]
    fn invalid_propagates() {
        let mut arena = TypeArena::new();
        let invalid = arena.invalid();

        // Union with invalid returns invalid
        let union_invalid = arena.union(smallvec::smallvec![arena.i32(), invalid]);
        assert!(arena.is_invalid(union_invalid));

        // Array of invalid returns invalid
        let arr_invalid = arena.array(invalid);
        assert!(arena.is_invalid(arr_invalid));

        // Function with invalid param returns invalid
        let func_invalid = arena.function(smallvec::smallvec![invalid], arena.i32(), false);
        assert!(arena.is_invalid(func_invalid));

        // Optional of invalid returns invalid
        let opt_invalid = arena.optional(invalid);
        assert!(arena.is_invalid(opt_invalid));
    }

    // ========================================================================
    // Phase 1.3 tests: Query methods and Display
    // ========================================================================

    #[test]
    fn is_numeric_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_numeric(arena.i32()));
        assert!(arena.is_numeric(arena.i64()));
        assert!(arena.is_numeric(arena.f64()));
        assert!(!arena.is_numeric(arena.string()));
        assert!(!arena.is_numeric(arena.bool()));
    }

    #[test]
    fn is_integer_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_integer(arena.i32()));
        assert!(arena.is_integer(arena.u64()));
        assert!(!arena.is_integer(arena.f64()));
        assert!(!arena.is_integer(arena.string()));
    }

    #[test]
    fn is_float_primitives() {
        let arena = TypeArena::new();
        assert!(arena.is_float(arena.f32()));
        assert!(arena.is_float(arena.f64()));
        assert!(!arena.is_float(arena.i32()));
    }

    #[test]
    fn unwrap_array_works() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        assert_eq!(arena.unwrap_array(arr), Some(arena.i32()));
        assert_eq!(arena.unwrap_array(arena.i32()), None);
    }

    #[test]
    fn unwrap_optional_works() {
        let mut arena = TypeArena::new();
        let opt = arena.optional(arena.string());
        assert_eq!(arena.unwrap_optional(opt), Some(arena.string()));
        assert_eq!(arena.unwrap_optional(arena.string()), None);
    }

    #[test]
    fn unwrap_function_works() {
        let mut arena = TypeArena::new();
        let func = arena.function(smallvec::smallvec![arena.i32()], arena.string(), true);
        let (params, ret, is_closure) = arena.unwrap_function(func).unwrap();
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], arena.i32());
        assert_eq!(ret, arena.string());
        assert!(is_closure);
    }

    #[test]
    fn type_def_id_extraction() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(type_def_id, TypeIdVec::new());
        assert_eq!(arena.type_def_id(cls), Some(type_def_id));
        assert_eq!(arena.type_def_id(arena.i32()), None);
    }

    #[test]
    fn type_args_extraction() {
        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        let cls = arena.class(
            type_def_id,
            smallvec::smallvec![arena.i32(), arena.string()],
        );
        let args = arena.type_args(cls);
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], arena.i32());
        assert_eq!(args[1], arena.string());
    }

    #[test]
    #[should_panic(expected = "Invalid type in codegen")]
    fn expect_valid_panics_on_invalid() {
        let arena = TypeArena::new();
        arena.expect_valid(arena.invalid(), "test context");
    }

    #[test]
    fn expect_valid_returns_valid() {
        let arena = TypeArena::new();
        let i32_id = arena.i32();
        assert_eq!(arena.expect_valid(i32_id, "test"), i32_id);
    }

    #[test]
    fn display_basic_primitives() {
        let arena = TypeArena::new();
        assert_eq!(arena.display_basic(arena.i32()), "i32");
        assert_eq!(arena.display_basic(arena.string()), "string");
        assert_eq!(arena.display_basic(arena.bool()), "bool");
        assert_eq!(arena.display_basic(arena.nil()), "nil");
        assert_eq!(arena.display_basic(arena.void()), "void");
    }

    #[test]
    fn display_basic_compound() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        assert_eq!(arena.display_basic(arr), "[i32]");

        let opt = arena.optional(arena.string());
        let opt_display = arena.display_basic(opt);
        // Order may vary in union, but should contain both
        assert!(opt_display.contains("string"));
        assert!(opt_display.contains("nil"));
    }

    #[test]
    fn display_basic_function() {
        let mut arena = TypeArena::new();
        let func = arena.function(
            smallvec::smallvec![arena.i32(), arena.string()],
            arena.bool(),
            false,
        );
        assert_eq!(arena.display_basic(func), "(i32, string) -> bool");
    }

    // ========================================================================
    // Phase 1.4 tests: Substitution
    // ========================================================================

    #[test]
    fn substitute_type_param() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        let result = arena.substitute(t, &subs);
        assert_eq!(result, arena.i32());
    }

    #[test]
    fn substitute_array_of_type_param() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());

        let result = arena.substitute(arr_t, &subs);
        let expected = arena.array(arena.string());
        assert_eq!(result, expected);
    }

    #[test]
    fn substitute_caches_via_interning() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let nil = arena.nil();
        let t = arena.type_param(name_id);
        let union_t = arena.union(smallvec::smallvec![t, nil]);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        let result1 = arena.substitute(union_t, &subs);
        let result2 = arena.substitute(union_t, &subs);
        assert_eq!(result1, result2); // Same TypeId due to interning

        // Should match direct construction
        let i32_id = arena.i32();
        let nil_id = arena.nil();
        let direct = arena.union(smallvec::smallvec![i32_id, nil_id]);
        assert_eq!(result1, direct);
    }

    #[test]
    fn substitute_empty_is_noop() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        let empty_subs: FxHashMap<NameId, TypeId> = FxHashMap::default();

        let result = arena.substitute(arr, &empty_subs);
        assert_eq!(result, arr); // Exact same TypeId
    }

    #[test]
    fn substitute_unchanged_returns_interned() {
        let mut arena = TypeArena::new();
        let _name_id = NameId::new_for_test(999);
        let other_id = NameId::new_for_test(888);

        let arr = arena.array(arena.i32()); // No type params

        let mut subs = FxHashMap::default();
        subs.insert(other_id, arena.string()); // Unrelated substitution

        let result = arena.substitute(arr, &subs);
        // Should return equivalent TypeId (may or may not be same due to interning)
        assert_eq!(arena.unwrap_array(result), Some(arena.i32()));
    }

    #[test]
    fn substitute_function_type() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let u_id = NameId::new_for_test(101);

        let t = arena.type_param(t_id);
        let u = arena.type_param(u_id);
        let func = arena.function(smallvec::smallvec![t], u, false);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i32());
        subs.insert(u_id, arena.string());

        let result = arena.substitute(func, &subs);
        let (params, ret, _) = arena.unwrap_function(result).unwrap();
        assert_eq!(params[0], arena.i32());
        assert_eq!(ret, arena.string());
    }

    #[test]
    fn substitute_class_type_args() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let type_def_id = TypeDefId::new(42);

        let t = arena.type_param(t_id);
        let cls = arena.class(type_def_id, smallvec::smallvec![t]);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i64());

        let result = arena.substitute(cls, &subs);
        let args = arena.type_args(result);
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], arena.i64());
    }

    #[test]
    fn substitute_nested_types() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);

        // Array<Array<T>>
        let t = arena.type_param(t_id);
        let inner_arr = arena.array(t);
        let outer_arr = arena.array(inner_arr);

        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.bool());

        let result = arena.substitute(outer_arr, &subs);

        // Should be Array<Array<bool>>
        let inner = arena.unwrap_array(result).unwrap();
        let innermost = arena.unwrap_array(inner).unwrap();
        assert_eq!(innermost, arena.bool());
    }

    // ========================================================================
    // lookup_substitute tests
    // ========================================================================

    #[test]
    fn lookup_substitute_empty_subs() {
        let mut arena = TypeArena::new();
        let arr = arena.array(arena.i32());
        let empty_subs: FxHashMap<NameId, TypeId> = FxHashMap::default();

        // Empty substitutions should return the same type
        let result = arena.lookup_substitute(arr, &empty_subs);
        assert_eq!(result, Some(arr));
    }

    #[test]
    fn lookup_substitute_primitive_unchanged() {
        let arena = TypeArena::new();
        let mut subs = FxHashMap::default();
        let name_id = NameId::new_for_test(999);
        subs.insert(name_id, arena.string());

        // Primitive with unrelated substitution should return unchanged
        let result = arena.lookup_substitute(arena.i32(), &subs);
        assert_eq!(result, Some(arena.i32()));
    }

    #[test]
    fn lookup_substitute_type_param_found() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i32());

        // Direct type param lookup
        let result = arena.lookup_substitute(t, &subs);
        assert_eq!(result, Some(arena.i32()));
    }

    #[test]
    fn lookup_substitute_type_param_not_in_subs() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let other_id = NameId::new_for_test(888);
        let t = arena.type_param(name_id);

        let mut subs = FxHashMap::default();
        subs.insert(other_id, arena.i32()); // Different name_id

        // Type param not in substitutions should return None
        let result = arena.lookup_substitute(t, &subs);
        assert_eq!(result, None);
    }

    #[test]
    fn lookup_substitute_existing_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // First, create the substituted type so it exists
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());
        let expected = arena.substitute(arr_t, &subs);

        // Now lookup should find it
        let result = arena.lookup_substitute(arr_t, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn lookup_substitute_nonexistent_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Create a type that substitutes T -> i64, but we'll query T -> f32
        let mut subs1 = FxHashMap::default();
        subs1.insert(name_id, arena.i64());
        let _ = arena.substitute(arr_t, &subs1);

        // Now lookup with a different substitution that wasn't created
        let mut subs2 = FxHashMap::default();
        subs2.insert(name_id, arena.f32());

        let result = arena.lookup_substitute(arr_t, &subs2);
        assert_eq!(result, None); // Array<f32> doesn't exist
    }

    #[test]
    fn lookup_substitute_class_type() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(100);
        let type_def_id = TypeDefId::new(42);

        let t = arena.type_param(name_id);
        let cls = arena.class(type_def_id, smallvec::smallvec![t]);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.i64());
        let expected = arena.substitute(cls, &subs);

        // Lookup should find it
        let result = arena.lookup_substitute(cls, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    fn lookup_substitute_function_type() {
        let mut arena = TypeArena::new();
        let t_id = NameId::new_for_test(100);
        let u_id = NameId::new_for_test(101);

        let t = arena.type_param(t_id);
        let u = arena.type_param(u_id);
        let func = arena.function(smallvec::smallvec![t], u, false);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(t_id, arena.i32());
        subs.insert(u_id, arena.string());
        let expected = arena.substitute(func, &subs);

        // Lookup should find it
        let result = arena.lookup_substitute(func, &subs);
        assert_eq!(result, Some(expected));
    }

    #[test]
    #[should_panic(expected = "Type not found after substitution")]
    fn expect_substitute_panics_on_missing() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Don't create the substituted type
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.f64());

        // This should panic
        arena.expect_substitute(arr_t, &subs, "test context");
    }

    #[test]
    fn expect_substitute_returns_existing() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let t = arena.type_param(name_id);
        let arr_t = arena.array(t);

        // Create the substituted type first
        let mut subs = FxHashMap::default();
        subs.insert(name_id, arena.string());
        let expected = arena.substitute(arr_t, &subs);

        // expect_substitute should return it
        let result = arena.expect_substitute(arr_t, &subs, "test context");
        assert_eq!(result, expected);
    }
}

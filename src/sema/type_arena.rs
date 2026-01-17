// src/sema/type_arena.rs
//
// Interned type system using TypeId handles for O(1) equality and minimal allocations.
//
// This module provides the canonical type representation for Vole's semantic analysis:
// - TypeId: u32 handle to an interned type (Copy, trivial Eq/Hash)
// - TypeArena: per-compilation storage with automatic deduplication
// - SemaType: the canonical type representation using TypeId for child types

use hashbrown::HashMap;
use smallvec::SmallVec;

use crate::identity::{ModuleId, NameId, TypeDefId, TypeParamId};
use crate::sema::types::{ConstantValue, LegacyType, PlaceholderKind, PrimitiveType};

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

    /// First non-reserved TypeId index (for dynamic types)
    pub const FIRST_DYNAMIC: u32 = 19;

    /// Get the raw index (for debugging/serialization)
    pub fn index(self) -> u32 {
        self.0
    }

    /// Check if this is a reserved (primitive/special) TypeId
    #[inline]
    pub fn is_reserved(self) -> bool {
        self.0 < Self::FIRST_DYNAMIC
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
    pub constants: std::collections::HashMap<NameId, ConstantValue>,
    /// Functions implemented via FFI rather than Vole code
    pub external_funcs: std::collections::HashSet<NameId>,
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
pub struct TypeArena {
    /// Interned types, indexed by TypeId
    types: Vec<SemaType>,
    /// Deduplication map - hashbrown for better perf
    intern_map: HashMap<SemaType, TypeId>,
    /// Pre-interned primitives for O(1) access
    pub primitives: PrimitiveTypes,
    /// Module metadata (constants, external_funcs) keyed by ModuleId.
    /// This data is not part of the type identity, but needed by codegen.
    module_metadata: std::collections::HashMap<ModuleId, ModuleMetadata>,
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
            intern_map: HashMap::new(),
            module_metadata: std::collections::HashMap::new(),
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

    /// Create a union type from variants
    pub fn union(&mut self, variants: impl Into<TypeIdVec>) -> TypeId {
        let variants = variants.into();
        // Propagate invalid
        if variants.iter().any(|&v| self.is_invalid(v)) {
            return self.invalid();
        }
        self.intern(SemaType::Union(variants))
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

    /// Create a function type
    pub fn function(
        &mut self,
        params: impl Into<TypeIdVec>,
        ret: TypeId,
        is_closure: bool,
    ) -> TypeId {
        let params = params.into();
        if params.iter().any(|&p| self.is_invalid(p)) || self.is_invalid(ret) {
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
    pub fn is_numeric(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Primitive(p) => p.is_numeric(),
            _ => false,
        }
    }

    /// Check if this is an integer type
    pub fn is_integer(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Primitive(p) => p.is_integer(),
            _ => false,
        }
    }

    /// Check if this is a floating point type
    pub fn is_float(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Primitive(p) => p.is_float(),
            _ => false,
        }
    }

    /// Check if this is a signed integer type
    pub fn is_signed(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Primitive(p) => p.is_signed(),
            _ => false,
        }
    }

    /// Check if this is an unsigned integer type
    pub fn is_unsigned(&self, id: TypeId) -> bool {
        match self.get(id) {
            SemaType::Primitive(p) => p.is_unsigned(),
            _ => false,
        }
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

    /// Check if this is a fixed array type
    pub fn is_fixed_array(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::FixedArray { .. })
    }

    /// Check if this is a function type
    pub fn is_function(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Function { .. })
    }

    /// Check if this is a closure (function with is_closure=true)
    pub fn is_closure(&self, id: TypeId) -> bool {
        matches!(
            self.get(id),
            SemaType::Function {
                is_closure: true,
                ..
            }
        )
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

    /// Check if this is a tuple type
    pub fn is_tuple(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Tuple(_))
    }

    /// Check if this is the string primitive
    pub fn is_string(&self, id: TypeId) -> bool {
        id == self.primitives.string
    }

    /// Check if this is nil
    pub fn is_nil(&self, id: TypeId) -> bool {
        id == self.primitives.nil
    }

    /// Check if this is void
    pub fn is_void(&self, id: TypeId) -> bool {
        id == self.primitives.void
    }

    /// Check if this is a runtime iterator type
    pub fn is_runtime_iterator(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::RuntimeIterator(_))
    }

    /// Check if this is a fallible type
    pub fn is_fallible(&self, id: TypeId) -> bool {
        matches!(self.get(id), SemaType::Fallible { .. })
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

    /// Display a type for error messages (basic version without name resolution)
    pub fn display_basic(&self, id: TypeId) -> String {
        match self.get(id) {
            SemaType::Primitive(p) => p.name().to_string(),
            SemaType::Void => "void".to_string(),
            SemaType::Nil => "nil".to_string(),
            SemaType::Done => "Done".to_string(),
            SemaType::Range => "range".to_string(),
            SemaType::MetaType => "type".to_string(),
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
    pub fn substitute(&mut self, ty: TypeId, subs: &HashMap<NameId, TypeId>) -> TypeId {
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
            | SemaType::Invalid { .. }
            | SemaType::Error { .. }
            | SemaType::Module(_)
            | SemaType::Placeholder(_) => ty,
        }
    }

    // ========================================================================
    // Bridge methods for incremental migration
    // TEMPORARY: These will be deleted in Phase 5 of the TypeArena refactor
    // ========================================================================

    /// Convert a legacy Type to a TypeId.
    ///
    /// TEMPORARY: For migration only, delete in Phase 5.
    /// This allows existing code to continue using LegacyType while we incrementally
    /// migrate to TypeId throughout the codebase.
    pub fn from_type(&mut self, ty: &LegacyType) -> TypeId {
        use crate::sema::types::NominalType;

        match ty {
            LegacyType::Primitive(p) => self.primitive(*p),
            LegacyType::Void => self.void(),
            LegacyType::Nil => self.nil(),
            LegacyType::Done => self.done(),
            LegacyType::Range => self.range(),
            LegacyType::MetaType => self.metatype(),
            LegacyType::Invalid(_) => self.invalid(),

            LegacyType::Array(elem) => {
                let elem_id = self.from_type(elem);
                self.array(elem_id)
            }

            LegacyType::Union(variants) => {
                let variant_ids: TypeIdVec = variants.iter().map(|v| self.from_type(v)).collect();
                self.union(variant_ids)
            }

            LegacyType::Tuple(elements) => {
                let elem_ids: TypeIdVec = elements.iter().map(|e| self.from_type(e)).collect();
                self.tuple(elem_ids)
            }

            LegacyType::FixedArray { element, size } => {
                let elem_id = self.from_type(element);
                self.fixed_array(elem_id, *size)
            }

            LegacyType::RuntimeIterator(elem) => {
                let elem_id = self.from_type(elem);
                self.runtime_iterator(elem_id)
            }

            LegacyType::Function(ft) => {
                let param_ids: TypeIdVec = ft.params.iter().map(|p| self.from_type(p)).collect();
                let ret_id = self.from_type(&ft.return_type);
                self.function(param_ids, ret_id, ft.is_closure)
            }

            LegacyType::Nominal(NominalType::Class(c)) => {
                self.class(c.type_def_id, c.type_args_id.clone())
            }

            LegacyType::Nominal(NominalType::Record(r)) => {
                self.record(r.type_def_id, r.type_args_id.clone())
            }

            LegacyType::Nominal(NominalType::Interface(i)) => {
                self.interface(i.type_def_id, i.type_args_id.clone())
            }

            LegacyType::Nominal(NominalType::Error(e)) => self.error_type(e.type_def_id),

            LegacyType::TypeParam(name_id) => self.type_param(*name_id),

            LegacyType::TypeParamRef(param_id) => self.type_param_ref(*param_id),

            LegacyType::Module(module_type) => {
                // Convert exports to (NameId, TypeId) pairs
                let exports: SmallVec<[(NameId, TypeId); 8]> = module_type
                    .exports
                    .iter()
                    .map(|(name_id, ty)| (*name_id, self.from_type(ty)))
                    .collect();

                // Register module metadata (constants, external_funcs)
                let metadata = ModuleMetadata {
                    constants: module_type.constants.clone(),
                    external_funcs: module_type.external_funcs.clone(),
                };
                self.register_module_metadata(module_type.module_id, metadata);

                self.module(module_type.module_id, exports)
            }

            LegacyType::Placeholder(kind) => self.placeholder(kind.clone()),

            LegacyType::Fallible(ft) => {
                let success_id = self.from_type(&ft.success_type);
                let error_id = self.from_type(&ft.error_type);
                self.fallible(success_id, error_id)
            }

            LegacyType::Structural(st) => {
                let fields: SmallVec<[(NameId, TypeId); 4]> = st
                    .fields
                    .iter()
                    .map(|f| (f.name, self.from_type(&f.ty)))
                    .collect();
                let methods: SmallVec<[InternedStructuralMethod; 2]> = st
                    .methods
                    .iter()
                    .map(|m| InternedStructuralMethod {
                        name: m.name,
                        params: m.params.iter().map(|p| self.from_type(p)).collect(),
                        return_type: self.from_type(&m.return_type),
                    })
                    .collect();
                self.structural(fields, methods)
            }
        }
    }

    /// Convert a TypeId back to a legacy Type.
    ///
    /// TEMPORARY: For migration only, delete in Phase 5.
    /// This allows existing code to continue using LegacyType while we incrementally
    /// migrate to TypeId throughout the codebase.
    pub fn to_type(&self, id: TypeId) -> LegacyType {
        use crate::sema::types::{
            ClassType, ErrorTypeInfo, FunctionType, InterfaceType, ModuleType, NominalType,
            RecordType,
        };

        match self.get(id) {
            SemaType::Primitive(p) => LegacyType::Primitive(*p),
            SemaType::Void => LegacyType::Void,
            SemaType::Nil => LegacyType::Nil,
            SemaType::Done => LegacyType::Done,
            SemaType::Range => LegacyType::Range,
            SemaType::MetaType => LegacyType::MetaType,
            SemaType::Invalid { kind } => LegacyType::invalid(kind),

            SemaType::Array(elem) => LegacyType::Array(Box::new(self.to_type(*elem))),

            SemaType::Union(variants) => {
                let types: Vec<LegacyType> = variants.iter().map(|&v| self.to_type(v)).collect();
                LegacyType::Union(types.into())
            }

            SemaType::Tuple(elements) => {
                let types: Vec<LegacyType> = elements.iter().map(|&e| self.to_type(e)).collect();
                LegacyType::Tuple(types.into())
            }

            SemaType::FixedArray { element, size } => LegacyType::FixedArray {
                element: Box::new(self.to_type(*element)),
                size: *size,
            },

            SemaType::RuntimeIterator(elem) => {
                LegacyType::RuntimeIterator(Box::new(self.to_type(*elem)))
            }

            SemaType::Function {
                params,
                ret,
                is_closure,
            } => {
                let param_types: Vec<LegacyType> =
                    params.iter().map(|&p| self.to_type(p)).collect();
                LegacyType::Function(FunctionType {
                    params: param_types.into(),
                    return_type: Box::new(self.to_type(*ret)),
                    is_closure: *is_closure,
                    params_id: None,
                    return_type_id: None,
                })
            }

            SemaType::Class {
                type_def_id,
                type_args,
            } => LegacyType::Nominal(NominalType::Class(ClassType {
                type_def_id: *type_def_id,
                type_args_id: type_args.clone(),
            })),

            SemaType::Record {
                type_def_id,
                type_args,
            } => LegacyType::Nominal(NominalType::Record(RecordType {
                type_def_id: *type_def_id,
                type_args_id: type_args.clone(),
            })),

            SemaType::Interface {
                type_def_id,
                type_args,
            } => {
                // Note: We lose methods/extends info here - this is a limitation of
                // storing types by TypeDefId only. For full interface type, lookup
                // from EntityRegistry is needed.
                LegacyType::Nominal(NominalType::Interface(InterfaceType {
                    type_def_id: *type_def_id,
                    type_args_id: type_args.clone(),
                    methods: vec![].into(),
                    extends: vec![].into(),
                }))
            }

            SemaType::Error { type_def_id } => {
                LegacyType::Nominal(NominalType::Error(ErrorTypeInfo {
                    type_def_id: *type_def_id,
                }))
            }

            SemaType::TypeParam(name_id) => LegacyType::TypeParam(*name_id),

            SemaType::TypeParamRef(param_id) => LegacyType::TypeParamRef(*param_id),

            SemaType::Module(m) => {
                // Reconstruct exports from interned types
                let exports_map: std::collections::HashMap<NameId, LegacyType> = m
                    .exports
                    .iter()
                    .map(|(name_id, type_id)| (*name_id, self.to_type(*type_id)))
                    .collect();

                // Get metadata (constants, external_funcs) from arena storage
                let metadata = self.module_metadata(m.module_id);
                let (constants, external_funcs) = match metadata {
                    Some(meta) => (meta.constants.clone(), meta.external_funcs.clone()),
                    None => (
                        std::collections::HashMap::new(),
                        std::collections::HashSet::new(),
                    ),
                };

                LegacyType::Module(ModuleType {
                    module_id: m.module_id,
                    exports: exports_map,
                    constants,
                    external_funcs,
                })
            }

            SemaType::Fallible { success, error } => {
                use crate::sema::types::FallibleType;
                LegacyType::Fallible(FallibleType {
                    success_type: Box::new(self.to_type(*success)),
                    error_type: Box::new(self.to_type(*error)),
                })
            }

            SemaType::Structural(st) => {
                use crate::sema::types::{
                    StructuralFieldType, StructuralMethodType, StructuralType,
                };
                LegacyType::Structural(StructuralType {
                    fields: st
                        .fields
                        .iter()
                        .map(|(name, ty)| StructuralFieldType {
                            name: *name,
                            ty: self.to_type(*ty),
                        })
                        .collect(),
                    methods: st
                        .methods
                        .iter()
                        .map(|m| StructuralMethodType {
                            name: m.name,
                            params: m.params.iter().map(|&p| self.to_type(p)).collect(),
                            return_type: self.to_type(m.return_type),
                        })
                        .collect(),
                })
            }

            SemaType::Placeholder(kind) => LegacyType::Placeholder(kind.clone()),
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

        let mut subs = HashMap::new();
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

        let mut subs = HashMap::new();
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

        let mut subs = HashMap::new();
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
        let empty_subs: HashMap<NameId, TypeId> = HashMap::new();

        let result = arena.substitute(arr, &empty_subs);
        assert_eq!(result, arr); // Exact same TypeId
    }

    #[test]
    fn substitute_unchanged_returns_interned() {
        let mut arena = TypeArena::new();
        let _name_id = NameId::new_for_test(999);
        let other_id = NameId::new_for_test(888);

        let arr = arena.array(arena.i32()); // No type params

        let mut subs = HashMap::new();
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

        let mut subs = HashMap::new();
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

        let mut subs = HashMap::new();
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

        let mut subs = HashMap::new();
        subs.insert(t_id, arena.bool());

        let result = arena.substitute(outer_arr, &subs);

        // Should be Array<Array<bool>>
        let inner = arena.unwrap_array(result).unwrap();
        let innermost = arena.unwrap_array(inner).unwrap();
        assert_eq!(innermost, arena.bool());
    }

    // ========================================================================
    // Phase 2.1 tests: Bridge methods (Type <-> TypeId)
    // ========================================================================

    #[test]
    fn bridge_roundtrip_primitives() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original = LegacyType::Primitive(PrimitiveType::I32);
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);

        // Test other primitives
        let string_type = LegacyType::Primitive(PrimitiveType::String);
        let string_id = arena.from_type(&string_type);
        assert_eq!(arena.to_type(string_id), string_type);

        let bool_type = LegacyType::Primitive(PrimitiveType::Bool);
        let bool_id = arena.from_type(&bool_type);
        assert_eq!(arena.to_type(bool_id), bool_type);
    }

    #[test]
    fn bridge_roundtrip_special_types() {
        let mut arena = TypeArena::new();

        // Void
        let void = LegacyType::Void;
        let void_id = arena.from_type(&void);
        assert_eq!(arena.to_type(void_id), void);

        // Nil
        let nil = LegacyType::Nil;
        let nil_id = arena.from_type(&nil);
        assert_eq!(arena.to_type(nil_id), nil);

        // Done
        let done = LegacyType::Done;
        let done_id = arena.from_type(&done);
        assert_eq!(arena.to_type(done_id), done);

        // Range
        let range = LegacyType::Range;
        let range_id = arena.from_type(&range);
        assert_eq!(arena.to_type(range_id), range);

        // Type (metatype)
        let metatype = LegacyType::MetaType;
        let metatype_id = arena.from_type(&metatype);
        assert_eq!(arena.to_type(metatype_id), metatype);
    }

    #[test]
    fn bridge_roundtrip_array() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original = LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::String)));
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_union() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original = LegacyType::Union(
            vec![LegacyType::Primitive(PrimitiveType::I32), LegacyType::Nil].into(),
        );
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_tuple() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original = LegacyType::Tuple(
            vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::String),
                LegacyType::Primitive(PrimitiveType::Bool),
            ]
            .into(),
        );
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_function() {
        use crate::sema::types::{FunctionType, PrimitiveType};

        let mut arena = TypeArena::new();
        let original = LegacyType::Function(FunctionType {
            params: vec![LegacyType::Primitive(PrimitiveType::I32)].into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::String)),
            is_closure: false,
            params_id: None,
            return_type_id: None,
        });
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);

        // Test with closure flag
        let closure = LegacyType::Function(FunctionType {
            params: vec![].into(),
            return_type: Box::new(LegacyType::Void),
            is_closure: true,
            params_id: None,
            return_type_id: None,
        });
        let closure_id = arena.from_type(&closure);
        let closure_back = arena.to_type(closure_id);
        assert_eq!(closure, closure_back);
    }

    #[test]
    fn bridge_roundtrip_class() {
        use crate::sema::types::{ClassType, NominalType, PrimitiveType};

        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(42);
        // Create type args with consistent LegacyType and TypeId representations
        let type_args_legacy = vec![LegacyType::Primitive(PrimitiveType::I32)];
        let type_args_id: TypeIdVec = type_args_legacy
            .iter()
            .map(|t| arena.from_type(t))
            .collect();
        let original = LegacyType::Nominal(NominalType::Class(ClassType {
            type_def_id,
            type_args_id,
        }));
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_record() {
        use crate::sema::types::{NominalType, PrimitiveType, RecordType};

        let mut arena = TypeArena::new();
        let type_def_id = TypeDefId::new(123);
        // Create type args
        let type_args_legacy = vec![
            LegacyType::Primitive(PrimitiveType::String),
            LegacyType::Primitive(PrimitiveType::Bool),
        ];
        let type_args_id: TypeIdVec = type_args_legacy
            .iter()
            .map(|t| arena.from_type(t))
            .collect();
        let original = LegacyType::Nominal(NominalType::Record(RecordType {
            type_def_id,
            type_args_id,
        }));
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_fixed_array() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original = LegacyType::FixedArray {
            element: Box::new(LegacyType::Primitive(PrimitiveType::I32)),
            size: 10,
        };
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_runtime_iterator() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let original =
            LegacyType::RuntimeIterator(Box::new(LegacyType::Primitive(PrimitiveType::String)));
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_roundtrip_type_param() {
        let mut arena = TypeArena::new();
        let name_id = NameId::new_for_test(999);
        let original = LegacyType::TypeParam(name_id);
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }

    #[test]
    fn bridge_interning_via_from_type() {
        use crate::sema::types::PrimitiveType;

        let mut arena = TypeArena::new();
        let ty1 = LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::I32)));
        let ty2 = LegacyType::Array(Box::new(LegacyType::Primitive(PrimitiveType::I32)));

        let id1 = arena.from_type(&ty1);
        let id2 = arena.from_type(&ty2);

        // Same types should get same TypeId
        assert_eq!(id1, id2);
    }

    #[test]
    fn bridge_nested_complex_type() {
        use crate::sema::types::{FunctionType, PrimitiveType};

        let mut arena = TypeArena::new();

        // Array<(i32, string) -> bool>
        let func = LegacyType::Function(FunctionType {
            params: vec![
                LegacyType::Primitive(PrimitiveType::I32),
                LegacyType::Primitive(PrimitiveType::String),
            ]
            .into(),
            return_type: Box::new(LegacyType::Primitive(PrimitiveType::Bool)),
            is_closure: false,
            params_id: None,
            return_type_id: None,
        });
        let original = LegacyType::Array(Box::new(func));

        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }
}

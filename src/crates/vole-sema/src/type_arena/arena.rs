// type_arena/arena.rs
//
// TypeArena: per-compilation type storage with interning, primitive registration,
// and compound type builders.

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;

use crate::types::{PlaceholderKind, PrimitiveType};
use vole_identity::{ModuleId, NameId, TypeDefId, TypeParamId};

use super::sema_type::*;
use super::type_id::{TypeId, TypeIdVec};

/// Macro for defining primitive TypeId fields and accessors with a single source of truth.
/// Each entry defines the field name used in PrimitiveTypes and the corresponding accessor.
macro_rules! define_primitive_types {
    ($($name:ident),* $(,)?) => {
        /// Pre-interned primitive and common types for O(1) access
        #[derive(Debug, Clone, Copy)]
        pub struct PrimitiveTypes {
            $(pub $name: TypeId),*
        }

        impl PrimitiveTypes {
            /// Initialize all fields to a placeholder value
            fn placeholder() -> Self {
                Self {
                    $($name: TypeId::INVALID),*
                }
            }
        }

        // Generate accessor methods for TypeArena
        impl TypeArena {
            $(
                pub fn $name(&self) -> TypeId {
                    self.primitives.$name
                }
            )*
        }
    };
}

// Define all TypeId-based primitives (20 types)
// Note: never and unknown are handled specially as they return TypeId constants directly
define_primitive_types!(
    // Signed integers
    i8, i16, i32, i64, i128, // Unsigned integers
    u8, u16, u32, u64, // Floating point
    f32, f64, // Other primitives
    bool, string, // Opaque handle type
    handle, // Special types
    void, nil, done, range, metatype, invalid
);

/// Per-compilation type arena with automatic interning/deduplication.
#[derive(Clone)]
pub struct TypeArena {
    /// Interned types, indexed by TypeId
    pub(super) types: Vec<SemaType>,
    /// Deduplication map - FxHashMap for better perf with small keys
    pub(super) intern_map: FxHashMap<SemaType, TypeId>,
    /// Pre-interned primitives for O(1) access
    pub primitives: PrimitiveTypes,
    /// Module metadata (constants, external_funcs) keyed by ModuleId.
    /// This data is not part of the type identity, but needed by codegen.
    module_metadata: FxHashMap<ModuleId, ModuleMetadata>,
    /// TypeIds that are sentinel types (e.g., nil, Done, user-defined sentinels).
    /// Sentinels are zero-field struct types that should not be treated as regular structs
    /// for codegen purposes (auto-boxing, field access, etc.).
    pub(super) sentinel_ids: FxHashSet<TypeId>,
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
            sentinel_ids: FxHashSet::default(),
            // Temporary placeholders - will be filled in below
            primitives: PrimitiveTypes::placeholder(),
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

        arena.primitives.handle = arena.intern(SemaType::Handle);
        debug_assert_eq!(arena.primitives.handle, TypeId::HANDLE);

        arena.primitives.void = arena.intern(SemaType::Void);
        debug_assert_eq!(arena.primitives.void, TypeId::VOID);
        // Nil and Done are placeholder slots that get rebound to sentinel struct types
        // when the prelude loads. We use a unique Invalid variant for each so they don't
        // collide with each other or with Void in the intern map.
        arena.primitives.nil = arena.intern(SemaType::Invalid {
            kind: "nil_placeholder",
        });
        debug_assert_eq!(arena.primitives.nil, TypeId::NIL);
        arena.primitives.done = arena.intern(SemaType::Invalid {
            kind: "done_placeholder",
        });
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
    pub(super) fn intern(&mut self, ty: SemaType) -> TypeId {
        let next_id = TypeId::from_raw(self.types.len() as u32);
        *self.intern_map.entry(ty.clone()).or_insert_with(|| {
            self.types.push(ty);
            next_id
        })
    }

    /// Replace the SemaType at a reserved TypeId slot.
    ///
    /// Used during prelude loading to rebind well-known types (Done, nil) from their
    /// initial placeholder SemaType variants to actual sentinel struct types. This ensures
    /// the reserved TypeId constants (e.g., TypeId::DONE, TypeId::NIL) point to the
    /// sentinel's struct type after prelude loading.
    ///
    /// Updates both the type storage and intern map to maintain consistency.
    pub fn rebind(&mut self, type_id: TypeId, new_type: SemaType) {
        let idx = type_id.raw() as usize;
        assert!(idx < self.types.len(), "rebind: TypeId out of range");

        // Remove the old type from the intern map
        let old_type = self.types[idx].clone();
        self.intern_map.remove(&old_type);

        // Insert the new type into the intern map pointing to the same TypeId
        self.intern_map.insert(new_type.clone(), type_id);

        // Replace the type in the storage
        self.types[idx] = new_type;
    }

    /// Get the SemaType for a TypeId
    pub fn get(&self, id: TypeId) -> &SemaType {
        &self.types[id.raw() as usize]
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
    // Special type accessors (not covered by the define_primitive_types macro)
    // ========================================================================

    pub fn never(&self) -> TypeId {
        TypeId::NEVER
    }
    pub fn unknown(&self) -> TypeId {
        TypeId::UNKNOWN
    }

    /// Get TypeId for a PrimitiveType enum variant
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

    /// Stable sort key for union variants.
    ///
    /// Returns a numeric key that produces a deterministic ordering:
    ///   - Higher values appear earlier (used with Reverse)
    ///   - Value types (primitives, compounds) > Nominal types (by TypeDefId) > Sentinels
    ///
    /// Uses numeric TypeDefId comparison instead of string-based Debug formatting,
    /// avoiding issues when TypeDefId indices cross digit boundaries (e.g., 99 vs 100).
    pub(super) fn union_sort_key(&self, type_id: TypeId) -> (u32, u64) {
        // No special sorting for sentinels - they are SemaType::Struct internally and sort
        // alongside other nominal types using (50, type_def_id.index()).
        match self.get(type_id) {
            // Value types get highest category
            SemaType::Primitive(_) => (100, type_id.raw() as u64),
            SemaType::Array(_) | SemaType::FixedArray { .. } => (90, type_id.raw() as u64),
            SemaType::Tuple(_) => (85, type_id.raw() as u64),
            SemaType::Function { .. } => (80, type_id.raw() as u64),
            SemaType::Fallible { .. } => (75, type_id.raw() as u64),
            SemaType::RuntimeIterator(_) => (70, type_id.raw() as u64),
            SemaType::Structural(_) => (65, type_id.raw() as u64),
            // Nominal types sorted by TypeDefId (descending) within category
            SemaType::Class { type_def_id, .. }
            | SemaType::Struct { type_def_id, .. }
            | SemaType::Interface { type_def_id, .. }
            | SemaType::Error { type_def_id } => (50, type_def_id.index() as u64),
            // Type params
            SemaType::TypeParam(_) | SemaType::TypeParamRef(_) => (40, type_id.raw() as u64),
            // Module types
            SemaType::Module(_) => (35, type_id.raw() as u64),
            SemaType::Handle => (60, 0),
            SemaType::Void => (5, 0),
            SemaType::Range => (4, 0),
            SemaType::MetaType => (3, 0),
            // Placeholder and special
            SemaType::Placeholder(_) => (2, type_id.raw() as u64),
            SemaType::Never => (1, 0),
            SemaType::Unknown => (0, 0),
            // Union and Invalid shouldn't appear in union variants, but handle gracefully
            SemaType::Union(_) => (0, type_id.raw() as u64),
            SemaType::Invalid { .. } => (0, 0),
        }
    }

    /// Create a union type from variants.
    /// Normalizes: flattens nested unions, sorts descending (value types before sentinels), dedupes.
    ///
    /// Lattice simplification rules:
    /// - `never | T` -> `T` (never is the bottom type, disappears from unions)
    /// - `unknown | T` -> `unknown` (unknown is the top type, absorbs everything)
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
        for &v in &variants {
            if let SemaType::Union(inner) = self.get(v) {
                flattened.extend(inner.iter().copied());
            } else {
                flattened.push(v);
            }
        }

        // Lattice simplification: unknown absorbs everything
        if flattened.iter().any(|&v| v.is_unknown()) {
            return TypeId::UNKNOWN;
        }

        // Lattice simplification: never disappears from unions
        flattened.retain(|&v| !v.is_never());

        // If all variants were never, return never
        if flattened.is_empty() {
            return TypeId::NEVER;
        }

        // Sort descending using a stable numeric sort key.
        // Each SemaType variant gets a category number (higher = earlier in union):
        //   Primitives/compound > Named types (by TypeDefId desc) > Sentinels
        // This ensures union order is deterministic regardless of Debug string formatting.
        flattened.sort_by_cached_key(|&v| std::cmp::Reverse(self.union_sort_key(v)));

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

    /// Create a struct type
    pub fn struct_type(
        &mut self,
        type_def_id: TypeDefId,
        type_args: impl Into<TypeIdVec>,
    ) -> TypeId {
        let type_args = type_args.into();
        if type_args.iter().any(|&a| self.is_invalid(a)) {
            return self.invalid();
        }
        self.intern(SemaType::Struct {
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
}

impl Default for TypeArena {
    fn default() -> Self {
        Self::new()
    }
}

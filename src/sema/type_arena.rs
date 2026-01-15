// src/sema/type_arena.rs
//
// Interned type system using TypeId handles for O(1) equality and minimal allocations.
//
// This module replaces the old Type enum with an arena-based interning system:
// - TypeId: u32 handle to an interned type (Copy, trivial Eq/Hash)
// - TypeArena: per-compilation storage with automatic deduplication
// - InternedType: internal storage using SmallVec for child types

use hashbrown::HashMap;
use smallvec::SmallVec;

use crate::identity::{ModuleId, NameId, TypeDefId, TypeParamId};
use crate::sema::types::{LegacyType, PlaceholderKind, PrimitiveType};

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
    /// Get the raw index (for debugging/serialization)
    pub fn index(self) -> u32 {
        self.0
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

/// Internal representation of interned types.
///
/// Note: Uses TypeId for children instead of recursive Type references,
/// which allows SmallVec to work (no infinite-size type issue).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InternedType {
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

    // Module type
    Module(ModuleId),

    // Fallible type: fallible(T, E) - result-like type
    Fallible {
        success: TypeId,
        error: TypeId,
    },

    // Structural type: duck typing constraint
    // e.g., { name: string, func greet() -> string }
    // Note: Boxed to keep InternedType size small
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
    types: Vec<InternedType>,
    /// Deduplication map - hashbrown for better perf
    intern_map: HashMap<InternedType, TypeId>,
    /// Pre-interned primitives for O(1) access
    pub primitives: PrimitiveTypes,
}

impl TypeArena {
    /// Create a new TypeArena with pre-interned primitive types
    pub fn new() -> Self {
        let mut arena = Self {
            types: Vec::new(),
            intern_map: HashMap::new(),
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

        // Pre-intern all primitive types
        // Invalid must be first (index 0) for is_invalid() check
        arena.primitives.invalid = arena.intern(InternedType::Invalid { kind: "invalid" });
        debug_assert_eq!(arena.primitives.invalid.0, 0);

        arena.primitives.i8 = arena.intern(InternedType::Primitive(PrimitiveType::I8));
        arena.primitives.i16 = arena.intern(InternedType::Primitive(PrimitiveType::I16));
        arena.primitives.i32 = arena.intern(InternedType::Primitive(PrimitiveType::I32));
        arena.primitives.i64 = arena.intern(InternedType::Primitive(PrimitiveType::I64));
        arena.primitives.i128 = arena.intern(InternedType::Primitive(PrimitiveType::I128));
        arena.primitives.u8 = arena.intern(InternedType::Primitive(PrimitiveType::U8));
        arena.primitives.u16 = arena.intern(InternedType::Primitive(PrimitiveType::U16));
        arena.primitives.u32 = arena.intern(InternedType::Primitive(PrimitiveType::U32));
        arena.primitives.u64 = arena.intern(InternedType::Primitive(PrimitiveType::U64));
        arena.primitives.f32 = arena.intern(InternedType::Primitive(PrimitiveType::F32));
        arena.primitives.f64 = arena.intern(InternedType::Primitive(PrimitiveType::F64));
        arena.primitives.bool = arena.intern(InternedType::Primitive(PrimitiveType::Bool));
        arena.primitives.string = arena.intern(InternedType::Primitive(PrimitiveType::String));
        arena.primitives.void = arena.intern(InternedType::Void);
        arena.primitives.nil = arena.intern(InternedType::Nil);
        arena.primitives.done = arena.intern(InternedType::Done);
        arena.primitives.range = arena.intern(InternedType::Range);
        arena.primitives.metatype = arena.intern(InternedType::MetaType);

        arena
    }

    /// Intern a type, returning existing TypeId if already interned
    fn intern(&mut self, ty: InternedType) -> TypeId {
        let next_id = TypeId(self.types.len() as u32);
        *self.intern_map.entry(ty.clone()).or_insert_with(|| {
            self.types.push(ty);
            next_id
        })
    }

    /// Get the InternedType for a TypeId
    pub fn get(&self, id: TypeId) -> &InternedType {
        &self.types[id.0 as usize]
    }

    /// Check if a TypeId is the invalid type
    pub fn is_invalid(&self, id: TypeId) -> bool {
        id.0 == 0 // Invalid is always at index 0
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
        self.intern(InternedType::Union(variants))
    }

    /// Create a tuple type from elements
    pub fn tuple(&mut self, elements: impl Into<TypeIdVec>) -> TypeId {
        let elements = elements.into();
        if elements.iter().any(|&e| self.is_invalid(e)) {
            return self.invalid();
        }
        self.intern(InternedType::Tuple(elements))
    }

    /// Create an array type
    pub fn array(&mut self, element: TypeId) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(InternedType::Array(element))
    }

    /// Create a fixed-size array type
    pub fn fixed_array(&mut self, element: TypeId, size: usize) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(InternedType::FixedArray { element, size })
    }

    /// Create a runtime iterator type
    pub fn runtime_iterator(&mut self, element: TypeId) -> TypeId {
        if self.is_invalid(element) {
            return self.invalid();
        }
        self.intern(InternedType::RuntimeIterator(element))
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
        self.intern(InternedType::Function {
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
        self.intern(InternedType::Class {
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
        self.intern(InternedType::Record {
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
        self.intern(InternedType::Interface {
            type_def_id,
            type_args,
        })
    }

    /// Create an error type
    pub fn error_type(&mut self, type_def_id: TypeDefId) -> TypeId {
        self.intern(InternedType::Error { type_def_id })
    }

    /// Create a type parameter placeholder
    pub fn type_param(&mut self, name_id: NameId) -> TypeId {
        self.intern(InternedType::TypeParam(name_id))
    }

    /// Create a type parameter reference
    pub fn type_param_ref(&mut self, type_param_id: TypeParamId) -> TypeId {
        self.intern(InternedType::TypeParamRef(type_param_id))
    }

    /// Create a module type
    pub fn module(&mut self, module_id: ModuleId) -> TypeId {
        self.intern(InternedType::Module(module_id))
    }

    /// Create a fallible type: fallible(success, error)
    pub fn fallible(&mut self, success: TypeId, error: TypeId) -> TypeId {
        if self.is_invalid(success) || self.is_invalid(error) {
            return self.invalid();
        }
        self.intern(InternedType::Fallible { success, error })
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
        self.intern(InternedType::Structural(Box::new(InternedStructural {
            fields,
            methods,
        })))
    }

    /// Create a placeholder type (for inference)
    pub fn placeholder(&mut self, kind: PlaceholderKind) -> TypeId {
        self.intern(InternedType::Placeholder(kind))
    }

    // ========================================================================
    // Query methods - predicates and unwrap helpers
    // ========================================================================

    /// Check if this is a numeric type (can do arithmetic)
    pub fn is_numeric(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Primitive(p) => p.is_numeric(),
            _ => false,
        }
    }

    /// Check if this is an integer type
    pub fn is_integer(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Primitive(p) => p.is_integer(),
            _ => false,
        }
    }

    /// Check if this is a floating point type
    pub fn is_float(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Primitive(p) => p.is_float(),
            _ => false,
        }
    }

    /// Check if this is a signed integer type
    pub fn is_signed(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Primitive(p) => p.is_signed(),
            _ => false,
        }
    }

    /// Check if this is an unsigned integer type
    pub fn is_unsigned(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Primitive(p) => p.is_unsigned(),
            _ => false,
        }
    }

    /// Check if this is an optional type (union containing nil)
    pub fn is_optional(&self, id: TypeId) -> bool {
        match self.get(id) {
            InternedType::Union(variants) => variants.contains(&self.nil()),
            _ => false,
        }
    }

    /// Unwrap an array type, returning the element type
    pub fn unwrap_array(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            InternedType::Array(elem) => Some(*elem),
            _ => None,
        }
    }

    /// Unwrap an optional type, returning the non-nil type
    pub fn unwrap_optional(&self, id: TypeId) -> Option<TypeId> {
        match self.get(id) {
            InternedType::Union(variants) => {
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
            InternedType::Function {
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
            InternedType::Tuple(elements) => Some(elements),
            _ => None,
        }
    }

    /// Unwrap a fixed array type, returning (element, size)
    pub fn unwrap_fixed_array(&self, id: TypeId) -> Option<(TypeId, usize)> {
        match self.get(id) {
            InternedType::FixedArray { element, size } => Some((*element, *size)),
            _ => None,
        }
    }

    /// Get TypeDefId for nominal types (class, record, interface, error)
    pub fn type_def_id(&self, id: TypeId) -> Option<TypeDefId> {
        match self.get(id) {
            InternedType::Class { type_def_id, .. } => Some(*type_def_id),
            InternedType::Record { type_def_id, .. } => Some(*type_def_id),
            InternedType::Interface { type_def_id, .. } => Some(*type_def_id),
            InternedType::Error { type_def_id } => Some(*type_def_id),
            _ => None,
        }
    }

    /// Get type arguments for generic types
    pub fn type_args(&self, id: TypeId) -> &[TypeId] {
        match self.get(id) {
            InternedType::Class { type_args, .. } => type_args,
            InternedType::Record { type_args, .. } => type_args,
            InternedType::Interface { type_args, .. } => type_args,
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

    /// Display a type for error messages (basic version without name resolution)
    pub fn display_basic(&self, id: TypeId) -> String {
        match self.get(id) {
            InternedType::Primitive(p) => p.name().to_string(),
            InternedType::Void => "void".to_string(),
            InternedType::Nil => "nil".to_string(),
            InternedType::Done => "Done".to_string(),
            InternedType::Range => "range".to_string(),
            InternedType::MetaType => "type".to_string(),
            InternedType::Invalid { kind } => format!("<invalid: {}>", kind),
            InternedType::Union(variants) => {
                let parts: Vec<String> = variants.iter().map(|&v| self.display_basic(v)).collect();
                parts.join(" | ")
            }
            InternedType::Tuple(elements) => {
                let parts: Vec<String> = elements.iter().map(|&e| self.display_basic(e)).collect();
                format!("[{}]", parts.join(", "))
            }
            InternedType::Array(elem) => format!("[{}]", self.display_basic(*elem)),
            InternedType::FixedArray { element, size } => {
                format!("[{}; {}]", self.display_basic(*element), size)
            }
            InternedType::RuntimeIterator(elem) => {
                format!("Iterator<{}>", self.display_basic(*elem))
            }
            InternedType::Function {
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
            InternedType::Class {
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
            InternedType::Record {
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
            InternedType::Interface {
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
            InternedType::Error { type_def_id } => format!("error#{}", type_def_id.index()),
            InternedType::TypeParam(name_id) => format!("TypeParam({:?})", name_id),
            InternedType::TypeParamRef(id) => format!("TypeParamRef#{}", id.index()),
            InternedType::Module(module_id) => format!("module#{}", module_id.index()),
            InternedType::Fallible { success, error } => {
                format!(
                    "fallible({}, {})",
                    self.display_basic(*success),
                    self.display_basic(*error)
                )
            }
            InternedType::Structural(st) => {
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
            InternedType::Placeholder(kind) => format!("{}", kind),
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
            InternedType::TypeParam(name_id) => subs.get(&name_id).copied().unwrap_or(ty),

            // TypeParamRef doesn't substitute based on NameId
            InternedType::TypeParamRef(_) => ty,

            // Recursive substitution for compound types
            InternedType::Array(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.array(new_elem)
            }

            InternedType::Union(variants) => {
                let new_variants: TypeIdVec =
                    variants.iter().map(|&v| self.substitute(v, subs)).collect();
                self.union(new_variants)
            }

            InternedType::Tuple(elements) => {
                let new_elements: TypeIdVec =
                    elements.iter().map(|&e| self.substitute(e, subs)).collect();
                self.tuple(new_elements)
            }

            InternedType::Function {
                params,
                ret,
                is_closure,
            } => {
                let new_params: TypeIdVec =
                    params.iter().map(|&p| self.substitute(p, subs)).collect();
                let new_ret = self.substitute(ret, subs);
                self.function(new_params, new_ret, is_closure)
            }

            InternedType::Class {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.class(type_def_id, new_args)
            }

            InternedType::Record {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.record(type_def_id, new_args)
            }

            InternedType::Interface {
                type_def_id,
                type_args,
            } => {
                let new_args: TypeIdVec = type_args
                    .iter()
                    .map(|&a| self.substitute(a, subs))
                    .collect();
                self.interface(type_def_id, new_args)
            }

            InternedType::RuntimeIterator(elem) => {
                let new_elem = self.substitute(elem, subs);
                self.runtime_iterator(new_elem)
            }

            InternedType::FixedArray { element, size } => {
                let new_elem = self.substitute(element, subs);
                self.fixed_array(new_elem, size)
            }

            InternedType::Fallible { success, error } => {
                let new_success = self.substitute(success, subs);
                let new_error = self.substitute(error, subs);
                self.fallible(new_success, new_error)
            }

            InternedType::Structural(st) => {
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
            InternedType::Primitive(_)
            | InternedType::Void
            | InternedType::Nil
            | InternedType::Done
            | InternedType::Range
            | InternedType::MetaType
            | InternedType::Invalid { .. }
            | InternedType::Error { .. }
            | InternedType::Module(_)
            | InternedType::Placeholder(_) => ty,
        }
    }

    // ========================================================================
    // Bridge methods for incremental migration
    // TEMPORARY: These will be deleted in Phase 5 of the TypeArena refactor
    // ========================================================================

    /// Convert a legacy Type to a TypeId.
    ///
    /// TEMPORARY: For migration only, delete in Phase 5.
    /// This allows existing code to continue using Type while we incrementally
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
                let arg_ids: TypeIdVec = c.type_args.iter().map(|a| self.from_type(a)).collect();
                self.class(c.type_def_id, arg_ids)
            }

            LegacyType::Nominal(NominalType::Record(r)) => {
                let arg_ids: TypeIdVec = r.type_args.iter().map(|a| self.from_type(a)).collect();
                self.record(r.type_def_id, arg_ids)
            }

            LegacyType::Nominal(NominalType::Interface(i)) => {
                let arg_ids: TypeIdVec = i.type_args.iter().map(|a| self.from_type(a)).collect();
                self.interface(i.type_def_id, arg_ids)
            }

            LegacyType::Nominal(NominalType::Error(e)) => self.error_type(e.type_def_id),

            LegacyType::TypeParam(name_id) => self.type_param(*name_id),

            LegacyType::TypeParamRef(param_id) => self.type_param_ref(*param_id),

            LegacyType::Module(module_type) => self.module(module_type.module_id),

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
    /// This allows existing code to continue using Type while we incrementally
    /// migrate to TypeId throughout the codebase.
    pub fn to_type(&self, id: TypeId) -> LegacyType {
        use crate::sema::types::{
            ClassType, ErrorTypeInfo, FunctionType, InterfaceType, ModuleType, NominalType,
            RecordType,
        };

        match self.get(id) {
            InternedType::Primitive(p) => LegacyType::Primitive(*p),
            InternedType::Void => LegacyType::Void,
            InternedType::Nil => LegacyType::Nil,
            InternedType::Done => LegacyType::Done,
            InternedType::Range => LegacyType::Range,
            InternedType::MetaType => LegacyType::MetaType,
            InternedType::Invalid { kind } => LegacyType::invalid(kind),

            InternedType::Array(elem) => LegacyType::Array(Box::new(self.to_type(*elem))),

            InternedType::Union(variants) => {
                let types: Vec<LegacyType> = variants.iter().map(|&v| self.to_type(v)).collect();
                LegacyType::Union(types.into())
            }

            InternedType::Tuple(elements) => {
                let types: Vec<LegacyType> = elements.iter().map(|&e| self.to_type(e)).collect();
                LegacyType::Tuple(types.into())
            }

            InternedType::FixedArray { element, size } => LegacyType::FixedArray {
                element: Box::new(self.to_type(*element)),
                size: *size,
            },

            InternedType::RuntimeIterator(elem) => {
                LegacyType::RuntimeIterator(Box::new(self.to_type(*elem)))
            }

            InternedType::Function {
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
                })
            }

            InternedType::Class {
                type_def_id,
                type_args,
            } => {
                let args: Vec<LegacyType> = type_args.iter().map(|&a| self.to_type(a)).collect();
                LegacyType::Nominal(NominalType::Class(ClassType {
                    type_def_id: *type_def_id,
                    type_args: args.into(),
                }))
            }

            InternedType::Record {
                type_def_id,
                type_args,
            } => {
                let args: Vec<LegacyType> = type_args.iter().map(|&a| self.to_type(a)).collect();
                LegacyType::Nominal(NominalType::Record(RecordType {
                    type_def_id: *type_def_id,
                    type_args: args.into(),
                }))
            }

            InternedType::Interface {
                type_def_id,
                type_args,
            } => {
                let args: Vec<LegacyType> = type_args.iter().map(|&a| self.to_type(a)).collect();
                // Note: We lose methods/extends info here - this is a limitation of
                // storing types by TypeDefId only. For full interface type, lookup
                // from EntityRegistry is needed.
                LegacyType::Nominal(NominalType::Interface(InterfaceType {
                    type_def_id: *type_def_id,
                    type_args: args.into(),
                    methods: vec![].into(),
                    extends: vec![].into(),
                }))
            }

            InternedType::Error { type_def_id } => {
                // Note: We lose field info here - lookup from EntityRegistry if needed
                LegacyType::Nominal(NominalType::Error(ErrorTypeInfo {
                    type_def_id: *type_def_id,
                    fields: vec![],
                }))
            }

            InternedType::TypeParam(name_id) => LegacyType::TypeParam(*name_id),

            InternedType::TypeParamRef(param_id) => LegacyType::TypeParamRef(*param_id),

            InternedType::Module(module_id) => {
                // Note: We lose exports/constants/external_funcs info here -
                // only module_id is stored in TypeArena. For full module type,
                // lookup from Analyzer's module state is needed.
                LegacyType::Module(ModuleType {
                    module_id: *module_id,
                    exports: std::collections::HashMap::new(),
                    constants: std::collections::HashMap::new(),
                    external_funcs: std::collections::HashSet::new(),
                })
            }

            InternedType::Fallible { success, error } => {
                use crate::sema::types::FallibleType;
                LegacyType::Fallible(FallibleType {
                    success_type: Box::new(self.to_type(*success)),
                    error_type: Box::new(self.to_type(*error)),
                })
            }

            InternedType::Structural(st) => {
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

            InternedType::Placeholder(kind) => LegacyType::Placeholder(kind.clone()),
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
        // Verify InternedType is reasonably sized
        let size = size_of::<InternedType>();
        assert!(size <= 48, "InternedType is {} bytes, expected <= 48", size);
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
            InternedType::Union(variants) => {
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
            InternedType::Array(elem) => {
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
            InternedType::Function {
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
            InternedType::Tuple(elements) => {
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
            InternedType::Class {
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
        });
        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);

        // Test with closure flag
        let closure = LegacyType::Function(FunctionType {
            params: vec![].into(),
            return_type: Box::new(LegacyType::Void),
            is_closure: true,
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
        let original = LegacyType::Nominal(NominalType::Class(ClassType {
            type_def_id,
            type_args: vec![LegacyType::Primitive(PrimitiveType::I32)].into(),
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
        let original = LegacyType::Nominal(NominalType::Record(RecordType {
            type_def_id,
            type_args: vec![
                LegacyType::Primitive(PrimitiveType::String),
                LegacyType::Primitive(PrimitiveType::Bool),
            ]
            .into(),
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
        });
        let original = LegacyType::Array(Box::new(func));

        let id = arena.from_type(&original);
        let back = arena.to_type(id);
        assert_eq!(original, back);
    }
}

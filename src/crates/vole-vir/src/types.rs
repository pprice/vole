// types.rs
//
// VIR type representations, memory layout descriptors, and reflection metadata.

use vole_identity::{NameId, Symbol, TypeDefId, VirTypeId};

use crate::expr::FieldStorage;

// ---------------------------------------------------------------------------
// VirType — self-contained type representation
// ---------------------------------------------------------------------------

/// Self-contained type in the VIR.
///
/// After monomorphization every type parameter has been substituted, so most
/// variants are fully concrete.  The `Param` variant represents an unresolved
/// generic type parameter (pre-monomorphization only).
///
/// `cranelift_type` is deliberately omitted: vole-vir must not depend on
/// Cranelift.  Codegen maps `VirType` to Cranelift types at instruction-
/// selection time.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VirType {
    /// Primitive scalar type (integers, floats, bool, string, handle).
    Primitive(VirPrimitiveKind),
    /// Generic type parameter (pre-monomorphization only).
    Param { name: NameId },
    /// Dynamically-sized array.
    Array { elem: VirTypeId },
    /// Fixed-size array (e.g. `[i32; 4]`).
    FixedArray { elem: VirTypeId, len: u32 },
    /// Tuple of heterogeneous types.
    Tuple { elems: Vec<VirTypeId> },
    /// Tagged union of variant types.
    Union { variants: Vec<VirTypeId> },
    /// Optional type (`T?`).
    Optional { inner: VirTypeId },
    /// Fallible return type (success or one of several error types).
    Fallible {
        success: VirTypeId,
        errors: Vec<VirTypeId>,
    },
    /// Function type with parameter types and a return type.
    Function {
        params: Vec<VirTypeId>,
        ret: VirTypeId,
    },
    /// Reference-counted class instance.
    Class {
        def: TypeDefId,
        type_args: Vec<VirTypeId>,
    },
    /// Value-type struct.
    Struct {
        def: TypeDefId,
        type_args: Vec<VirTypeId>,
    },
    /// Interface (trait object).
    Interface {
        def: TypeDefId,
        type_args: Vec<VirTypeId>,
    },
    /// Error type.
    Error { def: TypeDefId },
    /// Runtime iterator wrapping an `Iterator<T>` interface.
    RuntimeIterator { elem: VirTypeId },
    /// The void type (no value).
    Void,
    /// The bottom type (never returns).
    Never,
    /// Integer range.
    Range,
    /// Compile-time type metadata (`T.@meta`).
    MetaType,
    /// Unknown / unresolved type (error recovery).
    Unknown,
}

// ---------------------------------------------------------------------------
// VirPrimitiveKind — scalar primitive types
// ---------------------------------------------------------------------------

/// Scalar primitive types in the VIR.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VirPrimitiveKind {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
    String,
    Handle,
}

impl VirPrimitiveKind {
    /// Whether this primitive is an unsigned integer type.
    pub fn is_unsigned(self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    /// Whether this primitive is a numeric type (integer or float).
    pub fn is_numeric(self) -> bool {
        matches!(
            self,
            Self::I8
                | Self::I16
                | Self::I32
                | Self::I64
                | Self::I128
                | Self::U8
                | Self::U16
                | Self::U32
                | Self::U64
                | Self::F32
                | Self::F64
        )
    }
}

// ---------------------------------------------------------------------------
// StorageClass and VirTypeLayout
// ---------------------------------------------------------------------------

// Re-export from vole-identity — canonical definitions live there.
pub use vole_identity::{StorageClass, TypeLayout as VirTypeLayout};

// ---------------------------------------------------------------------------
// Struct and union layouts
// ---------------------------------------------------------------------------

/// Physical layout of a value-type struct in VIR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirStructLayout {
    /// The sema type definition this layout describes.
    pub type_def: TypeDefId,
    /// Ordered field list with storage information.
    pub fields: Vec<VirFieldInfo>,
}

/// A single field inside a `VirStructLayout`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirFieldInfo {
    /// Interned field name.
    pub name: Symbol,
    /// Concrete type of the field.
    pub ty: VirTypeId,
    /// VIR type of the field.
    pub vir_ty: VirTypeId,
    /// How the field is stored in memory (inline vs. heap-indirect).
    pub storage: FieldStorage,
}

/// Physical layout of a tagged union in VIR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirUnionLayout {
    /// The concrete variant types (order matches the tag values).
    pub variants: Vec<VirTypeId>,
    /// VIR variant types.
    pub vir_variants: Vec<VirTypeId>,
    /// Whether all variants fit inline (16-byte buffer) or require heap
    /// allocation.
    pub inline: bool,
}

// ---------------------------------------------------------------------------
// VirLayout — physical memory layout (legacy, kept for compatibility)
// ---------------------------------------------------------------------------

/// Physical memory layout for a VIR value.
///
/// `cranelift_type` is deliberately omitted: vole-vir must not depend on
/// Cranelift.  Codegen maps `VirLayout` to Cranelift types at instruction
/// selection time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirLayout {
    /// Size in bytes.
    pub size: u32,
    /// Whether this value is reference-counted.
    pub is_rc: bool,
    /// Whether this value lives on the heap.
    pub is_heap: bool,
}

// ---------------------------------------------------------------------------
// Reflection / annotation metadata
// ---------------------------------------------------------------------------

/// Compile-time metadata about a type, produced by `T.@meta`.
#[derive(Debug, Clone)]
pub struct VirTypeMeta {
    /// Interned type name.
    pub name: Symbol,
    /// The sema type definition.
    pub type_def: TypeDefId,
    /// Field metadata (empty for non-struct/class types).
    pub fields: Vec<VirFieldMeta>,
}

/// Compile-time metadata for a single field within a type.
#[derive(Debug, Clone)]
pub struct VirFieldMeta {
    /// Interned field name.
    pub name: Symbol,
    /// Concrete field type.
    pub ty: VirTypeId,
    /// VIR type of the field.
    pub vir_ty: VirTypeId,
    /// Annotations attached to this field.
    pub annotations: Vec<VirAnnotation>,
}

/// A single annotation instance attached to a type or field.
#[derive(Debug, Clone)]
pub struct VirAnnotation {
    /// The annotation type (must have `@annotation` marker).
    pub type_def: TypeDefId,
    /// The annotation's value payload.
    pub value: VirAnnotationValue,
}

/// The value payload of an annotation.
#[derive(Debug, Clone)]
pub enum VirAnnotationValue {
    /// Struct-like annotation: named fields with constant values.
    Instance { fields: Vec<(Symbol, VirConstant)> },
}

/// A compile-time constant value (used in annotation payloads).
#[derive(Debug, Clone)]
pub enum VirConstant {
    /// Integer constant.
    Int(i64),
    /// Floating-point constant.
    Float(f64),
    /// Boolean constant.
    Bool(bool),
    /// String constant.
    String(String),
    /// Nil constant.
    Nil,
}

// PartialEq for VirConstant — needed for testing / comparison.
// Float comparison uses bitwise equality (consistent with Eq on the rest).
impl PartialEq for VirConstant {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int(a), Self::Int(b)) => a == b,
            (Self::Float(a), Self::Float(b)) => a.to_bits() == b.to_bits(),
            (Self::Bool(a), Self::Bool(b)) => a == b,
            (Self::String(a), Self::String(b)) => a == b,
            (Self::Nil, Self::Nil) => true,
            _ => false,
        }
    }
}

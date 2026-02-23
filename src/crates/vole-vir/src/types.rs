// types.rs
//
// VIR type representations, memory layout descriptors, and reflection metadata.

use vole_identity::{Symbol, TypeDefId, TypeId};

use crate::expr::FieldStorage;

// ---------------------------------------------------------------------------
// VirType — concrete, fully-resolved types
// ---------------------------------------------------------------------------

/// Concrete, fully-resolved type in the VIR.
///
/// After monomorphization every type parameter has been substituted, so all
/// variants here are concrete.  `cranelift_type` is deliberately omitted:
/// vole-vir must not depend on Cranelift.  Codegen maps `VirType` to
/// Cranelift types at instruction-selection time.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VirType {
    /// A type that has already been resolved to a `TypeId` in sema.
    Resolved(TypeId),

    /// Integer type with a specific bit width.
    Int(BitWidth),
    /// Floating-point type with a specific bit width.
    Float(BitWidth),
    /// Boolean.
    Bool,
    /// Interned string (reference-counted).
    String,
    /// The nil / void type.
    Nil,
    /// Opaque pointer (used for FFI / runtime handles).
    Ptr,
    /// Opaque handle (file, socket, etc.).
    Handle,
    /// A value-type struct.
    Struct(VirStructLayout),
    /// A tagged union.
    Union(VirUnionLayout),
}

/// Bit width of an integer or float type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BitWidth {
    B8,
    B16,
    B32,
    B64,
    B128,
}

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
    pub ty: TypeId,
    /// How the field is stored in memory (inline vs. heap-indirect).
    pub storage: FieldStorage,
}

/// Physical layout of a tagged union in VIR.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VirUnionLayout {
    /// The concrete variant types (order matches the tag values).
    pub variants: Vec<TypeId>,
    /// Whether all variants fit inline (16-byte buffer) or require heap
    /// allocation.
    pub inline: bool,
}

// ---------------------------------------------------------------------------
// VirLayout — physical memory layout
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
    pub ty: TypeId,
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

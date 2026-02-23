// types.rs
//
// VIR type representations and memory layout descriptors.

use vole_identity::TypeId;

/// Concrete, fully-resolved type in the VIR.
///
/// After monomorphization every type parameter has been substituted, so all
/// variants here are concrete.  This enum will grow as VIR phases are added.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VirType {
    /// A type that has already been resolved to a `TypeId` in sema.
    Resolved(TypeId),
}

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

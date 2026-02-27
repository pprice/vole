// type_layout.rs
//
// Physical layout descriptors shared by VIR, sema, and codegen.
//
// These are pure data types whose only dependency is other identity types.
// They live in vole-identity so every downstream crate can use them without
// pulling in VIR or sema.

/// The register class / allocation strategy for a type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StorageClass {
    /// Integer registers (i8–i64, u8–u64, bool, handle).
    Word,
    /// Float registers (f32, f64).
    Float,
    /// Reference-counted heap allocation (class, string, array).
    Pointer,
    /// Two registers (i128).
    Wide,
    /// No storage (void, never, done).
    Void,
}

/// Physical layout descriptor for a type.
///
/// Describes the concrete memory shape: reference-counting, heap residency,
/// register width, and storage class.  Originally defined in vole-vir as
/// `VirTypeLayout`; moved here so codegen and sema can share the same type
/// without depending on the full VIR crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeLayout {
    /// Whether this type is reference-counted.
    pub is_rc: bool,
    /// Whether this type lives on the heap.
    pub is_heap: bool,
    /// Whether this type requires two registers (i128).
    pub is_wide: bool,
    /// Number of register slots: 0 for void, 1 for most, 2 for i128.
    pub slot_count: u8,
    /// The register class / allocation strategy.
    pub storage: StorageClass,
}

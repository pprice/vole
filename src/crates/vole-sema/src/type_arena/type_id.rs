// type_arena/type_id.rs
//
// Re-exports TypeId and TypeIdVec from vole-identity and defines sema-specific type helpers.

// Re-export TypeId and TypeIdVec from their canonical home in vole-identity
pub use vole_identity::{TypeId, TypeIdVec};

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

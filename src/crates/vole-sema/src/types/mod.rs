// src/sema/types/mod.rs
//
// Core type system module for Vole.
//
// This module is organized into submodules by type category:
// - `primitive` - PrimitiveType enum (i8-i128, u8-u64, f32, f64, bool, string)
// - `nominal` - NominalType enum (Class, Interface, Error) with TypeDefIds
// - `special` - Supporting types for special Type variants (Placeholder, Invalid, etc.)

pub mod nominal;
pub mod primitive;
pub mod special;
pub use nominal::{
    ClassType, ErrorTypeInfo, ExtendsVec, InterfaceMethodType, InterfaceType, NominalType,
};
pub use primitive::PrimitiveType;
pub use special::{AnalysisError, ConstantValue, PlaceholderKind};

use crate::type_arena::{TypeArena, TypeId, TypeIdVec};
use vole_identity::NameId;

// FunctionType is defined in vole-identity (alongside TypeId/TypeIdVec).
// Re-exported here for backward compatibility.
pub use vole_identity::FunctionType;

/// Field information for a class (TypeId version)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructFieldId {
    pub name_id: NameId,
    pub ty: TypeId,
    pub slot: usize, // Compile-time slot index
}

/// Arena-dependent extension methods for FunctionType.
///
/// These methods require a TypeArena reference and therefore cannot live
/// in vole-identity (which has no knowledge of the arena).
pub trait FunctionTypeArenaExt {
    /// Create a void function type (no arguments, returns void).
    fn void(arena: &TypeArena) -> Self;

    /// Create a predicate function type (one argument, returns bool).
    fn predicate(arg: TypeId, arena: &TypeArena) -> Self;

    /// Intern this FunctionType into the arena, returning its TypeId.
    fn intern(&self, arena: &mut TypeArena) -> TypeId;
}

impl FunctionTypeArenaExt for FunctionType {
    #[inline]
    fn void(arena: &TypeArena) -> Self {
        Self {
            is_closure: false,
            params_id: TypeIdVec::new(),
            return_type_id: arena.void(),
        }
    }

    #[inline]
    fn predicate(arg: TypeId, arena: &TypeArena) -> Self {
        Self {
            is_closure: false,
            params_id: smallvec::smallvec![arg],
            return_type_id: arena.bool(),
        }
    }

    fn intern(&self, arena: &mut TypeArena) -> TypeId {
        arena.function(self.params_id.clone(), self.return_type_id, self.is_closure)
    }
}

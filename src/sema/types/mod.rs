// src/sema/types/mod.rs
//
// Core type system module for Vole.
//
// This module is organized into submodules by type category:
// - `primitive` - PrimitiveType enum (i8-i128, u8-u64, f32, f64, bool, string)
// - `nominal` - NominalType enum (Class, Record, Interface, Error) with TypeDefIds
// - `special` - Supporting types for special Type variants (Placeholder, Invalid, etc.)
// - `display` - DisplayType enum (materialized form for error messages)

pub mod display;
pub mod nominal;
pub mod primitive;
pub mod special;
pub use display::{DisplayType, StructuralFieldType, StructuralMethodType, StructuralType};
pub use nominal::{
    ClassType, ErrorTypeInfo, ExtendsVec, InterfaceMethodType, InterfaceType, NominalType,
    RecordType,
};
pub use primitive::PrimitiveType;
pub use special::{AnalysisError, ConstantValue, FallibleType, ModuleType, PlaceholderKind};

use crate::identity::NameId;
use crate::sema::type_arena::{TypeArena, TypeId, TypeIdVec};

#[derive(Debug, Clone, Eq)]
pub struct FunctionType {
    /// If true, this function is a closure (has captures) and needs
    /// to be called with the closure pointer as the first argument.
    /// The closure pointer is passed implicitly and is not included in `params_id`.
    pub is_closure: bool,
    /// Interned parameter types
    pub params_id: TypeIdVec,
    /// Interned return type
    pub return_type_id: TypeId,
}

/// Field information for a class/record (TypeId version)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructFieldId {
    pub name_id: NameId,
    pub ty: TypeId,
    pub slot: usize, // Compile-time slot index
}

impl PartialEq for FunctionType {
    fn eq(&self, other: &Self) -> bool {
        // is_closure is not part of type equality - a closure () -> i64 is
        // compatible with a function type () -> i64 for type checking purposes
        //
        // Use TypeId fields for efficient O(1) comparison
        self.params_id == other.params_id && self.return_type_id == other.return_type_id
    }
}

// Manual Hash to match PartialEq semantics - ignore is_closure
impl std::hash::Hash for FunctionType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Use TypeId fields for efficient hashing
        self.params_id.hash(state);
        self.return_type_id.hash(state);
        // is_closure deliberately not hashed to match PartialEq
    }
}

impl FunctionType {
    /// Create a new FunctionType, interning types into the arena.
    /// This is the preferred constructor when you have DisplayTypes and an arena.
    pub fn new_with_arena(
        params: impl IntoIterator<Item = impl std::borrow::Borrow<DisplayType>>,
        return_type: &DisplayType,
        is_closure: bool,
        arena: &mut TypeArena,
    ) -> Self {
        let params_id: TypeIdVec = params
            .into_iter()
            .map(|p| arena.from_display(p.borrow()))
            .collect();
        let return_type_id = arena.from_display(return_type);
        Self {
            is_closure,
            params_id,
            return_type_id,
        }
    }

    /// Create a new FunctionType from TypeIds.
    /// This is the preferred constructor when you already have TypeIds (avoids DisplayType conversion).
    pub fn from_ids(param_ids: &[TypeId], return_id: TypeId, is_closure: bool) -> Self {
        Self {
            is_closure,
            params_id: param_ids.iter().copied().collect(),
            return_type_id: return_id,
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Display TypeIds - for proper type names, use arena-based display methods
        write!(f, "fn(")?;
        for (i, &param_id) in self.params_id.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "#{}", param_id.index())?;
        }
        write!(f, ") -> #{}", self.return_type_id.index())
    }
}

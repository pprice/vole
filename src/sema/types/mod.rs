// src/sema/types/mod.rs
//
// Core type system module for Vole.
//
// This module is organized into submodules by type category:
// - `primitive` - PrimitiveType enum (i8-i128, u8-u64, f32, f64, bool, string)
// - `nominal` - NominalType enum (Class, Record, Interface, Error) with TypeDefIds
// - `special` - Supporting types for special Type variants (Placeholder, Invalid, etc.)
// - `legacy` - LegacyType enum (being replaced by TypeId)

pub mod legacy;
pub mod nominal;
pub mod primitive;
pub mod special;
pub use legacy::{
    LegacyType, StructField, StructuralFieldType, StructuralMethodType, StructuralType,
};
pub use nominal::{
    ClassType, ErrorTypeInfo, ExtendsVec, InterfaceMethodType, InterfaceType, NominalType,
    RecordType,
};
pub use primitive::PrimitiveType;
pub use special::{AnalysisError, ConstantValue, FallibleType, ModuleType, PlaceholderKind};

use std::sync::Arc;

use crate::identity::NameId;
use crate::sema::type_arena::{TypeArena, TypeId, TypeIdVec};

#[derive(Debug, Clone, Eq)]
pub struct FunctionType {
    pub params: Arc<[LegacyType]>,
    pub return_type: Box<LegacyType>,
    /// If true, this function is a closure (has captures) and needs
    /// to be called with the closure pointer as the first argument.
    /// The closure pointer is passed implicitly and is not included in `params`.
    pub is_closure: bool,
    /// Interned parameter types (parallel to params)
    pub params_id: TypeIdVec,
    /// Interned return type (parallel to return_type)
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
    /// This is the preferred constructor when you have LegacyTypes and an arena.
    pub fn new_with_arena(
        params: impl Into<Arc<[LegacyType]>>,
        return_type: LegacyType,
        is_closure: bool,
        arena: &mut TypeArena,
    ) -> Self {
        let params: Arc<[LegacyType]> = params.into();
        let params_id: TypeIdVec = params.iter().map(|p| arena.from_type(p)).collect();
        let return_type_id = arena.from_type(&return_type);
        Self {
            params,
            return_type: Box::new(return_type),
            is_closure,
            params_id,
            return_type_id,
        }
    }

    /// Create a new FunctionType from TypeIds.
    /// This is the preferred constructor when you already have TypeIds (avoids LegacyType conversion).
    pub fn from_ids(
        param_ids: &[TypeId],
        return_id: TypeId,
        is_closure: bool,
        arena: &TypeArena,
    ) -> Self {
        let params: Arc<[LegacyType]> = param_ids.iter().map(|&id| arena.to_type(id)).collect();
        let return_type = Box::new(arena.to_type(return_id));
        Self {
            params,
            return_type,
            is_closure,
            params_id: param_ids.iter().copied().collect(),
            return_type_id: return_id,
        }
    }
}

impl std::fmt::Display for FunctionType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", param)?;
        }
        write!(f, ") -> {}", self.return_type)
    }
}

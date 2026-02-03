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

/// Field information for a class (TypeId version)
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
    /// Create a new FunctionType from TypeIds.
    pub fn from_ids(param_ids: &[TypeId], return_id: TypeId, is_closure: bool) -> Self {
        Self {
            is_closure,
            params_id: param_ids.iter().copied().collect(),
            return_type_id: return_id,
        }
    }

    /// Create a nullary (no arguments) function type.
    ///
    /// Equivalent to `FunctionType::from_ids(&[], return_type, false)`.
    #[inline]
    pub fn nullary(return_type: TypeId) -> Self {
        Self {
            is_closure: false,
            params_id: TypeIdVec::new(),
            return_type_id: return_type,
        }
    }

    /// Create a unary (one argument) function type.
    ///
    /// Equivalent to `FunctionType::from_ids(&[arg], return_type, false)`.
    #[inline]
    pub fn unary(arg: TypeId, return_type: TypeId) -> Self {
        Self {
            is_closure: false,
            params_id: smallvec::smallvec![arg],
            return_type_id: return_type,
        }
    }

    /// Create a binary (two arguments) function type.
    ///
    /// Equivalent to `FunctionType::from_ids(&[arg1, arg2], return_type, false)`.
    #[inline]
    pub fn binary(arg1: TypeId, arg2: TypeId, return_type: TypeId) -> Self {
        Self {
            is_closure: false,
            params_id: smallvec::smallvec![arg1, arg2],
            return_type_id: return_type,
        }
    }

    /// Create a void function type (no arguments, returns void).
    ///
    /// Equivalent to `FunctionType::from_ids(&[], arena.void(), false)`.
    #[inline]
    pub fn void(arena: &TypeArena) -> Self {
        Self {
            is_closure: false,
            params_id: TypeIdVec::new(),
            return_type_id: arena.void(),
        }
    }

    /// Create a predicate function type (one argument, returns bool).
    ///
    /// Equivalent to `FunctionType::from_ids(&[arg], arena.bool(), false)`.
    #[inline]
    pub fn predicate(arg: TypeId, arena: &TypeArena) -> Self {
        Self {
            is_closure: false,
            params_id: smallvec::smallvec![arg],
            return_type_id: arena.bool(),
        }
    }

    /// Intern this FunctionType into the arena, returning its TypeId.
    /// This consolidates the function type internment logic that was spread
    /// across codegen. Use this instead of calling arena.function() directly.
    pub fn intern(&self, arena: &mut TypeArena) -> TypeId {
        arena.function(self.params_id.clone(), self.return_type_id, self.is_closure)
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

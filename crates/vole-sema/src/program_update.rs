//! Update interface for arena mutations.
//!
//! ProgramUpdate provides a clean API for mutating the type arena,
//! centralizing all borrow_mut() calls to avoid scattered RefCell management.
//! This complements ProgramQuery (reads) with ProgramUpdate (writes).

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;

use crate::type_arena::{TypeArena, TypeId, TypeIdVec};
use vole_identity::{NameId, TypeDefId};

/// Update interface for mutating program data (primarily the type arena).
///
/// Centralizes all arena mutations, hiding RefCell borrow management.
/// Functions that need to create or modify types take &ProgramUpdate.
pub struct ProgramUpdate<'a> {
    arena: &'a Rc<RefCell<TypeArena>>,
}

impl<'a> ProgramUpdate<'a> {
    /// Create a new update interface
    pub fn new(arena: &'a Rc<RefCell<TypeArena>>) -> Self {
        Self { arena }
    }

    // =========================================================================
    // Type substitution
    // =========================================================================

    /// Substitute type parameters with concrete types.
    /// Returns the substituted type (may be the same if no substitutions apply).
    pub fn substitute(&self, ty: TypeId, substitutions: &FxHashMap<NameId, TypeId>) -> TypeId {
        self.arena.borrow_mut().substitute(ty, substitutions)
    }

    // =========================================================================
    // Composite type construction
    // =========================================================================

    /// Create an array type
    pub fn array(&self, element: TypeId) -> TypeId {
        self.arena.borrow_mut().array(element)
    }

    /// Create an optional type (T | nil)
    pub fn optional(&self, inner: TypeId) -> TypeId {
        self.arena.borrow_mut().optional(inner)
    }

    /// Create a union type from variants
    pub fn union(&self, variants: Vec<TypeId>) -> TypeId {
        self.arena.borrow_mut().union(variants)
    }

    /// Create a tuple type
    pub fn tuple(&self, elements: TypeIdVec) -> TypeId {
        self.arena.borrow_mut().tuple(elements)
    }

    /// Create a fixed-size array type
    pub fn fixed_array(&self, element: TypeId, size: usize) -> TypeId {
        self.arena.borrow_mut().fixed_array(element, size)
    }

    // =========================================================================
    // Function types
    // =========================================================================

    /// Create a function type
    pub fn function(&self, params: TypeIdVec, return_type: TypeId, is_fallible: bool) -> TypeId {
        self.arena
            .borrow_mut()
            .function(params, return_type, is_fallible)
    }

    /// Create a fallible type (success | error)
    pub fn fallible(&self, success: TypeId, error: TypeId) -> TypeId {
        self.arena.borrow_mut().fallible(success, error)
    }

    // =========================================================================
    // Named type construction
    // =========================================================================

    /// Create a class type with type arguments
    pub fn class(&self, type_def_id: TypeDefId, type_args: TypeIdVec) -> TypeId {
        self.arena.borrow_mut().class(type_def_id, type_args)
    }

    /// Create a record type with type arguments
    pub fn record(&self, type_def_id: TypeDefId, type_args: TypeIdVec) -> TypeId {
        self.arena.borrow_mut().record(type_def_id, type_args)
    }

    /// Create an interface type with type arguments
    pub fn interface(&self, type_def_id: TypeDefId, type_args: TypeIdVec) -> TypeId {
        self.arena.borrow_mut().interface(type_def_id, type_args)
    }

    /// Create an error type
    pub fn error_type(&self, type_def_id: TypeDefId) -> TypeId {
        self.arena.borrow_mut().error_type(type_def_id)
    }

    // =========================================================================
    // Runtime types
    // =========================================================================

    /// Create a runtime iterator type
    pub fn runtime_iterator(&self, element_type: TypeId) -> TypeId {
        self.arena.borrow_mut().runtime_iterator(element_type)
    }

    // =========================================================================
    // Placeholder types
    // =========================================================================

    /// Create a placeholder type (for type parameters, Self, etc.)
    pub fn placeholder(&self, kind: crate::types::PlaceholderKind) -> TypeId {
        self.arena.borrow_mut().placeholder(kind)
    }
}

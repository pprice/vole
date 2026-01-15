// src/sema/analyzer/type_helpers.rs
//
// Arena-backed type construction helpers for the TypeArena migration (Phase 3.2).
// These methods wrap type_arena operations and convert back to Type for compatibility
// with existing code. They will be optimized in later phases.

use super::*;
use crate::sema::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    // ========== Arena-backed type construction ==========
    //
    // These methods use the TypeArena internally for deduplication,
    // then convert to Type for compatibility with existing signatures.
    // In Phase 4+, we'll update callers to use TypeId directly.

    /// Create a primitive type through the arena
    #[inline]
    pub(crate) fn ty_prim(&mut self, p: PrimitiveType) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.primitive(p);
        arena.to_type(id)
    }

    /// Create i64 type through the arena
    #[inline]
    pub(crate) fn ty_i64(&mut self) -> LegacyType {
        self.ty_prim(PrimitiveType::I64)
    }

    /// Create i32 type through the arena
    #[inline]
    pub(crate) fn ty_i32(&mut self) -> LegacyType {
        self.ty_prim(PrimitiveType::I32)
    }

    /// Create f64 type through the arena
    #[inline]
    pub(crate) fn ty_f64(&mut self) -> LegacyType {
        self.ty_prim(PrimitiveType::F64)
    }

    /// Create bool type through the arena
    #[inline]
    pub(crate) fn ty_bool(&mut self) -> LegacyType {
        self.ty_prim(PrimitiveType::Bool)
    }

    /// Create string type through the arena
    #[inline]
    pub(crate) fn ty_string(&mut self) -> LegacyType {
        self.ty_prim(PrimitiveType::String)
    }

    /// Create void type through the arena
    #[inline]
    pub(crate) fn ty_void(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.void();
        arena.to_type(id)
    }

    /// Create nil type through the arena
    #[inline]
    pub(crate) fn ty_nil(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.nil();
        arena.to_type(id)
    }

    /// Create done type through the arena
    #[inline]
    pub(crate) fn ty_done(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.done();
        arena.to_type(id)
    }

    /// Create range type through the arena
    #[inline]
    pub(crate) fn ty_range(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.range();
        arena.to_type(id)
    }

    /// Create metatype (type) through the arena
    #[inline]
    pub(crate) fn ty_type(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.metatype();
        arena.to_type(id)
    }

    /// Create an array type through the arena
    #[inline]
    pub(crate) fn ty_array(&mut self, element: &LegacyType) -> LegacyType {
        let mut arena = self.type_arena.borrow_mut();
        let elem_id = arena.from_type(element);
        let arr_id = arena.array(elem_id);
        arena.to_type(arr_id)
    }

    /// Create a tuple type through the arena
    #[inline]
    pub(crate) fn ty_tuple(&mut self, elements: Vec<LegacyType>) -> LegacyType {
        let mut arena = self.type_arena.borrow_mut();
        let elem_ids: Vec<ArenaTypeId> = elements.iter().map(|t| arena.from_type(t)).collect();
        let tuple_id = arena.tuple(elem_ids);
        arena.to_type(tuple_id)
    }

    /// Create an optional type through the arena (T | nil)
    #[inline]
    #[allow(unused)] // Will be used in Phase 3.3+ migration
    pub(crate) fn ty_optional(&mut self, inner: &LegacyType) -> LegacyType {
        let mut arena = self.type_arena.borrow_mut();
        let inner_id = arena.from_type(inner);
        let opt_id = arena.optional(inner_id);
        arena.to_type(opt_id)
    }

    /// Create an invalid/error type for propagation (error already reported).
    /// Use `ty_invalid_traced` for unexpected cases that should be logged.
    #[inline]
    pub(crate) fn ty_invalid(&mut self) -> LegacyType {
        let arena = self.type_arena.borrow_mut();
        let id = arena.invalid();
        arena.to_type(id)
    }

    /// Create an invalid/error type with tracing for debugging.
    /// Use this for unexpected cases (fallback, unwrap failures) not propagation.
    #[inline]
    pub(crate) fn ty_invalid_traced(&mut self, reason: &str) -> LegacyType {
        tracing::warn!(reason, "creating invalid type");
        let arena = self.type_arena.borrow_mut();
        let id = arena.invalid();
        arena.to_type(id)
    }

    // ========== Arena TypeId operations ==========
    //
    // These methods work with TypeId directly for internal use.
    // They're exposed for gradual migration of callers.

    /// Convert Type to TypeId (interning)
    #[inline]
    #[allow(unused)] // Will be used in Phase 4+ migration
    pub(crate) fn type_to_id(&mut self, ty: &LegacyType) -> ArenaTypeId {
        self.type_arena.borrow_mut().from_type(ty)
    }

    /// Convert TypeId to Type
    #[inline]
    #[allow(unused)] // Will be used in Phase 4+ migration
    pub(crate) fn id_to_type(&self, id: ArenaTypeId) -> LegacyType {
        self.type_arena.borrow().to_type(id)
    }
}

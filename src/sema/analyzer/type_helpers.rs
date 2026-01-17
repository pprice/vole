// src/sema/analyzer/type_helpers.rs
//
// Arena-backed type construction helpers for the TypeArena migration.
// These methods wrap type_arena operations and convert back to Type for compatibility
// with existing code. The _id variants return TypeId directly for Phase 2+ migration.

#![allow(unused)] // Phase 2 infrastructure - methods will be used as callers migrate

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
    pub(crate) fn type_to_id(&mut self, ty: &LegacyType) -> ArenaTypeId {
        self.type_arena.borrow_mut().from_type(ty)
    }

    /// Convert TypeId to Type
    #[inline]
    pub(crate) fn id_to_type(&self, id: ArenaTypeId) -> LegacyType {
        self.type_arena.borrow().to_type(id)
    }

    // ========== TypeId-returning type construction ==========
    //
    // Phase 2: These return TypeId directly, avoiding LegacyType materialization.
    // Callers should prefer these over the ty_* variants.

    /// Create a primitive TypeId
    #[inline]
    #[allow(unused)] // Phase 2 infrastructure
    pub(crate) fn ty_prim_id(&self, p: PrimitiveType) -> ArenaTypeId {
        self.type_arena.borrow_mut().primitive(p)
    }

    /// Create i64 TypeId
    #[inline]
    pub(crate) fn ty_i64_id(&self) -> ArenaTypeId {
        self.ty_prim_id(PrimitiveType::I64)
    }

    /// Create i32 TypeId
    #[inline]
    pub(crate) fn ty_i32_id(&self) -> ArenaTypeId {
        self.ty_prim_id(PrimitiveType::I32)
    }

    /// Create f64 TypeId
    #[inline]
    pub(crate) fn ty_f64_id(&self) -> ArenaTypeId {
        self.ty_prim_id(PrimitiveType::F64)
    }

    /// Create bool TypeId
    #[inline]
    pub(crate) fn ty_bool_id(&self) -> ArenaTypeId {
        self.ty_prim_id(PrimitiveType::Bool)
    }

    /// Create string TypeId
    #[inline]
    pub(crate) fn ty_string_id(&self) -> ArenaTypeId {
        self.ty_prim_id(PrimitiveType::String)
    }

    /// Create void TypeId
    #[inline]
    pub(crate) fn ty_void_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().void()
    }

    /// Create nil TypeId
    #[inline]
    pub(crate) fn ty_nil_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().nil()
    }

    /// Create done TypeId
    #[inline]
    pub(crate) fn ty_done_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().done()
    }

    /// Create range TypeId
    #[inline]
    pub(crate) fn ty_range_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().range()
    }

    /// Create metatype TypeId
    #[inline]
    pub(crate) fn ty_type_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().metatype()
    }

    /// Create an array TypeId
    #[inline]
    pub(crate) fn ty_array_id(&self, element_id: ArenaTypeId) -> ArenaTypeId {
        self.type_arena.borrow_mut().array(element_id)
    }

    /// Create a tuple TypeId
    #[inline]
    pub(crate) fn ty_tuple_id(&self, element_ids: Vec<ArenaTypeId>) -> ArenaTypeId {
        self.type_arena.borrow_mut().tuple(element_ids)
    }

    /// Create an optional TypeId (T | nil)
    #[inline]
    pub(crate) fn ty_optional_id(&self, inner_id: ArenaTypeId) -> ArenaTypeId {
        self.type_arena.borrow_mut().optional(inner_id)
    }

    /// Create an invalid/error TypeId
    #[inline]
    pub(crate) fn ty_invalid_id(&self) -> ArenaTypeId {
        self.type_arena.borrow_mut().invalid()
    }

    /// Create an invalid/error TypeId with tracing
    #[inline]
    pub(crate) fn ty_invalid_traced_id(&self, reason: &str) -> ArenaTypeId {
        tracing::warn!(reason, "creating invalid type");
        self.type_arena.borrow_mut().invalid()
    }
}

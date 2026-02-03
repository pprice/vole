// types/type_ctx.rs
//
// Minimal context for type-system lookups in codegen.

use cranelift::prelude::Type;

use vole_sema::ProgramQuery;
use vole_sema::type_arena::TypeArena;

/// Minimal context for type-system lookups in codegen.
/// Stores ProgramQuery directly as a field for zero-overhead access.
pub struct TypeCtx<'a> {
    /// Query interface for type/entity/name lookups (stored, not created per-call)
    pub query: ProgramQuery<'a>,
    /// Cranelift pointer type (platform-specific). Reserved for type conversions
    /// that need to know the native pointer size.
    #[expect(
        dead_code,
        reason = "reserved for type conversions needing pointer size"
    )]
    pub pointer_type: Type,
}

impl<'a> TypeCtx<'a> {
    pub fn new(query: ProgramQuery<'a>, pointer_type: Type) -> Self {
        Self {
            query,
            pointer_type,
        }
    }

    /// Get the type arena
    #[inline]
    pub fn arena(&self) -> &'a TypeArena {
        self.query.arena()
    }
}

// types/type_ctx.rs
//
// Minimal context for type-system lookups in codegen.

use cranelift::prelude::Type;
use std::rc::Rc;

use vole_frontend::Interner;
use vole_identity::NameTable;
use vole_sema::type_arena::TypeArena;
use vole_sema::{EntityRegistry, ProgramQuery};

/// Minimal context for type-system lookups in codegen.
/// Stores ProgramQuery directly as a field for zero-overhead access.
pub struct TypeCtx<'a> {
    /// Query interface for type/entity/name lookups (stored, not created per-call)
    pub query: ProgramQuery<'a>,
    /// Cranelift pointer type (platform-specific)
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

    /// Get the entity registry
    #[inline]
    pub fn entities(&self) -> &'a EntityRegistry {
        self.query.registry()
    }

    /// Get the interner
    #[inline]
    pub fn interner(&self) -> &'a Interner {
        self.query.interner()
    }

    /// Get the name table Rc
    #[inline]
    pub fn name_table_rc(&self) -> &'a Rc<NameTable> {
        self.query.name_table_rc()
    }
}

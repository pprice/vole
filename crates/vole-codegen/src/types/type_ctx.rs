// types/type_ctx.rs
//
// Minimal context for type-system lookups in codegen.

use cranelift::prelude::Type;
use std::cell::RefCell;
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

    /// Convenience: borrow the type arena
    #[inline]
    pub fn arena(&self) -> std::cell::Ref<'_, TypeArena> {
        self.query.arena().borrow()
    }

    /// Raw arena access (for functions that need &RefCell<TypeArena>)
    #[inline]
    pub fn arena_rc(&self) -> &'a Rc<RefCell<TypeArena>> {
        self.query.arena()
    }

    /// Get an update interface for arena mutations.
    /// Centralizes all borrow_mut() calls for cleaner code.
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'a> {
        vole_sema::ProgramUpdate::new(self.query.arena())
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
    pub fn name_table_rc(&self) -> &'a Rc<RefCell<NameTable>> {
        self.query.name_table_rc()
    }
}

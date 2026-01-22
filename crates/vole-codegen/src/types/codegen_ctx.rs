// types/codegen_ctx.rs
//
// Codegen context with mutable JIT infrastructure.

// Allow dead code during migration - CodegenCtx will be used as CompileCtx is phased out
#![allow(dead_code)]

use cranelift::prelude::Type;
use cranelift_jit::JITModule;

use crate::FunctionRegistry;
use vole_frontend::Interner;
use vole_sema::type_arena::TypeArena;
use vole_sema::{EntityRegistry, ProgramQuery};

use super::TypeCtx;

/// Codegen context with mutable JIT infrastructure.
/// Extends TypeCtx with module and function registry access.
pub struct CodegenCtx<'a> {
    /// Type system lookups
    pub types: TypeCtx<'a>,
    /// Cranelift JIT module for function declarations
    pub module: &'a mut JITModule,
    /// Function identity and ID management
    pub func_registry: &'a mut FunctionRegistry,
}

impl<'a> CodegenCtx<'a> {
    pub fn new(
        query: ProgramQuery<'a>,
        pointer_type: Type,
        module: &'a mut JITModule,
        func_registry: &'a mut FunctionRegistry,
    ) -> Self {
        Self {
            types: TypeCtx::new(query, pointer_type),
            module,
            func_registry,
        }
    }

    /// Convenience: get TypeCtx reference
    #[inline]
    pub fn type_ctx(&self) -> &TypeCtx<'a> {
        &self.types
    }

    /// Convenience: pointer type (alias for Cg migration)
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.types.pointer_type
    }

    /// Convenience: query interface
    #[inline]
    pub fn query(&self) -> &ProgramQuery<'a> {
        &self.types.query
    }

    /// Convenience: borrow arena
    #[inline]
    pub fn arena(&self) -> std::cell::Ref<'_, TypeArena> {
        self.types.arena()
    }

    /// Get an update interface for arena mutations.
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        self.types.update()
    }

    /// Get interner reference.
    #[inline]
    pub fn interner(&self) -> &'a Interner {
        self.types.interner()
    }

    /// Get entity registry reference.
    #[inline]
    pub fn registry(&self) -> &'a EntityRegistry {
        self.types.entities()
    }

    /// Get mutable reference to function registry.
    #[inline]
    pub fn funcs(&mut self) -> &mut FunctionRegistry {
        self.func_registry
    }

    /// Get immutable reference to function registry.
    #[inline]
    pub fn funcs_ref(&self) -> &FunctionRegistry {
        self.func_registry
    }

    /// Get mutable reference to JIT module.
    #[inline]
    pub fn jit_module(&mut self) -> &mut JITModule {
        self.module
    }
}

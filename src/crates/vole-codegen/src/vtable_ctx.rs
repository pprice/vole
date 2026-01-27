// vtable_ctx.rs
//
// Trait for vtable compilation context.
// Provides unified interface for vtable operations.

use std::cell::RefCell;

use rustc_hash::FxHashMap;

use cranelift::prelude::Type;
use cranelift_jit::JITModule;

use vole_frontend::Interner;
use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::type_arena::TypeArena;
use vole_sema::{EntityRegistry, ProgramQuery};

use crate::types::{CodegenCtx, CompileEnv, TypeMetadataMap};
use crate::{AnalyzedProgram, FunctionKey, FunctionRegistry};

/// Trait providing the interface needed for vtable compilation.
///
/// This trait allows vtable operations to work with VtableCtxView,
/// which combines CodegenCtx and CompileEnv.
#[allow(dead_code)]
pub trait VtableCtx {
    /// Get the analyzed program reference
    fn analyzed(&self) -> &AnalyzedProgram;

    /// Get the type arena
    fn arena(&self) -> &TypeArena;

    /// Get the entity registry
    fn registry(&self) -> &EntityRegistry;

    /// Get the interner
    fn interner(&self) -> &Interner;

    /// Get query interface
    fn query(&self) -> ProgramQuery<'_>;

    /// Get the pointer type
    fn ptr_type(&self) -> Type;

    /// Get mutable JIT module
    fn jit_module(&mut self) -> &mut JITModule;

    /// Get mutable function registry
    fn funcs(&mut self) -> &mut FunctionRegistry;

    /// Resolve a type name string with fallback to interface/class search
    fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId>;

    /// Get the native function registry
    fn native_registry(&self) -> &NativeRegistry;

    /// Get the interface vtable registry
    fn interface_vtables(&self) -> &RefCell<crate::interface_vtable::InterfaceVtableRegistry>;

    /// Get type metadata map
    fn type_metadata(&self) -> &TypeMetadataMap;

    /// Get unified method function key map
    /// Keyed by (type_name_id, method_name_id) for stable lookup across analyzer instances
    fn method_func_keys(&self) -> &FxHashMap<(NameId, NameId), FunctionKey>;
}

/// A view that combines CodegenCtx and CompileEnv to implement VtableCtx.
///
/// This allows functions that need VtableCtx to work with split borrows from Cg,
/// avoiding borrow checker issues when both builder and context are needed.
pub struct VtableCtxView<'a, 'ctx> {
    pub codegen_ctx: &'a mut CodegenCtx<'ctx>,
    pub env: &'a CompileEnv<'ctx>,
}

impl<'a, 'ctx> VtableCtxView<'a, 'ctx> {
    pub fn new(codegen_ctx: &'a mut CodegenCtx<'ctx>, env: &'a CompileEnv<'ctx>) -> Self {
        Self { codegen_ctx, env }
    }
}

impl<'a, 'ctx> VtableCtx for VtableCtxView<'a, 'ctx> {
    fn analyzed(&self) -> &AnalyzedProgram {
        self.env.analyzed
    }

    fn arena(&self) -> &TypeArena {
        self.env.analyzed.type_arena()
    }

    fn registry(&self) -> &EntityRegistry {
        self.env.analyzed.entity_registry()
    }

    fn interner(&self) -> &Interner {
        self.env.interner
    }

    fn query(&self) -> ProgramQuery<'_> {
        self.env.analyzed.query()
    }

    fn ptr_type(&self) -> Type {
        self.codegen_ctx.ptr_type()
    }

    fn jit_module(&mut self) -> &mut JITModule {
        self.codegen_ctx.jit_module()
    }

    fn funcs(&mut self) -> &mut FunctionRegistry {
        self.codegen_ctx.funcs()
    }

    fn resolve_type_str_or_interface(&self, name: &str) -> Option<TypeDefId> {
        let query = self.query();
        let module_id = query.main_module();
        query.resolve_type_def_by_str(module_id, name)
    }

    fn native_registry(&self) -> &NativeRegistry {
        &self.env.state.native_registry
    }

    fn interface_vtables(&self) -> &RefCell<crate::interface_vtable::InterfaceVtableRegistry> {
        &self.env.state.interface_vtables
    }

    fn type_metadata(&self) -> &TypeMetadataMap {
        &self.env.state.type_metadata
    }

    fn method_func_keys(&self) -> &FxHashMap<(NameId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }
}

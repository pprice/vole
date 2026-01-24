// vtable_ctx.rs
//
// Trait for vtable compilation context.
// Provides unified interface for vtable operations.

use std::cell::{Ref, RefCell};
use std::rc::Rc;

use std::collections::HashMap;

use cranelift::prelude::Type;
use cranelift_jit::JITModule;

use vole_frontend::Interner;
use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeArena;
use vole_sema::{EntityRegistry, ProgramQuery, ProgramUpdate};

use crate::types::{CodegenCtx, CompileEnv, MethodInfo, TypeMetadataMap};
use crate::{AnalyzedProgram, FunctionKey, FunctionRegistry};

/// Trait providing the interface needed for vtable compilation.
///
/// This trait allows vtable operations to work with VtableCtxView,
/// which combines CodegenCtx and CompileEnv.
#[allow(dead_code)]
pub trait VtableCtx {
    /// Get the analyzed program reference
    fn analyzed(&self) -> &AnalyzedProgram;

    /// Borrow the type arena
    fn arena(&self) -> Ref<'_, TypeArena>;

    /// Get arena Rc for functions that need ownership
    fn arena_rc(&self) -> &Rc<RefCell<TypeArena>>;

    /// Get the entity registry
    fn registry(&self) -> &EntityRegistry;

    /// Get the interner
    fn interner(&self) -> &Interner;

    /// Get query interface
    fn query(&self) -> ProgramQuery<'_>;

    /// Get update interface for arena mutations
    fn update(&self) -> ProgramUpdate<'_>;

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

    /// Get impl method infos map
    /// DEPRECATED: Use method_func_keys instead.
    fn impl_method_infos(&self) -> &HashMap<(ImplTypeId, NameId), MethodInfo>;

    /// Get unified method function key map
    fn method_func_keys(&self) -> &HashMap<(TypeDefId, NameId), FunctionKey>;
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

    fn arena(&self) -> Ref<'_, TypeArena> {
        self.env.analyzed.type_arena()
    }

    fn arena_rc(&self) -> &Rc<RefCell<TypeArena>> {
        self.env.analyzed.type_arena_ref()
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

    fn update(&self) -> ProgramUpdate<'_> {
        ProgramUpdate::new(self.env.analyzed.type_arena_ref())
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

    fn impl_method_infos(&self) -> &HashMap<(ImplTypeId, NameId), MethodInfo> {
        &self.env.state.impl_method_infos
    }

    fn method_func_keys(&self) -> &HashMap<(TypeDefId, NameId), FunctionKey> {
        &self.env.state.method_func_keys
    }
}

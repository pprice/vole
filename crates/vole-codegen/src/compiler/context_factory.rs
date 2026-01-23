// compiler/context_factory.rs
//
// Factory for creating split context objects, centralizing context construction
// to avoid divergent call-site wiring during the CompileCtx migration.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use cranelift::prelude::Type;
use cranelift_jit::JITModule;

use crate::types::{CodegenCtx, FunctionCtx, GlobalCtx, MethodInfo, TypeCtx, TypeMetadata};
use crate::{AnalyzedProgram, FunctionRegistry};
use vole_frontend::{Expr, Interner, Symbol};
use vole_identity::{ModuleId, NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::ProgramQuery;
use vole_sema::implement_registry::ImplTypeId;
use vole_sema::type_arena::TypeId;

/// Factory for creating compilation contexts.
///
/// Centralizes the construction of TypeCtx, CodegenCtx, FunctionCtx, GlobalCtx,
/// and the legacy CompileCtx. This avoids divergent call-site wiring and ensures
/// consistent context creation across the codebase.
///
/// # Usage
///
/// ```ignore
/// let factory = CtxFactory::new(
///     analyzed, interner, module, func_registry,
///     type_metadata, impl_method_infos, static_method_infos,
///     interface_vtables, native_registry, global_inits,
///     source_file_ptr, lambda_counter,
/// );
///
/// // Build contexts as needed
/// let type_ctx = factory.type_ctx();
/// let function_ctx = FunctionCtx::main(return_type);
/// let global = factory.global();
///
/// // Or build a legacy CompileCtx for compatibility
/// let mut compile_ctx = factory.compile_ctx(return_type, None, None);
/// ```
#[allow(dead_code)] // Used during migration
pub(crate) struct CtxFactory<'a> {
    /// Analyzed program containing expr_types, method_resolutions, etc.
    pub analyzed: &'a AnalyzedProgram,
    /// Interner for symbol resolution (may differ from analyzed.interner for module code)
    pub interner: &'a Interner,
    /// Cranelift JIT module for function declarations
    pub module: &'a mut JITModule,
    /// Function identity and ID management
    pub func_registry: &'a mut FunctionRegistry,
    /// Class and record metadata
    pub type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    /// Implement block method info
    pub impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info
    pub static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry
    pub interface_vtables: &'a RefCell<crate::interface_vtable::InterfaceVtableRegistry>,
    /// Registry of native functions
    pub native_registry: &'a NativeRegistry,
    /// Global variable initializer expressions
    pub global_inits: &'a HashMap<Symbol, Expr>,
    /// Source file pointer for error reporting
    pub source_file_ptr: (*const u8, usize),
    /// Counter for generating unique lambda names
    pub lambda_counter: &'a Cell<usize>,
    /// Cranelift pointer type
    pub pointer_type: Type,
}

#[allow(dead_code)] // Used during migration
impl<'a> CtxFactory<'a> {
    /// Create a new context factory with all shared data.
    #[must_use]
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        analyzed: &'a AnalyzedProgram,
        interner: &'a Interner,
        module: &'a mut JITModule,
        func_registry: &'a mut FunctionRegistry,
        type_metadata: &'a HashMap<Symbol, TypeMetadata>,
        impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
        static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
        interface_vtables: &'a RefCell<crate::interface_vtable::InterfaceVtableRegistry>,
        native_registry: &'a NativeRegistry,
        global_inits: &'a HashMap<Symbol, Expr>,
        source_file_ptr: (*const u8, usize),
        lambda_counter: &'a Cell<usize>,
        pointer_type: Type,
    ) -> Self {
        Self {
            analyzed,
            interner,
            module,
            func_registry,
            type_metadata,
            impl_method_infos,
            static_method_infos,
            interface_vtables,
            native_registry,
            global_inits,
            source_file_ptr,
            lambda_counter,
            pointer_type,
        }
    }

    /// Get a query interface for the analyzed program.
    #[inline]
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(
            self.analyzed.entity_registry(),
            &self.analyzed.expression_data,
            self.analyzed.name_table_ref(),
            self.interner,
            self.analyzed.implement_registry(),
            &self.analyzed.module_programs,
            self.analyzed.type_arena_ref(),
        )
    }

    /// Build a TypeCtx for type-only operations.
    #[must_use]
    pub fn type_ctx(&self) -> TypeCtx<'_> {
        TypeCtx::new(self.query(), self.pointer_type)
    }

    /// Build GlobalCtx - shared read-only lookup tables.
    #[must_use]
    pub fn global(&self) -> GlobalCtx<'_> {
        GlobalCtx {
            analyzed: self.analyzed,
            interner: self.interner,
            type_metadata: self.type_metadata,
            impl_method_infos: self.impl_method_infos,
            static_method_infos: self.static_method_infos,
            interface_vtables: self.interface_vtables,
            native_registry: self.native_registry,
            global_inits: self.global_inits,
            source_file_ptr: self.source_file_ptr,
            lambda_counter: self.lambda_counter,
        }
    }

    /// Build a FunctionCtx for main program function (no module, no substitutions).
    #[must_use]
    pub fn function_ctx_main(&self, return_type: Option<TypeId>) -> FunctionCtx<'static> {
        FunctionCtx::main(return_type)
    }

    /// Build a FunctionCtx for module function.
    #[must_use]
    pub fn function_ctx_module(
        &self,
        return_type: Option<TypeId>,
        module_id: ModuleId,
    ) -> FunctionCtx<'static> {
        FunctionCtx::module(return_type, module_id)
    }

    /// Build a FunctionCtx for monomorphized generic function.
    #[must_use]
    pub fn function_ctx_monomorph<'b>(
        &self,
        return_type: Option<TypeId>,
        substitutions: &'b HashMap<NameId, TypeId>,
    ) -> FunctionCtx<'b> {
        FunctionCtx::monomorphized(return_type, substitutions)
    }

    /// Build a FunctionCtx for test function (no return type).
    #[must_use]
    pub fn function_ctx_test(&self) -> FunctionCtx<'static> {
        FunctionCtx::test()
    }

    // Note: A `compile_ctx()` method that returns CompileCtx<'a> is not possible
    // because CtxFactory holds mutable references to module and func_registry,
    // and Rust's borrowing rules prevent giving those same mutable references
    // to the returned CompileCtx while &mut self is held.
    //
    // For legacy compatibility, callers should:
    // 1. Use the factory's fields directly to construct CompileCtx, OR
    // 2. Use the split contexts (TypeCtx, FunctionCtx, GlobalCtx) with Cg::new_split
    //
    // Example legacy construction:
    // ```
    // let ctx = CompileCtx {
    //     analyzed: factory.analyzed,
    //     interner: factory.interner,
    //     module: factory.module,  // Note: factory must be consumed or mutable ref managed
    //     func_registry: factory.func_registry,
    //     ...
    // };
    // ```
}

/// Builder for creating a JitCtx.
///
/// This is separate from CtxFactory because JitCtx takes mutable references
/// to module and func_registry, which creates borrowing challenges.
/// Use this when you need direct access to JitCtx without going through
/// the full CtxFactory.
#[allow(dead_code)] // Used during migration
pub(crate) fn build_jit_ctx<'a>(
    module: &'a mut JITModule,
    func_registry: &'a mut FunctionRegistry,
) -> CodegenCtx<'a> {
    CodegenCtx::new(module, func_registry)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Full integration tests would require setting up a JIT context,
    // which is complex. These tests verify the factory compiles correctly
    // and the type signatures are as expected. Real testing happens through
    // the existing unit/snapshot test suite.

    #[test]
    fn function_ctx_constructors_work() {
        // Test that FunctionCtx constructors return the expected types
        let main_ctx = FunctionCtx::main(None);
        assert!(main_ctx.return_type.is_none());
        assert!(main_ctx.current_module.is_none());
        assert!(main_ctx.substitutions.is_none());

        let test_ctx = FunctionCtx::test();
        assert!(test_ctx.return_type.is_none());
    }
}

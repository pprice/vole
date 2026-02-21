// types/codegen_ctx.rs
//
// Codegen context with mutable infrastructure for code generation.

use cranelift::prelude::Type;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::FunctionRegistry;

/// A monomorphized instance that was lazily declared on FuncId miss and needs
/// compilation later. The pending queue is drained by a fixpoint loop after
/// each compilation phase.
#[derive(Debug, Clone)]
pub enum PendingMonomorph {
    /// A free-function monomorph (from monomorph_cache).
    Function(vole_sema::generic::MonomorphInstance),
    /// A class instance method monomorph (from class_method_monomorph_cache).
    ClassMethod(vole_sema::generic::ClassMethodMonomorphInstance),
    /// A static method monomorph (from static_method_monomorph_cache).
    StaticMethod(vole_sema::generic::StaticMethodMonomorphInstance),
}

/// Codegen context - mutable infrastructure for code generation.
///
/// This holds only the mutable parts needed during compilation:
/// - JIT module for declaring/defining functions
/// - Function registry for tracking function IDs
///
/// Read-only data (analyzed program, type metadata, etc.) lives in CompileEnv.
/// Per-function state (return type, substitutions) lives in FunctionCtx.
pub struct CodegenCtx<'a> {
    /// Cranelift JIT module for function declarations
    pub module: &'a mut JITModule,
    /// Function identity and ID management
    pub func_registry: &'a mut FunctionRegistry,
    /// Monomorphs lazily declared on demand (FuncId miss fallback).
    /// These have been declared (assigned a FuncId) but not yet compiled.
    /// Drained by the fixpoint compilation loop in Compiler.
    pub pending_monomorphs: &'a mut Vec<PendingMonomorph>,
}

impl<'a> CodegenCtx<'a> {
    pub fn new(
        module: &'a mut JITModule,
        func_registry: &'a mut FunctionRegistry,
        pending_monomorphs: &'a mut Vec<PendingMonomorph>,
    ) -> Self {
        Self {
            module,
            func_registry,
            pending_monomorphs,
        }
    }

    /// Get the pointer type from the JIT module's target config.
    #[inline]
    pub fn ptr_type(&self) -> Type {
        self.module.target_config().pointer_type()
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

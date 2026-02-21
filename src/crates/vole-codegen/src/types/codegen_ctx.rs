// types/codegen_ctx.rs
//
// Codegen context with mutable infrastructure for code generation.

use cranelift::prelude::Type;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::FunctionRegistry;
use vole_identity::NameId;

/// A monomorphized instance that was lazily declared on FuncId miss and needs
/// compilation later. The pending queue is drained by a fixpoint loop in a
/// follow-up ticket (vol-4nd6).
#[derive(Debug, Clone)]
pub enum PendingMonomorph {
    /// A free-function monomorph (from monomorph_cache).
    #[allow(dead_code)] // consumed by the fixpoint compilation loop (vol-4nd6)
    Function(vole_sema::generic::MonomorphInstance),
    /// A class instance method monomorph (from class_method_monomorph_cache).
    #[allow(dead_code)] // consumed by the fixpoint compilation loop (vol-4nd6)
    ClassMethod(vole_sema::generic::ClassMethodMonomorphInstance),
    /// A static method monomorph (from static_method_monomorph_cache).
    #[allow(dead_code)] // consumed by the fixpoint compilation loop (vol-4nd6)
    StaticMethod(vole_sema::generic::StaticMethodMonomorphInstance),
}

impl PendingMonomorph {
    /// Get the mangled name NameId of this pending monomorph.
    #[allow(dead_code)] // used by the fixpoint compilation loop (vol-4nd6)
    pub fn mangled_name(&self) -> NameId {
        match self {
            PendingMonomorph::Function(inst) => inst.mangled_name,
            PendingMonomorph::ClassMethod(inst) => inst.mangled_name,
            PendingMonomorph::StaticMethod(inst) => inst.mangled_name,
        }
    }
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
    /// Drained by the fixpoint compilation loop.
    pub pending_monomorphs: Vec<PendingMonomorph>,
}

impl<'a> CodegenCtx<'a> {
    pub fn new(module: &'a mut JITModule, func_registry: &'a mut FunctionRegistry) -> Self {
        Self {
            module,
            func_registry,
            pending_monomorphs: Vec::new(),
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

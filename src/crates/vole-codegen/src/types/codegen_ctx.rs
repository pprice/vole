// types/codegen_ctx.rs
//
// JIT context with mutable infrastructure for code generation.

use cranelift::prelude::Type;
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::FunctionRegistry;

/// JIT context - mutable infrastructure for code generation.
///
/// This holds only the mutable parts needed during compilation:
/// - JIT module for declaring/defining functions
/// - Function registry for tracking function IDs
///
/// Read-only data (analyzed program, type metadata, etc.) lives in CompileEnv.
/// Per-function state (return type, substitutions) lives in FunctionCtx.
pub struct JitCtx<'a> {
    /// Cranelift JIT module for function declarations
    pub module: &'a mut JITModule,
    /// Function identity and ID management
    pub func_registry: &'a mut FunctionRegistry,
}

impl<'a> JitCtx<'a> {
    pub fn new(module: &'a mut JITModule, func_registry: &'a mut FunctionRegistry) -> Self {
        Self {
            module,
            func_registry,
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

// Keep CodegenCtx as a type alias during migration
pub type CodegenCtx<'a> = JitCtx<'a>;

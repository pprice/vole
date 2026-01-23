// types/global_ctx.rs
//
// Global context - immutable/interior-mutable data shared across all compilations.

#![allow(dead_code)]

use std::cell::{Cell, RefCell};
use std::collections::HashMap;

use vole_frontend::{Expr, Interner, Symbol};
use vole_identity::{NameId, TypeDefId};
use vole_runtime::NativeRegistry;
use vole_sema::implement_registry::ImplTypeId;

use crate::AnalyzedProgram;
use crate::interface_vtable::InterfaceVtableRegistry;

use super::{CompileCtx, MethodInfo, TypeMetadata};

/// Global context - immutable and interior-mutable data shared during codegen.
///
/// This holds program-wide data that doesn't change during function compilation:
/// - Analyzed program (type info, method resolutions)
/// - Metadata maps (type metadata, method info)
/// - Interior-mutable registries (vtables, lambda counter)
///
/// Paired with `JitCtx` (mutable JIT infrastructure) and `FunctionCtx` (per-function state).
pub struct GlobalCtx<'a> {
    /// Analyzed program containing expr_types, method_resolutions, etc.
    pub analyzed: &'a AnalyzedProgram,
    /// Interner for symbol resolution
    pub interner: &'a Interner,
    /// Class and record metadata for struct literals, field access, and method calls
    pub type_metadata: &'a HashMap<Symbol, TypeMetadata>,
    /// Implement block method info for primitive and named types
    pub impl_method_infos: &'a HashMap<(ImplTypeId, NameId), MethodInfo>,
    /// Static method info keyed by (TypeDefId, method_name)
    pub static_method_infos: &'a HashMap<(TypeDefId, NameId), MethodInfo>,
    /// Interface vtable registry (uses interior mutability)
    pub interface_vtables: &'a RefCell<InterfaceVtableRegistry>,
    /// Registry of native functions for external method calls
    pub native_registry: &'a NativeRegistry,
    /// Global variable initializer expressions keyed by name
    pub global_inits: &'a HashMap<Symbol, Expr>,
    /// Source file pointer for error reporting
    pub source_file_ptr: (*const u8, usize),
    /// Counter for generating unique lambda names (interior mutability)
    pub lambda_counter: &'a Cell<usize>,
}

impl<'a> GlobalCtx<'a> {
    /// Create GlobalCtx from a CompileCtx (for transitional use)
    #[allow(dead_code)] // Part of CompileCtx migration
    pub fn from_compile_ctx(ctx: &'a CompileCtx<'a>) -> Self {
        Self {
            analyzed: ctx.analyzed,
            interner: ctx.interner,
            type_metadata: ctx.type_metadata,
            impl_method_infos: ctx.impl_method_infos,
            static_method_infos: ctx.static_method_infos,
            interface_vtables: ctx.interface_vtables,
            native_registry: ctx.native_registry,
            global_inits: ctx.global_inits,
            source_file_ptr: ctx.source_file_ptr,
            lambda_counter: ctx.lambda_counter,
        }
    }
}

// Keep ExplicitParams as a type alias for backward compatibility
pub type ExplicitParams<'a> = GlobalCtx<'a>;

// types/explicit_params.rs
//
// Explicit parameters - read-only lookup tables used during codegen.

// Allow dead code during migration - ExplicitParams will be used as CompileCtx is phased out
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

/// Explicit parameters - read-only lookup tables used during codegen.
/// These are shared across all function compilations within a compile unit.
pub struct ExplicitParams<'a> {
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

impl<'a> ExplicitParams<'a> {
    /// Create ExplicitParams from a CompileCtx (for transitional use)
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

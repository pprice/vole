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

use super::{MethodInfo, TypeMetadata};

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
    /// Get a ProgramUpdate for modifying the type arena.
    ///
    /// This is used when creating new types (e.g., function types for closures).
    #[inline]
    pub fn update(&self) -> vole_sema::ProgramUpdate<'_> {
        vole_sema::ProgramUpdate::new(self.analyzed.type_arena_ref())
    }
}

// Keep ExplicitParams as a type alias for backward compatibility
pub type ExplicitParams<'a> = GlobalCtx<'a>;

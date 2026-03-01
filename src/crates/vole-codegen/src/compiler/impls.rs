//! Shared types and traits for class/struct/implement method compilation.
//!
//! This module contains the shared abstractions used by both:
//! - `impl_dispatch` (class/struct method compilation)
//! - `impl_monomorph` (implement block registration and compilation)

use vole_frontend::{Interner, Symbol};
use vole_identity::{MethodId, ModuleId};
use vole_vir::entity_metadata::VirTypeDef;

/// Data needed to compile methods for a type (class or struct).
///
/// Uses VIR entity metadata: methods are referenced by MethodId (resolved
/// from `VirTypeDef.methods`) instead of AST `FuncDecl` nodes.
pub(super) struct TypeMethodsData<'a> {
    /// Type name symbol
    pub name: Symbol,
    /// Instance method IDs to compile
    pub method_ids: &'a [MethodId],
    /// Static method IDs to compile
    pub static_method_ids: &'a [MethodId],
    /// Type kind for error messages ("class" or "struct")
    pub type_kind: &'static str,
}

impl<'a> TypeMethodsData<'a> {
    /// Create from a VIR type definition.
    pub fn from_vir(type_def: &'a VirTypeDef, name: Symbol) -> Self {
        Self {
            name,
            method_ids: &type_def.methods,
            static_method_ids: &type_def.static_methods,
            type_kind: type_def.type_kind(),
        }
    }
}

/// Module-specific compilation context passed to method compilation helpers.
pub(super) struct ModuleCompileInfo<'a> {
    pub interner: &'a Interner,
    pub module_id: ModuleId,
}

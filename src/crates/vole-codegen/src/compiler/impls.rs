//! Shared types and traits for class/struct/implement method compilation.
//!
//! This module contains the shared abstractions used by both:
//! - `impl_dispatch` (class/struct method compilation)
//! - `impl_monomorph` (implement block registration and compilation)

use vole_frontend::Interner;
use vole_identity::ModuleId;

/// Module-specific compilation context passed to method compilation helpers.
pub(super) struct ModuleCompileInfo<'a> {
    pub interner: &'a Interner,
    pub module_id: ModuleId,
}

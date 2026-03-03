// types/compile_env.rs
//
// Compilation environment - session/unit level context.

use rustc_hash::FxHashMap;

use vole_identity::{Interner, ModuleId, Symbol, VirTypeId};

use crate::AnalyzedProgram;

use super::CodegenState;

/// Module export binding: (module_id, export_name, vir_type_id)
pub type ModuleExportBinding = (ModuleId, Symbol, VirTypeId);

/// Compilation environment for a session/unit.
///
/// Created once per `compile_program` call (or once per module).
/// Contains references to shared state that doesn't change during
/// function compilation.
///
/// Provides cleaner separation:
/// - `CompileEnv` = session/unit level (interner, module)
/// - `Cg` = per-function working context (return_type, substitutions)
pub struct CompileEnv<'a> {
    /// Analyzed program containing expr_types, method_resolutions, etc.
    pub analyzed: &'a AnalyzedProgram,
    /// Codegen lookup tables (type_metadata, method_infos, etc.)
    pub state: &'a CodegenState,
    /// Interner for symbol resolution (main or module-specific)
    pub interner: &'a Interner,
    /// Source file pointer for error reporting
    pub source_file_ptr: (*const u8, usize),
    /// Global module bindings from top-level destructuring imports
    pub global_module_bindings: &'a FxHashMap<Symbol, ModuleExportBinding>,
}

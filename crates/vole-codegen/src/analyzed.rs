// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;

use vole_frontend::{Interner, Program};
use vole_identity::NameTable;
use vole_sema::{
    AnalysisOutput, EntityRegistry, ExpressionData, ImplementRegistry, ProgramQuery, TypeArena,
};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Interner,
    /// All expression-level metadata (types, method resolutions, generic calls)
    pub expression_data: ExpressionData,
    /// Methods added via implement blocks (includes external_func_info)
    pub implement_registry: ImplementRegistry,
    /// Parsed module programs for compiling pure Vole functions
    pub module_programs: FxHashMap<String, (Program, Interner)>,
    /// Qualified name interner for printable identities
    pub name_table: NameTable,
    /// Entity registry for type/method/field/function identity
    pub entity_registry: EntityRegistry,
    /// Shared type arena for interned types (same arena used by ExpressionData)
    pub type_arena: Rc<RefCell<TypeArena>>,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    pub fn from_analysis(program: Program, interner: Interner, output: AnalysisOutput) -> Self {
        Self {
            program,
            interner,
            expression_data: output.expression_data,
            implement_registry: output.implement_registry,
            module_programs: output.module_programs,
            name_table: output.name_table,
            entity_registry: output.entity_registry,
            type_arena: output.type_arena,
        }
    }

    /// Get a query interface for accessing type information and analysis results.
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(
            &self.entity_registry,
            &self.expression_data,
            &self.name_table,
            &self.interner,
            &self.implement_registry,
            &self.module_programs,
        )
    }
}

// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;

use vole_frontend::{Interner, Program};
use vole_identity::NameTable;
use vole_sema::{
    AnalysisOutput, CodegenDb, EntityRegistry, ExpressionData, ImplementRegistry, ProgramQuery,
    TypeArena,
};

/// Result of parsing and analyzing a source file.
pub struct AnalyzedProgram {
    pub program: Program,
    pub interner: Interner,
    /// All expression-level metadata (types, method resolutions, generic calls)
    pub expression_data: ExpressionData,
    /// Parsed module programs for compiling pure Vole functions
    pub module_programs: FxHashMap<String, (Program, Interner)>,
    /// Compilation database converted for codegen use (types/names wrapped in Rc<RefCell<>>)
    pub db: CodegenDb,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    pub fn from_analysis(program: Program, interner: Interner, output: AnalysisOutput) -> Self {
        // Convert CompilationDb to CodegenDb (wraps types/names in Rc<RefCell<>>)
        let db = match Rc::try_unwrap(output.db) {
            Ok(cell) => cell.into_inner().into_codegen(),
            Err(rc) => (*rc.borrow()).clone().into_codegen(),
        };
        Self {
            program,
            interner,
            expression_data: output.expression_data,
            module_programs: output.module_programs,
            db,
        }
    }

    /// Get a query interface for accessing type information and analysis results.
    pub fn query(&self) -> ProgramQuery<'_> {
        ProgramQuery::new(
            self.entity_registry(),
            &self.expression_data,
            self.name_table_ref(),
            &self.interner,
            self.implement_registry(),
            &self.module_programs,
            self.type_arena(),
        )
    }

    /// Get read-only access to the name table
    pub fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        self.db.names.borrow()
    }

    /// Get mutable access to the name table (for interning new names in codegen)
    pub fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        self.db.names.borrow_mut()
    }

    /// Get a shared reference to the name table Rc (cloned)
    pub fn name_table_rc(&self) -> Rc<RefCell<NameTable>> {
        Rc::clone(self.name_table_ref())
    }

    /// Get a reference to the name table Rc (borrowed, no clone)
    pub fn name_table_ref(&self) -> &Rc<RefCell<NameTable>> {
        &self.db.names
    }

    /// Get read-only access to the type arena
    pub fn type_arena(&self) -> &TypeArena {
        &self.db.types
    }

    /// Get read-only access to entity registry
    pub fn entity_registry(&self) -> &EntityRegistry {
        &self.db.entities
    }

    /// Get read-only access to implement registry
    pub fn implement_registry(&self) -> &ImplementRegistry {
        &self.db.implements
    }
}

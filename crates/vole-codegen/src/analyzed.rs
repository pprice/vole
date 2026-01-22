// analyzed.rs
//! Result of parsing and analyzing a source file.

use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;

use vole_frontend::{Interner, Program};
use vole_identity::NameTable;
use vole_sema::{
    AnalysisOutput, CompilationDb, EntityRegistry, ExpressionData, ImplementRegistry, ProgramQuery,
    TypeArena,
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
    /// Shared name table for qualified name interning (used by codegen for lambda/test names)
    pub name_table: Rc<RefCell<NameTable>>,
    /// Entity registry for type/method/field/function identity
    pub entity_registry: EntityRegistry,
    /// Shared type arena for interned types (same arena used by ExpressionData)
    pub type_arena: Rc<RefCell<TypeArena>>,
}

impl AnalyzedProgram {
    /// Construct AnalyzedProgram from parsed program and analysis output.
    pub fn from_analysis(program: Program, interner: Interner, output: AnalysisOutput) -> Self {
        // Extract components from the shared compilation database.
        // If the db has a single owner (no cache), we can take ownership.
        // If the db has multiple owners (cache holds a reference), we clone the inner data.
        let (types, entities, implements, names) = match Rc::try_unwrap(output.db) {
            Ok(cell) => {
                let CompilationDb {
                    types,
                    entities,
                    implements,
                    names,
                } = cell.into_inner();
                (types, entities, implements, names)
            }
            Err(rc) => {
                // Cache still holds a reference - clone the inner data
                let db = rc.borrow();
                (
                    db.types.clone(),
                    db.entities.clone(),
                    db.implements.clone(),
                    db.names.clone(),
                )
            }
        };
        Self {
            program,
            interner,
            expression_data: output.expression_data,
            implement_registry: implements,
            module_programs: output.module_programs,
            name_table: Rc::new(RefCell::new(names)),
            entity_registry: entities,
            type_arena: Rc::new(RefCell::new(types)),
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
            &self.type_arena,
        )
    }

    /// Get read-only access to the name table
    pub fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        self.name_table.borrow()
    }

    /// Get mutable access to the name table (for interning new names in codegen)
    pub fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        self.name_table.borrow_mut()
    }

    /// Get a shared reference to the name table Rc (for FunctionRegistry)
    pub fn name_table_rc(&self) -> Rc<RefCell<NameTable>> {
        Rc::clone(&self.name_table)
    }
}

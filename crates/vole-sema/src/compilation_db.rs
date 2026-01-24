// src/sema/compilation_db.rs
//
// Unified compilation database containing all registries.
// Wrapped in Rc<RefCell<>> for shared access across analyzer instances.

use crate::entity_registry::EntityRegistry;
use crate::implement_registry::ImplementRegistry;
use crate::type_arena::TypeArena;
use vole_identity::NameTable;

/// Unified compilation database containing all type/entity/method registries.
///
/// This is shared across analyzer instances via `Rc<RefCell<CompilationDb>>`,
/// eliminating expensive clone/merge operations when analyzing modules.
///
/// # Usage
/// ```ignore
/// let db = Rc::new(RefCell::new(CompilationDb::new()));
///
/// // Read access
/// let method = db.borrow().entities.get_method(id);
///
/// // Write access
/// db.borrow_mut().entities.register_method(...);
///
/// // Multiple reads - borrow once
/// {
///     let db = db.borrow();
///     let ty = db.types.get(type_id);
///     let method = db.entities.get_method(method_id);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct CompilationDb {
    /// Interned type representations (TypeId -> SemaType)
    pub types: TypeArena,
    /// Type/method/field/function definitions
    pub entities: EntityRegistry,
    /// Methods added via implement blocks
    pub implements: ImplementRegistry,
    /// Fully-qualified name interner
    pub names: NameTable,
}

impl CompilationDb {
    /// Create a new compilation database with primitives registered.
    pub fn new() -> Self {
        let names = NameTable::new();
        let mut entities = EntityRegistry::new();
        entities.register_primitives(&names);
        Self {
            types: TypeArena::new(),
            entities,
            implements: ImplementRegistry::new(),
            names,
        }
    }

    /// Get the main module ID
    pub fn main_module(&self) -> vole_identity::ModuleId {
        self.names.main_module()
    }

    /// Get the builtin module ID (creates it if needed)
    pub fn builtin_module(&mut self) -> vole_identity::ModuleId {
        self.names.builtin_module()
    }
}

impl Default for CompilationDb {
    fn default() -> Self {
        Self::new()
    }
}

/// Parts extracted from CompilationDb for codegen use.
/// TypeArena is owned directly (immutable during codegen).
/// NameTable remains in Rc<RefCell<>> for function name interning.
pub struct CodegenDb {
    /// Type arena - immutable during codegen
    pub types: TypeArena,
    pub entities: EntityRegistry,
    pub implements: ImplementRegistry,
    /// Names still need mutation for function name interning
    pub names: std::rc::Rc<std::cell::RefCell<NameTable>>,
}

impl CompilationDb {
    /// Convert to a form suitable for codegen.
    /// TypeArena is moved directly (immutable during codegen).
    /// NameTable wrapped in Rc<RefCell<>> for function name interning.
    pub fn into_codegen(self) -> CodegenDb {
        CodegenDb {
            types: self.types,
            entities: self.entities,
            implements: self.implements,
            names: std::rc::Rc::new(std::cell::RefCell::new(self.names)),
        }
    }
}

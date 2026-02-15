// src/sema/compilation_db.rs
//
// Unified compilation database containing all registries.
// Shared across analyzer instances via Rc<CompilationDb>.
//
// Each field has its own RefCell<Rc<T>> allowing independent borrows
// of types, entities, names, and implements without contention.
// Mutation uses Rc::make_mut (copy-on-write) inside RefMut guards.

use crate::entity_registry::EntityRegistry;
use crate::implement_registry::ImplementRegistry;
use crate::type_arena::TypeArena;
use std::cell::{Ref, RefCell, RefMut};
use std::rc::Rc;
use vole_identity::NameTable;

/// Unified compilation database containing all type/entity/method registries.
///
/// Shared across analyzer instances via `Rc<CompilationDb>`.
/// Each field is independently borrowable via its own `RefCell`, eliminating
/// the borrow contention that previously required raw-pointer workarounds.
///
/// # Usage
/// ```ignore
/// let db = Rc::new(CompilationDb::new());
///
/// // Independent borrows -- no contention
/// let types = db.types();      // borrows types only
/// let entities = db.entities(); // borrows entities only, types still borrowed
///
/// // Write access (uses Rc::make_mut internally via accessor methods)
/// let mut types = db.types_mut();
/// types.register(...);
/// ```
pub struct CompilationDb {
    /// Interned type representations (TypeId -> SemaType).
    /// Rc-wrapped for cheap sharing with CodegenDb.
    types: RefCell<Rc<TypeArena>>,
    /// Type/method/field/function definitions.
    /// Rc-wrapped for cheap sharing with CodegenDb.
    entities: RefCell<Rc<EntityRegistry>>,
    /// Methods added via implement blocks.
    /// Rc-wrapped for cheap sharing with CodegenDb.
    implements: RefCell<Rc<ImplementRegistry>>,
    /// Fully-qualified name interner.
    /// Rc-wrapped for cheap sharing with CodegenDb.
    names: RefCell<Rc<NameTable>>,
}

impl CompilationDb {
    /// Create a new compilation database with primitives registered.
    pub fn new() -> Self {
        let names = NameTable::new();
        let mut entities = EntityRegistry::new();
        entities.register_primitives(&names);
        Self {
            types: RefCell::new(Rc::new(TypeArena::new())),
            entities: RefCell::new(Rc::new(entities)),
            implements: RefCell::new(Rc::new(ImplementRegistry::new())),
            names: RefCell::new(Rc::new(names)),
        }
    }

    /// Get the type arena (read access).
    #[inline]
    pub fn types(&self) -> Ref<'_, TypeArena> {
        Ref::map(self.types.borrow(), |rc| &**rc)
    }

    /// Get the type arena (write access, copy-on-write via Rc::make_mut).
    #[inline]
    pub fn types_mut(&self) -> RefMut<'_, TypeArena> {
        RefMut::map(self.types.borrow_mut(), |rc| Rc::make_mut(rc))
    }

    /// Clone the Rc for the type arena (for CodegenDb sharing).
    #[inline]
    pub fn types_rc(&self) -> Rc<TypeArena> {
        Rc::clone(&self.types.borrow())
    }

    /// Get the entity registry (read access).
    #[inline]
    pub fn entities(&self) -> Ref<'_, EntityRegistry> {
        Ref::map(self.entities.borrow(), |rc| &**rc)
    }

    /// Get the entity registry (write access, copy-on-write via Rc::make_mut).
    #[inline]
    pub fn entities_mut(&self) -> RefMut<'_, EntityRegistry> {
        RefMut::map(self.entities.borrow_mut(), |rc| Rc::make_mut(rc))
    }

    /// Clone the Rc for the entity registry (for CodegenDb sharing).
    #[inline]
    pub fn entities_rc(&self) -> Rc<EntityRegistry> {
        Rc::clone(&self.entities.borrow())
    }

    /// Get the implement registry (read access).
    #[inline]
    pub fn implements(&self) -> Ref<'_, ImplementRegistry> {
        Ref::map(self.implements.borrow(), |rc| &**rc)
    }

    /// Get the implement registry (write access, copy-on-write via Rc::make_mut).
    #[inline]
    pub fn implements_mut(&self) -> RefMut<'_, ImplementRegistry> {
        RefMut::map(self.implements.borrow_mut(), |rc| Rc::make_mut(rc))
    }

    /// Clone the Rc for the implement registry (for CodegenDb sharing).
    #[inline]
    pub fn implements_rc(&self) -> Rc<ImplementRegistry> {
        Rc::clone(&self.implements.borrow())
    }

    /// Get the name table (read access).
    #[inline]
    pub fn names(&self) -> Ref<'_, NameTable> {
        Ref::map(self.names.borrow(), |rc| &**rc)
    }

    /// Get the name table (write access, copy-on-write via Rc::make_mut).
    #[inline]
    pub fn names_mut(&self) -> RefMut<'_, NameTable> {
        RefMut::map(self.names.borrow_mut(), |rc| Rc::make_mut(rc))
    }

    /// Clone the Rc for the name table (for CodegenDb sharing).
    #[inline]
    pub fn names_rc(&self) -> Rc<NameTable> {
        Rc::clone(&self.names.borrow())
    }

    /// Get the main module ID.
    pub fn main_module(&self) -> vole_identity::ModuleId {
        self.names.borrow().main_module()
    }

    /// Get the builtin module ID (creates it if needed).
    pub fn builtin_module(&self) -> vole_identity::ModuleId {
        self.names_mut().builtin_module()
    }
}

impl Default for CompilationDb {
    fn default() -> Self {
        Self::new()
    }
}

/// Parts extracted from CompilationDb for codegen use.
/// All fields are Rc-shared with CompilationDb and immutable during codegen.
pub struct CodegenDb {
    /// Type arena - Rc-shared, immutable during codegen
    pub types: Rc<TypeArena>,
    /// Entity registry - Rc-shared, immutable during codegen
    pub entities: Rc<EntityRegistry>,
    /// Implement registry - Rc-shared, immutable during codegen
    pub implements: Rc<ImplementRegistry>,
    /// Name table - Rc-shared, immutable during codegen
    pub names: Rc<NameTable>,
}

impl CompilationDb {
    /// Convert to a form suitable for codegen (consuming self).
    /// Extracts Rc references from RefCells (O(1)).
    pub fn into_codegen(self) -> CodegenDb {
        CodegenDb {
            types: self.types.into_inner(),
            entities: self.entities.into_inner(),
            implements: self.implements.into_inner(),
            names: self.names.into_inner(),
        }
    }

    /// Create a CodegenDb that shares data with this CompilationDb via Rc.
    /// This is the zero-clone path used when the CompilationDb has multiple owners
    /// (e.g., when the module cache holds a reference).
    /// All fields are Rc-shared (O(1), no cloning).
    pub fn to_codegen_shared(&self) -> CodegenDb {
        CodegenDb {
            types: self.types_rc(),
            entities: self.entities_rc(),
            implements: self.implements_rc(),
            names: self.names_rc(),
        }
    }
}

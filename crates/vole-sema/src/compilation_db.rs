// src/sema/compilation_db.rs
//
// Unified compilation database containing all registries.
// Wrapped in Rc<RefCell<>> for shared access across analyzer instances.
//
// Fields (types, entities, implements) are Rc-wrapped for cheap sharing
// with CodegenDb. This avoids expensive clones when the module cache
// holds a reference to the CompilationDb during codegen conversion.
// Mutation during analysis uses Rc::make_mut (copy-on-write), which is
// free when the Rc has a single owner (the typical case).

use crate::entity_registry::EntityRegistry;
use crate::implement_registry::ImplementRegistry;
use crate::type_arena::TypeArena;
use std::rc::Rc;
use vole_identity::NameTable;

/// Unified compilation database containing all type/entity/method registries.
///
/// This is shared across analyzer instances via `Rc<RefCell<CompilationDb>>`,
/// eliminating expensive clone/merge operations when analyzing modules.
///
/// The `types`, `entities`, and `implements` fields are `Rc`-wrapped so that
/// `CodegenDb` can share them without cloning. During analysis, mutation goes
/// through `Rc::make_mut` which is zero-cost when the refcount is 1 (the
/// common case, since `CodegenDb` is dropped before the next analysis).
///
/// # Usage
/// ```ignore
/// let db = Rc::new(RefCell::new(CompilationDb::new()));
///
/// // Read access
/// let method = db.borrow().entities.get_method(id);
///
/// // Write access (uses Rc::make_mut internally via accessor methods)
/// db.borrow_mut().entities_mut().register_method(...);
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
    /// Interned type representations (TypeId -> SemaType).
    /// Rc-wrapped for cheap sharing with CodegenDb.
    pub types: Rc<TypeArena>,
    /// Type/method/field/function definitions.
    /// Rc-wrapped for cheap sharing with CodegenDb.
    pub entities: Rc<EntityRegistry>,
    /// Methods added via implement blocks.
    /// Rc-wrapped for cheap sharing with CodegenDb.
    pub implements: Rc<ImplementRegistry>,
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
            types: Rc::new(TypeArena::new()),
            entities: Rc::new(entities),
            implements: Rc::new(ImplementRegistry::new()),
            names,
        }
    }

    /// Get mutable access to the type arena (copy-on-write via Rc::make_mut).
    /// Free when refcount is 1 (the common case).
    #[inline]
    pub fn types_mut(&mut self) -> &mut TypeArena {
        Rc::make_mut(&mut self.types)
    }

    /// Get mutable access to the entity registry (copy-on-write via Rc::make_mut).
    /// Free when refcount is 1 (the common case).
    #[inline]
    pub fn entities_mut(&mut self) -> &mut EntityRegistry {
        Rc::make_mut(&mut self.entities)
    }

    /// Get mutable access to the implement registry (copy-on-write via Rc::make_mut).
    /// Free when refcount is 1 (the common case).
    #[inline]
    pub fn implements_mut(&mut self) -> &mut ImplementRegistry {
        Rc::make_mut(&mut self.implements)
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
    /// Shares Rc references for all fields (O(1)).
    pub fn into_codegen(self) -> CodegenDb {
        CodegenDb {
            types: self.types,
            entities: self.entities,
            implements: self.implements,
            names: Rc::new(self.names),
        }
    }

    /// Create a CodegenDb that shares data with this CompilationDb via Rc.
    /// This is the zero-clone path used when the CompilationDb has multiple owners
    /// (e.g., when the module cache holds a reference).
    /// NameTable is cloned (other fields are Rc-shared).
    pub fn to_codegen_shared(&self) -> CodegenDb {
        CodegenDb {
            types: Rc::clone(&self.types),
            entities: Rc::clone(&self.entities),
            implements: Rc::clone(&self.implements),
            names: Rc::new(self.names.clone()),
        }
    }
}

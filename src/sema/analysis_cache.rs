//! General-purpose module analysis cache.
//!
//! Caches the analysis results of any imported module (stdlib, user modules, etc.)
//! so that multiple files importing the same module don't re-parse and re-analyze it.
//!
//! This is especially useful for:
//! - Test runner: 100+ files all importing the same prelude/stdlib
//! - Large projects: Many files importing shared utilities
//! - Incremental builds: Only re-analyze changed modules

use crate::frontend::{Interner, NodeId, Program};
use crate::identity::NameTable;
use crate::sema::TypeArena;
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::{FunctionType, ModuleType, Type};
use crate::sema::{EntityRegistry, ImplementRegistry};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Cached analysis results for a single module.
#[derive(Clone)]
pub struct CachedModule {
    /// Parsed program
    pub program: Program,
    /// Interner with symbols from this module
    pub interner: Interner,
    /// Module type (exports, constants, external functions) - only for user imports
    pub module_type: Option<ModuleType>,
    /// Expression types from analysis.
    /// Stored as Type (interned handles) - valid because TypeArena is shared
    /// across all analyzers via Rc<RefCell<TypeArena>>.
    pub expr_types: HashMap<NodeId, Type>,
    /// Method resolutions from analysis
    pub method_resolutions: HashMap<NodeId, ResolvedMethod>,
    /// Entity registry contributions (types, methods, fields)
    pub entity_registry: EntityRegistry,
    /// Implement registry contributions
    pub implement_registry: ImplementRegistry,
    /// Functions registered by name
    pub functions_by_name: FxHashMap<String, FunctionType>,
    /// Name table state after analyzing this module (includes all NameIds used by registries)
    pub name_table: NameTable,
}

/// Cache for module analysis results.
///
/// Thread-local cache that can be shared across multiple Analyzer instances.
/// Use `Rc<RefCell<ModuleCache>>` to share between analyzers in the same thread.
/// The cache includes a shared TypeArena so that TypeIds in cached entries remain
/// valid across all Analyzers that use this cache.
pub struct ModuleCache {
    /// Cached modules keyed by import path (e.g., "std:prelude/string", "std:math")
    entries: HashMap<String, CachedModule>,
    /// Shared type arena - all analyzers using this cache must share this arena
    /// so that TypeIds in cached entries remain valid.
    type_arena: Rc<RefCell<TypeArena>>,
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCache {
    /// Create a new empty cache with a fresh TypeArena.
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
            type_arena: Rc::new(RefCell::new(TypeArena::new())),
        }
    }

    /// Create a shareable cache wrapped in Rc<RefCell>.
    pub fn shared() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self::new()))
    }

    /// Get the shared TypeArena that must be used by all Analyzers using this cache.
    pub fn type_arena(&self) -> Rc<RefCell<TypeArena>> {
        self.type_arena.clone()
    }

    /// Check if a module is cached.
    pub fn contains(&self, import_path: &str) -> bool {
        self.entries.contains_key(import_path)
    }

    /// Get a cached module if available.
    pub fn get(&self, import_path: &str) -> Option<&CachedModule> {
        self.entries.get(import_path)
    }

    /// Store a module in the cache.
    pub fn insert(&mut self, import_path: String, module: CachedModule) {
        self.entries.insert(import_path, module);
    }

    /// Number of cached modules.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if cache is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Clear all cached entries.
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

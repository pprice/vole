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
use crate::sema::resolution::ResolvedMethod;
use crate::sema::types::{FunctionType, ModuleType};
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
    /// Expression types from analysis
    pub expr_types: HashMap<NodeId, super::Type>,
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
#[derive(Default)]
pub struct ModuleCache {
    /// Cached modules keyed by import path (e.g., "std:prelude/string", "std:math")
    entries: HashMap<String, CachedModule>,
}

impl ModuleCache {
    /// Create a new empty cache.
    pub fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Create a shareable cache wrapped in Rc<RefCell>.
    pub fn shared() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self::new()))
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

//! General-purpose module analysis cache.
//!
//! Caches the analysis results of any imported module (stdlib, user modules, etc.)
//! so that multiple files importing the same module don't re-parse and re-analyze it.
//!
//! This is especially useful for:
//! - Test runner: 100+ files all importing the same prelude/stdlib
//! - Large projects: Many files importing shared utilities
//! - Incremental builds: Only re-analyze changed modules
//!
//! ## Design
//!
//! All analyzers using the cache share the same `Rc<RefCell<CompilationDb>>`.
//! This means type definitions, methods, and names are automatically shared -
//! we only need to cache per-module metadata like expression types and method
//! resolutions (which are keyed by NodeId, which is per-program).

use crate::compilation_db::CompilationDb;
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::resolution::ResolvedMethod;
use crate::type_arena::TypeId;
use crate::types::FunctionType;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::rc::Rc;
use vole_frontend::{Interner, NodeId, Program};

/// Result of compile-time analysis for type checks (`is` expressions and type patterns).
///
/// Used to eliminate runtime type lookups when the result can be determined at compile time,
/// or to provide the tag value when a runtime check is needed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsCheckResult {
    /// The check always succeeds (e.g., `x is Int` when x is `Int`)
    AlwaysTrue,
    /// The check always fails (e.g., `x is Int` when x is `String`)
    AlwaysFalse,
    /// Runtime check needed - compare against this union variant tag
    CheckTag(u32),
    /// Runtime check needed for unknown type - compare against this type's tag
    /// The TypeId indicates what type we're checking for at runtime.
    CheckUnknown(TypeId),
}

/// Cached analysis results for a single module.
///
/// Note: Registry data (types, methods, fields) is NOT stored here - it lives
/// in the shared CompilationDb. We only cache per-module metadata that is
/// keyed by NodeId (which is program-specific).
#[derive(Clone)]
pub struct CachedModule {
    /// Parsed program (needed for codegen)
    pub program: Program,
    /// Interner with symbols from this module
    pub interner: Interner,
    /// Expression types from analysis (NodeId → TypeId).
    /// TypeIds are valid because all analyzers share the same TypeArena.
    pub expr_types: FxHashMap<NodeId, TypeId>,
    /// Method resolutions from analysis (NodeId → ResolvedMethod)
    pub method_resolutions: FxHashMap<NodeId, ResolvedMethod>,
    /// Generic function monomorph keys (NodeId -> MonomorphKey)
    pub generic_calls: FxHashMap<NodeId, MonomorphKey>,
    /// Generic class method monomorph keys (NodeId -> ClassMethodMonomorphKey)
    pub class_method_generics: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Generic static method monomorph keys (NodeId -> StaticMethodMonomorphKey)
    pub static_method_generics: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Functions registered by name (for cross-interner lookup)
    pub functions_by_name: FxHashMap<String, FunctionType>,
    /// Type check results for `is` expressions and type patterns (NodeId → IsCheckResult)
    pub is_check_results: FxHashMap<NodeId, IsCheckResult>,
}

/// Cache for module analysis results.
///
/// Thread-local cache that can be shared across multiple Analyzer instances.
/// Use `Rc<RefCell<ModuleCache>>` to share between analyzers in the same thread.
/// The cache includes a shared CompilationDb so that TypeIds in cached entries remain
/// valid across all Analyzers that use this cache.
pub struct ModuleCache {
    /// Cached modules keyed by import path (e.g., "std:prelude/string", "std:math")
    entries: FxHashMap<String, CachedModule>,
    /// Shared compilation database - all analyzers using this cache must share this db
    /// so that TypeIds in cached entries remain valid.
    db: Rc<RefCell<CompilationDb>>,
}

impl Default for ModuleCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ModuleCache {
    /// Create a new empty cache with a fresh CompilationDb.
    pub fn new() -> Self {
        Self {
            entries: FxHashMap::default(),
            db: Rc::new(RefCell::new(CompilationDb::new())),
        }
    }

    /// Create a shareable cache wrapped in Rc<RefCell>.
    pub fn shared() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self::new()))
    }

    /// Get the shared CompilationDb that must be used by all Analyzers using this cache.
    pub fn db(&self) -> Rc<RefCell<CompilationDb>> {
        Rc::clone(&self.db)
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

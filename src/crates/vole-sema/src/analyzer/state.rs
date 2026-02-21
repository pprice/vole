// Per-analysis mutable state structs for the analyzer.

use crate::generic::TypeParamScopeStack;
use crate::module::ModuleLoader;
use crate::scope::Scope;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use std::collections::HashSet;
use std::path::PathBuf;
use vole_frontend::Span;
use vole_frontend::ast::{NodeId, Symbol};
use vole_identity::ModuleId;

use super::{TypeError, TypeWarning};

/// Tracks return analysis results for a code path.
///
/// This struct collects information about return statements encountered during
/// analysis of a block or function body, used to:
/// - Infer return types when not declared
/// - Check for missing returns in non-void functions
/// - Validate return type consistency across branches
#[derive(Default, Clone)]
pub(crate) struct ReturnInfo {
    /// Whether this code path definitely returns or raises.
    /// A path "definitely returns" if every control flow path ends in a
    /// return/raise statement.
    pub definitely_returns: bool,
    /// Types and spans from all return statements encountered on this path.
    /// Used for return type inference, consistency checking, and error reporting.
    /// Each entry is (type, span) where span points to the return expression.
    pub return_types: Vec<(ArenaTypeId, Span)>,
}

/// Information about a captured variable during lambda analysis
#[derive(Debug, Clone)]
pub(crate) struct CaptureInfo {
    pub(crate) name: Symbol,
    pub(crate) is_mutable: bool, // Was the captured variable declared with `let mut`
    pub(crate) is_mutated: bool, // Does the lambda assign to this variable
}

/// Type checking environment: scope, type overrides, and function context.
#[derive(Default)]
pub(crate) struct TypeCheckEnv {
    pub scope: Scope,
    /// Type overrides from flow-sensitive narrowing (e.g., after `if x is T`)
    pub type_overrides: FxHashMap<Symbol, ArenaTypeId>,
    pub current_function_return: Option<ArenaTypeId>,
    /// Current function's error type (if fallible)
    pub current_function_error_type: Option<ArenaTypeId>,
    /// Generator context: if inside a generator function, this holds the Iterator element type.
    /// None means we're not in a generator (or not in a function at all).
    pub current_generator_element_type: Option<ArenaTypeId>,
    /// Whether a `yield` expression was encountered in the current function body.
    /// Reset when entering a function context, used to mark generators in the entity registry.
    pub has_yield: bool,
    /// If we're inside a static method, this holds the method name (for error reporting).
    /// None means we're not in a static method.
    pub current_static_method: Option<String>,
    /// Stack of type parameter scopes for nested generic contexts.
    pub type_param_stack: TypeParamScopeStack,
    /// Parent module IDs for hierarchical resolution (e.g., virtual test modules
    /// that need to see parent module types). These are searched after the current
    /// module but before the builtin module, providing scope inheritance for types.
    pub parent_modules: Vec<ModuleId>,
    /// Priority module for type resolution in tests blocks. When set, this module
    /// is checked BEFORE current_module during type resolution, enabling types
    /// defined in tests blocks to shadow parent module types of the same name.
    pub type_priority_module: Option<ModuleId>,
}

/// Lambda/closure capture analysis state.
#[derive(Default)]
pub(crate) struct LambdaState {
    /// Stack of lambda scopes for capture analysis. Each entry is a FxHashMap
    /// mapping captured variable names to their capture info.
    pub captures: Vec<FxHashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    pub locals: Vec<HashSet<Symbol>>,
    /// Stack of side effect flags for currently analyzed lambdas
    pub side_effects: Vec<bool>,
    /// Variable to lambda expression mapping. Tracks which variables hold lambdas with defaults.
    /// Maps Symbol -> (lambda_node_id, required_params, param_names)
    pub variables: FxHashMap<Symbol, (NodeId, usize, Vec<String>)>,
    /// Depth counter for implicit `it`-lambda contexts.
    /// Incremented when synthesizing an implicit `it => expr` lambda, decremented after.
    /// Used to detect nested `it` usage and emit E2118.
    pub it_lambda_depth: u32,
}

/// Module loading and file context state.
#[derive(Default)]
pub(crate) struct ModuleContext {
    /// Module loader for handling imports
    pub module_loader: ModuleLoader,
    /// Flag to prevent recursive prelude loading
    pub loading_prelude: bool,
    /// Current module being analyzed (for proper NameId registration)
    pub current_module: ModuleId,
    /// Current file path being analyzed (for relative imports).
    /// This is set from the file path passed to Analyzer::new() and updated
    /// when analyzing imported modules.
    pub current_file_path: Option<PathBuf>,
    /// When true, skip processing of `Decl::Tests` in all analysis passes.
    /// Set by `vole run` to avoid sema/codegen cost for tests blocks in production.
    pub skip_tests: bool,
}

/// Diagnostic errors and warnings collected during analysis.
#[derive(Default)]
pub(crate) struct Diagnostics {
    pub errors: Vec<TypeError>,
    pub warnings: Vec<TypeWarning>,
}

// src/sema/analyzer/mod.rs

mod builtins;
mod declarations;
mod errors;
mod expr;
mod inference;
mod lambda;
mod methods;
mod patterns;
mod prelude;
mod stmt;
mod type_helpers;

use crate::ExpressionData;
pub use crate::ResolverEntityExt;
use crate::analysis_cache::{IsCheckResult, ModuleCache};
use crate::compilation_db::CompilationDb;
use crate::entity_defs::TypeDefKind;
use crate::entity_registry::EntityRegistry;
use crate::errors::{SemanticError, SemanticWarning};
use crate::expression_data::LambdaDefaults;
use crate::generic::{
    ClassMethodMonomorphKey, MonomorphInstance, MonomorphKey, StaticMethodMonomorphKey,
    TypeParamInfo, TypeParamScope, TypeParamScopeStack, TypeParamVariance,
};
use crate::implement_registry::{
    ExternalMethodInfo, GenericExternalInfo, ImplTypeId, ImplementRegistry, MethodImpl,
    TypeMappingEntry,
};
use crate::module::ModuleLoader;
use crate::resolution::{MethodResolutions, ResolvedMethod};
use crate::resolve::resolve_type_to_id;
use crate::type_arena::{TypeArena, TypeId as ArenaTypeId};
use crate::types::ConstantValue;
use crate::{
    ErrorTypeInfo, FunctionType, PrimitiveType,
    resolve::TypeResolutionContext,
    scope::{Scope, Variable},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;
use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;
use vole_frontend::*;
use vole_identity::{self, MethodId, ModuleId, NameId, NameTable, Namer, Resolver, TypeDefId};

/// Guard that holds a borrow of the db and provides resolver access.
/// This allows safe access to the resolver without exposing the RefCell directly.
pub struct ResolverGuard<'a> {
    _guard: std::cell::Ref<'a, CompilationDb>,
    interner: &'a Interner,
    module_id: ModuleId,
}

impl<'a> ResolverGuard<'a> {
    fn new(db: &'a RefCell<CompilationDb>, interner: &'a Interner, module_id: ModuleId) -> Self {
        let guard = db.borrow();
        Self {
            _guard: guard,
            interner,
            module_id,
        }
    }

    /// Get the resolver. The lifetime is tied to this guard.
    pub fn resolver(&self) -> Resolver<'_> {
        // SAFETY: We hold the guard, so the borrow is valid
        let names = unsafe { &*(&self._guard.names as *const NameTable) };
        Resolver::new(self.interner, names, self.module_id, &[])
    }

    /// Resolve a Symbol to a TypeDefId through the resolution chain.
    pub fn resolve_type(&self, sym: Symbol, registry: &EntityRegistry) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver().resolve_type(sym, registry)
    }

    /// Resolve a type with fallback to interface/class short name search.
    pub fn resolve_type_or_interface(
        &self,
        sym: Symbol,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver().resolve_type_or_interface(sym, registry)
    }

    /// Resolve a type string with fallback to interface/class short name search.
    pub fn resolve_type_str_or_interface(
        &self,
        name: &str,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver()
            .resolve_type_str_or_interface(name, registry)
    }
}

/// Check if a type param's constraint (found) satisfies a required constraint.
/// Returns true if found has at least as strong constraints as required.
fn constraint_satisfied(
    found: &Option<crate::generic::TypeConstraint>,
    required: &crate::generic::TypeConstraint,
) -> bool {
    use crate::generic::TypeConstraint;

    let Some(found) = found else {
        // Found has no constraint - can only satisfy if required is empty
        return false;
    };

    match (found, required) {
        // Interface constraints: found must have all interfaces that required has
        (
            TypeConstraint::Interface(found_interfaces),
            TypeConstraint::Interface(required_interfaces),
        ) => {
            // All required interfaces must be in the found interfaces
            required_interfaces
                .iter()
                .all(|req| found_interfaces.contains(req))
        }
        // Union constraints: found must be a subset of or equal to required (TypeId version)
        (TypeConstraint::UnionId(found_ids), TypeConstraint::UnionId(required_ids)) => {
            // All found TypeIds must be in the required TypeIds
            found_ids
                .iter()
                .all(|f| required_ids.iter().any(|r| f == r))
        }
        // Structural constraints: more complex matching needed, for now require exact match
        (TypeConstraint::Structural(found_struct), TypeConstraint::Structural(required_struct)) => {
            found_struct == required_struct
        }
        // Different constraint kinds don't satisfy each other
        _ => false,
    }
}

/// Information about a captured variable during lambda analysis
#[derive(Debug, Clone)]
struct CaptureInfo {
    name: Symbol,
    is_mutable: bool, // Was the captured variable declared with `let mut`
    is_mutated: bool, // Does the lambda assign to this variable
}

/// A type error wrapping a miette-enabled SemanticError
#[derive(Debug, Clone)]
pub struct TypeError {
    pub error: SemanticError,
    pub span: Span,
}

impl TypeError {
    /// Create a new type error
    pub fn new(error: SemanticError, span: Span) -> Self {
        Self { error, span }
    }
}

/// A type warning wrapping a miette-enabled SemanticWarning
#[derive(Debug, Clone)]
pub struct TypeWarning {
    pub warning: SemanticWarning,
    pub span: Span,
}

impl TypeWarning {
    /// Create a new type warning
    pub fn new(warning: SemanticWarning, span: Span) -> Self {
        Self { warning, span }
    }
}

/// Output from semantic analysis, bundling all analysis results.
/// Used to construct AnalyzedProgram with program and interner.
pub struct AnalysisOutput {
    /// All expression-level metadata (types, method resolutions, generic calls)
    pub expression_data: ExpressionData,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    pub module_programs: FxHashMap<String, (Program, Interner)>,
    /// Shared compilation database containing all registries
    pub db: Rc<RefCell<CompilationDb>>,
}

/// Tracks return analysis results for a code path.
///
/// This struct collects information about return statements encountered during
/// analysis of a block or function body, used to:
/// - Infer return types when not declared
/// - Check for missing returns in non-void functions
/// - Validate return type consistency across branches
#[derive(Default, Clone)]
#[allow(dead_code)] // Infrastructure for return flow analysis (epic v-d409)
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

#[allow(dead_code)] // Infrastructure for return flow analysis (epic v-d409)
impl ReturnInfo {
    /// Merge another ReturnInfo into this one.
    ///
    /// This combines return types from both paths. The caller is responsible
    /// for handling `definitely_returns` based on the control flow context
    /// (e.g., for if/else both branches must return, for loops the merge
    /// semantics differ).
    pub fn merge(&mut self, other: ReturnInfo) {
        self.return_types.extend(other.return_types);
    }
}

/// Saved state when entering a function/method check context.
/// Used by enter_function_context/exit_function_context for uniform save/restore.
struct FunctionCheckContext {
    return_type: Option<ArenaTypeId>,
    error_type: Option<ArenaTypeId>,
    generator_element_type: Option<ArenaTypeId>,
    static_method: Option<String>,
    /// How many scopes were on the stack when we entered this context
    type_param_stack_depth: usize,
}

pub struct Analyzer {
    scope: Scope,
    functions: FxHashMap<Symbol, FunctionType>,
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    functions_by_name: FxHashMap<String, FunctionType>,
    globals: FxHashMap<Symbol, ArenaTypeId>,
    /// Globals with constant initializers (for constant expression checking)
    constant_globals: HashSet<Symbol>,
    current_function_return: Option<ArenaTypeId>,
    /// Current function's error type (if fallible)
    current_function_error_type: Option<ArenaTypeId>,
    /// Generator context: if inside a generator function, this holds the Iterator element type.
    /// None means we're not in a generator (or not in a function at all).
    current_generator_element_type: Option<ArenaTypeId>,
    /// If we're inside a static method, this holds the method name (for error reporting).
    /// None means we're not in a static method.
    current_static_method: Option<String>,
    errors: Vec<TypeError>,
    warnings: Vec<TypeWarning>,
    /// Type overrides from flow-sensitive narrowing (e.g., after `if x is T`)
    type_overrides: FxHashMap<Symbol, ArenaTypeId>,
    /// Stack of lambda scopes for capture analysis. Each entry is a FxHashMap
    /// mapping captured variable names to their capture info.
    lambda_captures: Vec<FxHashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    lambda_locals: Vec<HashSet<Symbol>>,
    /// Stack of side effect flags for currently analyzed lambdas
    lambda_side_effects: Vec<bool>,
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their interned type handles for O(1) equality.
    expr_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Type check results for `is` expressions and type patterns (for codegen)
    /// Maps NodeId -> IsCheckResult to eliminate runtime type lookups
    is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Resolved method calls for codegen
    pub method_resolutions: MethodResolutions,
    /// Module loader for handling imports
    module_loader: ModuleLoader,
    /// Cached module TypeIds by import path (avoids re-parsing)
    module_type_ids: FxHashMap<String, ArenaTypeId>,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    module_programs: FxHashMap<String, (Program, Interner)>,
    /// Expression types for module programs (keyed by module path -> NodeId -> ArenaTypeId)
    /// Stored separately since NodeIds are per-program and can't be merged into main expr_types.
    /// Uses interned ArenaTypeId handles for O(1) equality during analysis.
    pub module_expr_types: FxHashMap<String, FxHashMap<NodeId, ArenaTypeId>>,
    /// Method resolutions for module programs (keyed by module path -> NodeId -> ResolvedMethod)
    /// Stored separately since NodeIds are per-program and can't be merged into main method_resolutions
    pub module_method_resolutions: FxHashMap<String, FxHashMap<NodeId, ResolvedMethod>>,
    /// Flag to prevent recursive prelude loading
    loading_prelude: bool,
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    generic_calls: FxHashMap<NodeId, MonomorphKey>,
    /// Mapping from method call expression NodeId to ClassMethodMonomorphKey (for generic class method calls)
    class_method_calls: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Mapping from static method call expression NodeId to StaticMethodMonomorphKey (for generic static method calls)
    static_method_calls: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Substituted return types for generic method calls.
    /// When a method like `list.head()` is called on `List<i32>`, the generic return type `T`
    /// is substituted to `i32`. This map stores the concrete type so codegen doesn't recompute.
    substituted_return_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Lambda defaults for closure calls. Maps call site NodeId to lambda info.
    lambda_defaults: FxHashMap<NodeId, LambdaDefaults>,
    /// Variable to lambda expression mapping. Tracks which variables hold lambdas with defaults.
    /// Maps Symbol -> (lambda_node_id, required_params)
    lambda_variables: FxHashMap<Symbol, (NodeId, usize)>,
    /// Scoped function closure types. Maps function declaration span to its closure function type.
    /// Used for scoped functions in test blocks which are compiled as closures.
    scoped_function_types: FxHashMap<Span, ArenaTypeId>,
    /// Declared variable types for let statements with explicit type annotations.
    /// Maps init expression NodeId -> declared TypeId for codegen to use.
    declared_var_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Current module being analyzed (for proper NameId registration)
    current_module: ModuleId,
    /// Stack of type parameter scopes for nested generic contexts.
    type_param_stack: TypeParamScopeStack,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Unified compilation database containing all registries.
    /// Shared via Rc<RefCell> so sub-analyzers use the same db, making TypeIds
    /// valid across all analyzers and eliminating clone/merge operations.
    pub db: Rc<RefCell<CompilationDb>>,
    /// Current file path being analyzed (for relative imports).
    /// This is set from the file path passed to Analyzer::new() and updated
    /// when analyzing imported modules.
    current_file_path: Option<PathBuf>,
}

/// Result of looking up a method on a type via EntityRegistry
pub struct MethodLookup {
    pub method_id: MethodId,
    pub signature_id: ArenaTypeId,
}

impl Analyzer {
    pub fn new(file: &str, _source: &str) -> Self {
        // Create the shared CompilationDb
        let db = Rc::new(RefCell::new(CompilationDb::new()));
        let main_module = db.borrow().main_module();

        // Determine current file path and project root
        let file_path = std::path::Path::new(file);
        let current_file_path = file_path.canonicalize().ok();
        let project_root = current_file_path
            .as_ref()
            .map(|p| ModuleLoader::detect_project_root(p));

        let mut module_loader = ModuleLoader::new();
        if let Some(root) = project_root {
            module_loader.set_project_root(root);
        }

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            module_loader,
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: main_module,
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,
            db,
            current_file_path,
        };

        // Register built-in interfaces and implementations
        // NOTE: This is temporary - will eventually come from stdlib/traits.void
        analyzer.register_builtins();

        analyzer
    }

    /// Create an analyzer with a shared module cache.
    /// The cache is shared across multiple Analyzer instances to avoid
    /// re-analyzing the same modules (prelude, stdlib, user imports).
    /// The analyzer uses the CompilationDb from the cache to ensure TypeIds remain valid.
    pub fn with_cache(file: &str, _source: &str, cache: Rc<RefCell<ModuleCache>>) -> Self {
        // Get the shared db from the cache BEFORE borrowing cache again
        let shared_db = cache.borrow().db();
        let main_module = shared_db.borrow().main_module();

        // Determine current file path and project root
        let file_path = std::path::Path::new(file);
        let current_file_path = file_path.canonicalize().ok();
        let project_root = current_file_path
            .as_ref()
            .map(|p| ModuleLoader::detect_project_root(p));

        let mut module_loader = ModuleLoader::new();
        if let Some(root) = project_root {
            module_loader.set_project_root(root);
        }

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            module_loader,
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: main_module,
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: Some(cache),
            db: shared_db,
            current_file_path,
        };

        // Register built-in interfaces and implementations
        // NOTE: This is temporary - will eventually come from stdlib/traits.void
        analyzer.register_builtins();

        analyzer
    }

    /// Create an analyzer with an explicit project root override.
    /// If `project_root` is `None`, auto-detects from file path.
    pub fn with_project_root(
        file: &str,
        _source: &str,
        project_root: Option<&std::path::Path>,
    ) -> Self {
        // Create the shared CompilationDb
        let db = Rc::new(RefCell::new(CompilationDb::new()));
        let main_module = db.borrow().main_module();

        // Determine current file path
        let file_path = std::path::Path::new(file);
        let current_file_path = file_path.canonicalize().ok();

        // Use explicit project root or auto-detect
        let effective_root = if let Some(root) = project_root {
            Some(root.to_path_buf())
        } else {
            current_file_path
                .as_ref()
                .map(|p| ModuleLoader::detect_project_root(p))
        };

        let mut module_loader = ModuleLoader::new();
        if let Some(root) = effective_root {
            module_loader.set_project_root(root);
        }

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            module_loader,
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: main_module,
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,
            db,
            current_file_path,
        };

        // Register built-in interfaces and implementations
        analyzer.register_builtins();

        analyzer
    }

    /// Create an analyzer with a shared module cache and an explicit project root override.
    /// If `project_root` is `None`, auto-detects from file path.
    pub fn with_cache_and_project_root(
        file: &str,
        _source: &str,
        cache: Rc<RefCell<ModuleCache>>,
        project_root: Option<&std::path::Path>,
    ) -> Self {
        // Get the shared db from the cache BEFORE borrowing cache again
        let shared_db = cache.borrow().db();
        let main_module = shared_db.borrow().main_module();

        // Determine current file path
        let file_path = std::path::Path::new(file);
        let current_file_path = file_path.canonicalize().ok();

        // Use explicit project root or auto-detect
        let effective_root = if let Some(root) = project_root {
            Some(root.to_path_buf())
        } else {
            current_file_path
                .as_ref()
                .map(|p| ModuleLoader::detect_project_root(p))
        };

        let mut module_loader = ModuleLoader::new();
        if let Some(root) = effective_root {
            module_loader.set_project_root(root);
        }

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            module_loader,
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: main_module,
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: Some(cache),
            db: shared_db,
            current_file_path,
        };

        // Register built-in interfaces and implementations
        analyzer.register_builtins();

        analyzer
    }

    // Builtin registration: builtins.rs
    // Prelude loading: prelude.rs
    // Error/display helpers: errors.rs
    // Type inference: inference.rs

    /// Get the resolved expression types as interned ArenaTypeId handles.
    pub fn expr_types(&self) -> &FxHashMap<NodeId, ArenaTypeId> {
        &self.expr_types
    }

    /// Get the type check results for `is` expressions and type patterns.
    pub fn is_check_results(&self) -> &FxHashMap<NodeId, IsCheckResult> {
        &self.is_check_results
    }

    /// Get a resolver configured for the current module context.
    /// Uses the resolution chain: primitives -> current module -> builtin module.
    /// Note: Returns a Resolver that borrows the db's name_table.
    /// The caller must ensure the returned Resolver doesn't outlive the borrow.
    pub fn resolver_with_db<'a>(
        &'a self,
        interner: &'a Interner,
        db: &'a CompilationDb,
    ) -> Resolver<'a> {
        // For now, we don't track imports at the Analyzer level.
        // The resolver will check: primitives, current module, then builtin module.
        Resolver::new(interner, &db.names, self.current_module, &[])
    }

    /// Create a resolver for name resolution.
    /// Note: The returned resolver holds a borrow of the db's name_table.
    pub fn resolver<'a>(&'a self, interner: &'a Interner) -> ResolverGuard<'a> {
        ResolverGuard::new(&self.db, interner, self.current_module)
    }

    /// Take ownership of the expression types (consuming self)
    pub fn into_expr_types(self) -> FxHashMap<NodeId, ArenaTypeId> {
        self.expr_types
    }

    /// Take accumulated warnings, leaving the warnings list empty
    pub fn take_warnings(&mut self) -> Vec<TypeWarning> {
        std::mem::take(&mut self.warnings)
    }

    /// Take ownership of analysis results (consuming self)
    pub fn into_analysis_results(self) -> AnalysisOutput {
        let expression_data = ExpressionData::from_analysis(
            self.expr_types,
            self.method_resolutions.into_inner(),
            self.generic_calls,
            self.class_method_calls,
            self.static_method_calls,
            self.module_expr_types,
            self.module_method_resolutions,
            self.substituted_return_types,
            self.lambda_defaults,
            self.scoped_function_types,
            self.is_check_results,
            self.declared_var_types,
        );
        AnalysisOutput {
            expression_data,
            module_programs: self.module_programs,
            db: self.db,
        }
    }

    /// Record the resolved type for an expression using TypeId directly.
    /// Also pre-creates RuntimeIterator types for Iterator<T> return types,
    /// so codegen can look them up without needing mutable arena access.
    fn record_expr_type_id(&mut self, expr: &Expr, type_id: ArenaTypeId) -> ArenaTypeId {
        // Pre-create RuntimeIterator(T) for Iterator<T> types so codegen can look them up
        self.ensure_runtime_iterator_for_iterator(type_id);
        self.expr_types.insert(expr.id, type_id);
        type_id
    }

    /// Record the result of a type check (is expression or type pattern) for codegen.
    fn record_is_check_result(&mut self, node_id: NodeId, result: IsCheckResult) {
        self.is_check_results.insert(node_id, result);
    }

    /// Get the display name for a type parameter.
    /// For synthetic type params (created for implicit generification), we use the name_id
    /// since the Symbol is not a real interned string.
    fn get_type_param_display_name(&self, param: &TypeParamInfo, interner: &Interner) -> String {
        // Synthetic type params have Symbol values >= 0x80000000
        // (we use Symbol(0x8000_0000 + i) for them)
        if param.name.0 >= 0x8000_0000 {
            // Use name_id for synthetic type params
            self.name_table()
                .last_segment_str(param.name_id)
                .unwrap_or_else(|| format!("__T{}", param.name.0 - 0x8000_0000))
        } else {
            // Use normal interner resolution
            interner.resolve(param.name).to_string()
        }
    }

    /// If the given type is Iterator<T>, ensure RuntimeIterator(T) exists in the arena.
    /// This allows codegen to convert Iterator return types to RuntimeIterator without
    /// needing mutable arena access.
    fn ensure_runtime_iterator_for_iterator(&mut self, type_id: ArenaTypeId) {
        // Check if this is an Iterator interface type
        let elem_type_id = {
            let arena = self.type_arena();
            if let Some((type_def_id, type_args)) = arena.unwrap_interface(type_id) {
                // Get the type's name_id from the registry
                let type_name_id = self.entity_registry().get_type(type_def_id).name_id;
                // Check if it's the Iterator interface by looking up the type name
                let is_iterator = self
                    .name_table()
                    .last_segment_str(type_name_id)
                    .is_some_and(|name| name == "Iterator");
                if is_iterator {
                    type_args.first().copied()
                } else {
                    None
                }
            } else {
                None
            }
        };

        // Create the RuntimeIterator type if needed
        if let Some(elem) = elem_type_id {
            self.type_arena_mut().runtime_iterator(elem);
        }
    }

    // === Backward-compatible accessors for db fields ===
    // These methods provide the old access patterns while using the shared db.

    /// Get the type arena (read access)
    #[inline]
    fn type_arena(&self) -> std::cell::Ref<'_, TypeArena> {
        std::cell::Ref::map(self.db.borrow(), |db| &*db.types)
    }

    /// Get the type arena (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn type_arena_mut(&self) -> std::cell::RefMut<'_, TypeArena> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| db.types_mut())
    }

    /// Get the entity registry (read access)
    #[inline]
    fn entity_registry(&self) -> std::cell::Ref<'_, EntityRegistry> {
        std::cell::Ref::map(self.db.borrow(), |db| &*db.entities)
    }

    /// Get the entity registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn entity_registry_mut(&self) -> std::cell::RefMut<'_, EntityRegistry> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| db.entities_mut())
    }

    /// Get the name table (read access)
    #[inline]
    fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        std::cell::Ref::map(self.db.borrow(), |db| &db.names)
    }

    /// Get the name table (write access)
    #[inline]
    fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| &mut db.names)
    }

    /// Get the implement registry (read access)
    #[inline]
    fn implement_registry(&self) -> std::cell::Ref<'_, ImplementRegistry> {
        std::cell::Ref::map(self.db.borrow(), |db| &*db.implements)
    }

    /// Get the implement registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn implement_registry_mut(&self) -> std::cell::RefMut<'_, ImplementRegistry> {
        std::cell::RefMut::map(self.db.borrow_mut(), |db| db.implements_mut())
    }

    /// Pre-compute substituted field types for a generic class/record instantiation.
    ///
    /// When creating a type like Box<String>, this ensures that the substituted field
    /// types (e.g., String for a field of type T) exist in the arena. This allows
    /// codegen to use lookup_substitute instead of substitute, making it fully read-only.
    fn precompute_field_substitutions(&self, type_def_id: TypeDefId, type_args: &[ArenaTypeId]) {
        // Skip if no type arguments (no substitution needed)
        if type_args.is_empty() {
            return;
        }

        // Get field types and type params from the type definition
        let (field_types, type_params): (Vec<ArenaTypeId>, Vec<NameId>) = {
            let registry = self.entity_registry();
            let type_def = registry.get_type(type_def_id);
            if let Some(generic_info) = &type_def.generic_info {
                (
                    generic_info.field_types.clone(),
                    type_def.type_params.clone(),
                )
            } else {
                return;
            }
        };

        // Build substitution map: type param NameId -> concrete TypeId
        let subs: FxHashMap<NameId, ArenaTypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        // Pre-compute substituted types for all fields
        // This ensures they exist in the arena for codegen's lookup_substitute
        let mut arena = self.type_arena_mut();
        for field_type in field_types {
            arena.substitute(field_type, &subs);
        }
    }

    /// Pre-compute substituted method signatures for an interface instantiation.
    ///
    /// When a concrete type implements an interface (via implements clause or interface boxing),
    /// this ensures that the substituted method param/return types exist in the arena.
    /// This allows codegen to use lookup_substitute instead of substitute when building vtables.
    fn precompute_interface_method_substitutions(
        &self,
        interface_type_def_id: TypeDefId,
        type_args: &[ArenaTypeId],
    ) {
        // Skip if no type arguments (no substitution needed)
        if type_args.is_empty() {
            return;
        }

        // Get interface type params and method signature IDs upfront
        // to avoid borrow conflicts with the arena
        let (type_params, signature_ids): (Vec<NameId>, Vec<ArenaTypeId>) = {
            let registry = self.entity_registry();
            let type_params = registry.get_type(interface_type_def_id).type_params.clone();
            let method_ids = registry.interface_methods_ordered(interface_type_def_id);
            let signature_ids: Vec<ArenaTypeId> = method_ids
                .iter()
                .map(|&mid| registry.get_method(mid).signature_id)
                .collect();
            (type_params, signature_ids)
        };

        // Skip if type params and args don't match (error case handled elsewhere)
        if type_params.len() != type_args.len() {
            return;
        }

        // Build substitution map: type param NameId -> concrete TypeId
        let subs: FxHashMap<NameId, ArenaTypeId> = type_params
            .iter()
            .zip(type_args.iter())
            .map(|(&param, &arg)| (param, arg))
            .collect();

        // Pre-compute substituted types for all method signatures
        // This ensures they exist in the arena for codegen's lookup_substitute
        let mut arena = self.type_arena_mut();
        for signature_id in signature_ids {
            // Get method param and return types
            if let Some((params, ret, _)) = arena.unwrap_function(signature_id) {
                // Substitute each param type
                let params = params.to_vec();
                for param in params {
                    arena.substitute(param, &subs);
                }
                // Substitute return type
                arena.substitute(ret, &subs);
            }
        }
    }

    /// Check if we're currently inside a lambda
    fn in_lambda(&self) -> bool {
        !self.lambda_captures.is_empty()
    }

    /// Check if a symbol is a local variable in the current lambda
    fn is_lambda_local(&self, sym: Symbol) -> bool {
        if let Some(locals) = self.lambda_locals.last() {
            locals.contains(&sym)
        } else {
            false
        }
    }

    /// Add a local variable to the current lambda's locals set
    fn add_lambda_local(&mut self, sym: Symbol) {
        if let Some(locals) = self.lambda_locals.last_mut() {
            locals.insert(sym);
        }
    }

    /// Record a captured variable in the current lambda
    fn record_capture(&mut self, sym: Symbol, is_mutable: bool) {
        if let Some(captures) = self.lambda_captures.last_mut() {
            // Only add if not already captured
            captures.entry(sym).or_insert(CaptureInfo {
                name: sym,
                is_mutable,
                is_mutated: false,
            });
        }
    }

    /// Mark a captured variable as mutated
    fn mark_capture_mutated(&mut self, sym: Symbol) {
        if let Some(captures) = self.lambda_captures.last_mut()
            && let Some(info) = captures.get_mut(&sym)
        {
            info.is_mutated = true;
        }
    }

    fn module_name_id(&self, module_id: ModuleId, name: &str) -> Option<NameId> {
        let module_path = {
            let table = self.name_table();
            table.module_path(module_id).to_string()
        };
        let (_, module_interner) = self.module_programs.get(&module_path)?;
        let sym = module_interner.lookup(name)?;
        self.name_table()
            .name_id(module_id, &[sym], module_interner)
    }

    /// Create an interface TypeId by name (e.g., "Iterator").
    fn interface_type_id(
        &mut self,
        name: &str,
        type_args_id: &[crate::type_arena::TypeId],
        interner: &Interner,
    ) -> Option<crate::type_arena::TypeId> {
        // Look up interface by string name using resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(name, &self.entity_registry())?;
        let type_params_len = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).type_params.len()
        };

        // Check type params match
        if type_params_len != 0 && type_params_len != type_args_id.len() {
            return Some(crate::type_arena::TypeId::INVALID);
        }

        // Create interface type directly in arena
        let type_args_vec: crate::type_arena::TypeIdVec = type_args_id.iter().copied().collect();
        let type_id = self.type_arena_mut().interface(type_def_id, type_args_vec);
        // Pre-compute substituted method signatures so codegen can use lookup_substitute
        self.precompute_interface_method_substitutions(type_def_id, type_args_id);
        Some(type_id)
    }

    fn method_name_id(&mut self, name: Symbol, interner: &Interner) -> NameId {
        let mut name_table = self.name_table_mut();
        let mut namer = Namer::new(&mut name_table, interner);
        namer.method(name)
    }

    /// Look up a method NameId by string name (cross-interner safe)
    fn method_name_id_by_str(&self, name_str: &str, interner: &Interner) -> Option<NameId> {
        vole_identity::method_name_id_by_str(&self.name_table(), interner, name_str)
    }

    /// Look up a method on a type via EntityRegistry
    fn lookup_method(
        &mut self,
        type_def_id: TypeDefId,
        method_name: Symbol,
        interner: &Interner,
    ) -> Option<MethodLookup> {
        let method_name_id = self.method_name_id(method_name, interner);
        let method_id = self
            .entity_registry()
            .find_method_on_type(type_def_id, method_name_id)?;
        let signature_id = {
            let registry = self.entity_registry();
            registry.get_method(method_id).signature_id
        };
        Some(MethodLookup {
            method_id,
            signature_id,
        })
    }

    /// Mark the current lambda as having side effects
    fn mark_lambda_has_side_effects(&mut self) {
        if let Some(flag) = self.lambda_side_effects.last_mut() {
            *flag = true;
        }
    }

    /// Get variable type as TypeId with flow-sensitive overrides
    fn get_variable_type_id(&self, sym: Symbol) -> Option<ArenaTypeId> {
        // Check overrides first (for narrowed types inside if-blocks)
        if let Some(ty) = self.type_overrides.get(&sym) {
            return Some(*ty);
        }
        // Then check scope
        self.scope.get(sym).map(|v| v.ty)
    }

    /// Get function type if the symbol refers to a top-level function.
    /// Returns None if the symbol is not a function name.
    fn get_function_type(&self, sym: Symbol, interner: &Interner) -> Option<FunctionType> {
        // Check by Symbol first (same interner)
        if let Some(func_type) = self.functions.get(&sym) {
            return Some(func_type.clone());
        }
        // Check by name for prelude functions (cross-interner lookup)
        let name = interner.resolve(sym);
        self.functions_by_name.get(name).cloned()
    }

    #[tracing::instrument(skip(self, program, interner))]
    pub fn analyze(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        self.register_primitive_name_ids(interner);
        self.register_builtin_methods(interner);

        // Load prelude (trait definitions and primitive type implementations)
        // This makes stdlib methods like "hello".length() available without explicit imports
        self.load_prelude(interner);

        // Clear monomorph caches from any previous analysis.
        // When using a shared ModuleCache across multiple test files, the entity_registry
        // accumulates monomorph instances from previous files. These instances reference
        // class/method definitions that exist only in those previous files, causing
        // "method X not found in class/record Y" errors during codegen. Clearing these
        // caches ensures each main program analysis starts fresh while still benefiting
        // from cached prelude analysis (prelude modules don't have generic classes that
        // get monomorphized in the main program).
        self.entity_registry_mut().clear_monomorph_caches();

        // Populate well-known types after prelude has registered all interfaces
        self.name_table_mut().populate_well_known();

        // Pass 0.5: Register type shells for forward reference support
        // This allows types to reference each other regardless of declaration order
        self.register_all_type_shells(program, interner);

        // Pass 0: Resolve type aliases (now that shells exist, can reference forward types)
        self.collect_type_aliases(program, interner);

        // Pass 0.75: Process module imports so they're available for implement block resolution
        self.process_module_imports(program, interner);

        // Pass 1: Collect signatures for all declarations (shells already exist)
        self.collect_signatures(program, interner);

        // Populate well-known TypeDefIds now that interfaces are registered
        // Destructure db to allow simultaneous mutable and immutable borrows of different fields
        {
            let mut db = self.db.borrow_mut();
            let CompilationDb {
                ref mut names,
                ref entities,
                ..
            } = *db;
            crate::well_known::populate_type_def_ids(names, entities);
        }

        // Process global let declarations
        self.process_global_lets(program, interner)?;

        // Pass 2: type check function bodies and tests
        self.check_declaration_bodies(program, interner)?;

        // Pass 3: analyze monomorphized function bodies to discover nested generic calls
        // This iterates until no new MonomorphInstances are created
        self.analyze_monomorph_bodies(program, interner);

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    /// Resolve a type expression to TypeId.
    pub(crate) fn resolve_type_id(&mut self, ty: &TypeExpr, interner: &Interner) -> ArenaTypeId {
        self.resolve_type_id_with_self(ty, interner, None)
    }

    /// Resolve a type expression to TypeId with optional Self type for method signatures
    pub(crate) fn resolve_type_id_with_self(
        &mut self,
        ty: &TypeExpr,
        interner: &Interner,
        self_type_id: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        let module_id = self.current_module;
        let mut ctx = TypeResolutionContext {
            db: &self.db,
            interner,
            module_id,
            type_params: self.type_param_stack.current(),
            self_type: self_type_id,
        };
        resolve_type_to_id(ty, &mut ctx)
    }

    /// Pass 0: Collect type aliases (so they're available for function signatures)
    fn collect_type_aliases(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(type_expr) => {
                        let aliased_type_id = self.resolve_type_id(type_expr, interner);
                        self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                    }
                    LetInit::Expr(init_expr) => {
                        // Legacy: handle let X: type = SomeType
                        if let ExprKind::TypeLiteral(type_expr) = &init_expr.kind {
                            let aliased_type_id = self.resolve_type_id(type_expr, interner);
                            self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                        }
                    }
                }
            }
        }
    }

    /// Register a type alias in EntityRegistry
    fn register_type_alias_id(
        &mut self,
        name: Symbol,
        aliased_type_id: ArenaTypeId,
        interner: &Interner,
    ) {
        // Lookup shell registered in register_all_type_shells
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[name], interner);
        let type_id = self
            .entity_registry_mut()
            .type_by_name(name_id)
            .expect("alias shell registered in register_all_type_shells");
        // Set the aliased type (uses TypeId directly as alias index key)
        self.entity_registry_mut()
            .set_aliased_type(type_id, aliased_type_id);
    }

    /// Process module imports early so they're available for qualified implement syntax.
    /// This runs before signature collection to allow `implement mod.Interface for Type`.
    fn process_module_imports(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl
                && let LetInit::Expr(init_expr) = &let_stmt.init
                && let ExprKind::Import(import_path) = &init_expr.kind
            {
                // Process the import and register the binding
                if let Ok(module_type_id) =
                    self.analyze_module(import_path, init_expr.span, interner)
                {
                    // Register in scope so it's available for implement block resolution
                    self.scope.define(
                        let_stmt.name,
                        Variable {
                            ty: module_type_id,
                            mutable: false,
                        },
                    );
                    // Also register in globals for consistency
                    self.globals.insert(let_stmt.name, module_type_id);
                    // Record the expression type so codegen can look it up
                    self.record_expr_type_id(init_expr, module_type_id);
                }
            }

            // Handle destructuring imports: let { x, y } = import "..."
            if let Decl::LetTuple(let_tuple) = decl
                && let ExprKind::Import(import_path) = &let_tuple.init.kind
            {
                // Process the import
                if let Ok(module_type_id) =
                    self.analyze_module(import_path, let_tuple.init.span, interner)
                {
                    // Record the expression type for the import
                    self.record_expr_type_id(&let_tuple.init, module_type_id);
                    // Destructure the module exports into scope
                    self.check_destructure_pattern_id(
                        &let_tuple.pattern,
                        module_type_id,
                        let_tuple.mutable,
                        let_tuple.init.span,
                        interner,
                    );
                }
            }
        }
    }

    /// Process global let declarations (type check and add to scope)
    fn process_global_lets(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(_) => {
                        // Type aliases are already handled in collect_type_aliases
                    }
                    LetInit::Expr(init_expr) => {
                        // Skip imports - already handled in process_module_imports
                        if matches!(&init_expr.kind, ExprKind::Import(_)) {
                            continue;
                        }

                        // Check for ambiguous type alias: let Alias = TypeName
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            if self
                                .resolver(interner)
                                .resolve_type(*ident_sym, &self.entity_registry())
                                .is_some()
                            {
                                let let_name = interner.resolve(let_stmt.name);
                                self.add_error(
                                    SemanticError::AmbiguousTypeAlias {
                                        name: let_name.to_string(),
                                        type_name: ident_name.to_string(),
                                        span: init_expr.span.into(),
                                    },
                                    init_expr.span,
                                );
                            }
                        }

                        let declared_type_id = let_stmt
                            .ty
                            .as_ref()
                            .map(|t| self.resolve_type_id(t, interner));
                        let init_type_id =
                            self.check_expr_expecting_id(init_expr, declared_type_id, interner)?;

                        // Check if trying to use void return value
                        if init_type_id == ArenaTypeId::VOID {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type_id = declared_type_id.unwrap_or(init_type_id);

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type_id == ArenaTypeId::METATYPE
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type_id = self.resolve_type_id(type_expr, interner);
                            self.register_type_alias_id(let_stmt.name, aliased_type_id, interner);
                        }
                        self.globals.insert(let_stmt.name, var_type_id);
                        self.scope.define(
                            let_stmt.name,
                            Variable {
                                ty: var_type_id,
                                mutable: let_stmt.mutable,
                            },
                        );

                        // Track if this immutable global has a constant initializer
                        // This enables using it in other constant expressions (e.g., default params)
                        if !let_stmt.mutable && self.is_constant_expr(init_expr) {
                            self.constant_globals.insert(let_stmt.name);
                        }

                        // Register in entity registry for proper global variable tracking
                        let global_name_id = self.name_table_mut().intern(
                            self.current_module,
                            &[let_stmt.name],
                            interner,
                        );
                        self.entity_registry_mut().register_global(
                            global_name_id,
                            var_type_id,
                            self.current_module,
                            let_stmt.mutable,
                            init_expr.id,
                        );
                    }
                }
            }

            // Handle destructuring let declarations: let { x, y } = expr
            if let Decl::LetTuple(let_tuple) = decl {
                // Skip imports - already handled in process_module_imports
                if matches!(&let_tuple.init.kind, ExprKind::Import(_)) {
                    continue;
                }

                // Check the initializer expression
                let init_type_id = self.check_expr(&let_tuple.init, interner)?;
                self.check_destructure_pattern_id(
                    &let_tuple.pattern,
                    init_type_id,
                    let_tuple.mutable,
                    let_tuple.init.span,
                    interner,
                );
            }
        }
        Ok(())
    }

    /// Pass 2: Type check function bodies, tests, and methods
    fn check_declaration_bodies(
        &mut self,
        program: &Program,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for decl in &program.declarations {
            match decl {
                Decl::Function(func) => {
                    self.check_function(func, interner)?;
                }
                Decl::Tests(tests_decl) => {
                    self.check_tests(tests_decl, interner)?;
                }
                Decl::Let(_) | Decl::LetTuple(_) => {
                    // Already processed in process_global_lets/process_module_imports
                }
                Decl::Class(class) => {
                    // Set up type param scope for generic class methods
                    // This allows method resolution to use constraint interfaces
                    let generic_type_params = if !class.type_params.is_empty() {
                        let class_name_id =
                            self.name_table()
                                .name_id(self.current_module, &[class.name], interner);
                        class_name_id.and_then(|class_name_id| {
                            let registry = self.entity_registry();
                            registry
                                .type_by_name(class_name_id)
                                .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                                .map(|gi| gi.type_params.clone())
                        })
                    } else {
                        None
                    };
                    if let Some(ref type_params) = generic_type_params {
                        let mut scope = TypeParamScope::new();
                        for tp in type_params {
                            scope.add(tp.clone());
                        }
                        self.type_param_stack.push_scope(scope);
                    }

                    // Type-check field default expressions
                    {
                        let class_name_id =
                            self.name_table()
                                .name_id(self.current_module, &[class.name], interner);
                        let field_types = class_name_id.and_then(|class_name_id| {
                            let registry = self.entity_registry();
                            registry
                                .type_by_name(class_name_id)
                                .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                                .map(|gi| gi.field_types.clone())
                        });
                        if let Some(field_types) = field_types {
                            self.check_field_defaults(&class.fields, &field_types, interner)?;
                        }
                    }

                    for method in &class.methods {
                        self.check_method(method, class.name, interner)?;
                    }
                    // Check static methods if present
                    if let Some(ref statics) = class.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, class.name, interner)?;
                        }
                    }

                    // Pop type param scope after checking methods
                    if generic_type_params.is_some() {
                        self.type_param_stack.pop();
                    }
                    // Validate interface satisfaction via EntityRegistry
                    let maybe_type_def_id = {
                        let class_name_id =
                            self.name_table()
                                .name_id(self.current_module, &[class.name], interner);
                        class_name_id.and_then(|class_name_id| {
                            let registry = self.entity_registry();
                            registry.type_by_name(class_name_id)
                        })
                    };
                    if let Some(type_def_id) = maybe_type_def_id {
                        let type_methods = self.get_type_method_signatures(class.name, interner);
                        let interface_ids = self
                            .entity_registry()
                            .get_implemented_interfaces(type_def_id);
                        for interface_id in interface_ids {
                            let interface_name_id = {
                                let registry = self.entity_registry();
                                registry.get_type(interface_id).name_id
                            };
                            let iface_name_str =
                                self.name_table().last_segment_str(interface_name_id);
                            if let Some(iface_name_str) = iface_name_str
                                && let Some(iface_name) = interner.lookup(&iface_name_str)
                            {
                                self.validate_interface_satisfaction(
                                    class.name,
                                    iface_name,
                                    &type_methods,
                                    class.span,
                                    interner,
                                );
                            }
                        }
                    }
                }
                Decl::Record(record) => {
                    // Set up type param scope for generic record methods
                    // This allows method resolution to use constraint interfaces
                    let generic_type_params = if !record.type_params.is_empty() {
                        let record_name_id = {
                            self.name_table()
                                .name_id(self.current_module, &[record.name], interner)
                        };
                        record_name_id.and_then(|record_name_id| {
                            let registry = self.entity_registry();
                            registry
                                .type_by_name(record_name_id)
                                .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                                .map(|gi| gi.type_params.clone())
                        })
                    } else {
                        None
                    };
                    if let Some(type_params) = &generic_type_params {
                        let mut scope = TypeParamScope::new();
                        for tp in type_params {
                            scope.add(tp.clone());
                        }
                        self.type_param_stack.push_scope(scope);
                    }

                    // Type-check field default expressions
                    {
                        let record_name_id = self.name_table().name_id(
                            self.current_module,
                            &[record.name],
                            interner,
                        );
                        let field_types = record_name_id.and_then(|record_name_id| {
                            let registry = self.entity_registry();
                            registry
                                .type_by_name(record_name_id)
                                .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                                .map(|gi| gi.field_types.clone())
                        });
                        if let Some(field_types) = field_types {
                            self.check_field_defaults(&record.fields, &field_types, interner)?;
                        }
                    }

                    for method in &record.methods {
                        self.check_method(method, record.name, interner)?;
                    }
                    // Check static methods if present
                    if let Some(ref statics) = record.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, record.name, interner)?;
                        }
                    }

                    // Pop type param scope after checking methods
                    if !record.type_params.is_empty() {
                        self.type_param_stack.pop();
                    }

                    // Validate interface satisfaction via EntityRegistry
                    let maybe_type_def_id = {
                        let record_name_id = self.name_table().name_id(
                            self.current_module,
                            &[record.name],
                            interner,
                        );
                        record_name_id
                            .and_then(|name_id| self.entity_registry().type_by_name(name_id))
                    };
                    if let Some(type_def_id) = maybe_type_def_id {
                        let type_methods = self.get_type_method_signatures(record.name, interner);
                        let interface_ids = self
                            .entity_registry()
                            .get_implemented_interfaces(type_def_id);
                        for interface_id in interface_ids {
                            let interface_name_id = {
                                let registry = self.entity_registry();
                                registry.get_type(interface_id).name_id
                            };
                            let iface_name_str =
                                self.name_table().last_segment_str(interface_name_id);
                            if let Some(iface_name_str) = iface_name_str
                                && let Some(iface_name) = interner.lookup(&iface_name_str)
                            {
                                self.validate_interface_satisfaction(
                                    record.name,
                                    iface_name,
                                    &type_methods,
                                    record.span,
                                    interner,
                                );
                            }
                        }
                    }
                }
                Decl::Interface(interface_decl) => {
                    // Check static method default bodies
                    if let Some(ref statics) = interface_decl.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, interface_decl.name, interner)?;
                        }
                    }
                }
                Decl::Implement(impl_block) => {
                    // Check static methods in implement blocks
                    if let Some(ref statics) = impl_block.statics {
                        match &impl_block.target_type {
                            TypeExpr::Named(type_name) => {
                                for method in &statics.methods {
                                    self.check_static_method(method, *type_name, interner)?;
                                }
                            }
                            TypeExpr::Primitive(prim) => {
                                // Get TypeDefId for primitive
                                let type_def_id = {
                                    let name_id = self.name_table().primitives.from_ast(*prim);
                                    self.entity_registry().type_by_name(name_id)
                                };
                                if let Some(type_def_id) = type_def_id {
                                    for method in &statics.methods {
                                        self.check_static_method_with_type_def(
                                            method,
                                            type_def_id,
                                            interner,
                                        )?;
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
                Decl::Error(_) => {
                    // Error declarations fully processed in first pass
                }
                Decl::External(_) => {
                    // External blocks are processed during code generation
                }
            }
        }
        Ok(())
    }

    fn analyze_error_decl(&mut self, decl: &ErrorDecl, interner: &Interner) {
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[decl.name], interner);

        // Register in EntityRegistry first to get TypeDefId
        let entity_type_id = self.entity_registry_mut().register_type(
            name_id,
            TypeDefKind::ErrorType,
            self.current_module,
        );

        let error_info = ErrorTypeInfo {
            type_def_id: entity_type_id,
        };

        // Set error info for lookup
        self.entity_registry_mut()
            .set_error_info(entity_type_id, error_info);

        // Register fields in EntityRegistry - resolve types directly to TypeId
        let builtin_module = self.name_table_mut().builtin_module();
        let type_name_str = interner.resolve(decl.name);
        for (i, field) in decl.fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let field_name_id = self
                .name_table_mut()
                .intern_raw(builtin_module, &[field_name_str]);
            let full_field_name_id = self
                .name_table_mut()
                .intern_raw(self.current_module, &[type_name_str, field_name_str]);

            // Resolve field type directly to TypeId
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext {
                db: &self.db,
                interner,
                module_id,
                type_params: None,
                self_type: None,
            };
            let field_type_id = resolve_type_to_id(&field.ty, &mut ctx);

            self.entity_registry_mut().register_field(
                entity_type_id,
                field_name_id,
                full_field_name_id,
                field_type_id,
                i,
            );
        }
    }

    fn resolve_type_param_constraint(
        &mut self,
        constraint: &TypeConstraint,
        type_param_scope: &TypeParamScope,
        interner: &Interner,
        span: Span,
    ) -> Option<crate::generic::TypeConstraint> {
        tracing::debug!(?constraint, "resolve_type_param_constraint");
        match constraint {
            TypeConstraint::Interface(syms) => {
                tracing::debug!(
                    num_interfaces = syms.len(),
                    "processing interface constraint"
                );
                // For single interface, check if it's a type alias first
                if syms.len() == 1 {
                    let sym = syms[0];
                    if let Some(type_def_id) = self
                        .resolver(interner)
                        .resolve_type(sym, &self.entity_registry())
                    {
                        let (kind, aliased_type) = {
                            let registry = self.entity_registry();
                            let type_def = registry.get_type(type_def_id);
                            (type_def.kind, type_def.aliased_type)
                        };
                        if kind == TypeDefKind::Alias
                            && let Some(aliased_type_id) = aliased_type
                        {
                            // Use TypeId directly - check what kind of type it is
                            let arena = self.type_arena();

                            // Check if it's a structural type - return as Structural constraint
                            if let Some(structural) = arena.unwrap_structural(aliased_type_id) {
                                return Some(crate::generic::TypeConstraint::Structural(
                                    structural.clone(),
                                ));
                            }

                            // Check if it's a union type
                            let type_ids =
                                if let Some(variants) = arena.unwrap_union(aliased_type_id) {
                                    // It's a union - use the variant TypeIds
                                    variants.to_vec()
                                } else {
                                    // Not a union - use the single TypeId
                                    vec![aliased_type_id]
                                };
                            return Some(crate::generic::TypeConstraint::UnionId(type_ids));
                        }
                    }
                }

                // Validate all interfaces exist via EntityRegistry using resolver
                for sym in syms {
                    let iface_str = interner.resolve(*sym);
                    let iface_exists = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry())
                        .is_some();

                    if !iface_exists {
                        self.add_error(
                            SemanticError::UnknownInterface {
                                name: iface_str.to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                        return None;
                    }
                }
                Some(crate::generic::TypeConstraint::Interface(syms.clone()))
            }
            TypeConstraint::Union(types) => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.db,
                    interner,
                    module_id,
                    type_param_scope,
                );
                let resolved_ids = types
                    .iter()
                    .map(|ty| resolve_type_to_id(ty, &mut ctx))
                    .collect();
                Some(crate::generic::TypeConstraint::UnionId(resolved_ids))
            }
            TypeConstraint::Structural { fields, methods } => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params(
                    &self.db,
                    interner,
                    module_id,
                    type_param_scope,
                );
                // Convert AST structural to InternedStructural (TypeId-based)
                let resolved_fields: smallvec::SmallVec<[(NameId, ArenaTypeId); 4]> = fields
                    .iter()
                    .map(|f| {
                        let name =
                            ctx.name_table_mut()
                                .intern(ctx.module_id, &[f.name], ctx.interner);
                        let ty = resolve_type_to_id(&f.ty, &mut ctx);
                        (name, ty)
                    })
                    .collect();
                let resolved_methods: smallvec::SmallVec<
                    [crate::type_arena::InternedStructuralMethod; 2],
                > = methods
                    .iter()
                    .map(|m| {
                        let name =
                            ctx.name_table_mut()
                                .intern(ctx.module_id, &[m.name], ctx.interner);
                        let params = m
                            .params
                            .iter()
                            .map(|p| resolve_type_to_id(p, &mut ctx))
                            .collect();
                        let return_type = resolve_type_to_id(&m.return_type, &mut ctx);
                        crate::type_arena::InternedStructuralMethod {
                            name,
                            params,
                            return_type,
                        }
                    })
                    .collect();
                Some(crate::generic::TypeConstraint::Structural(
                    crate::type_arena::InternedStructural {
                        fields: resolved_fields,
                        methods: resolved_methods,
                    },
                ))
            }
        }
    }

    /// Check type param constraints.
    fn check_type_param_constraints_id(
        &mut self,
        type_params: &[TypeParamInfo],
        inferred: &FxHashMap<NameId, ArenaTypeId>,
        span: Span,
        interner: &Interner,
    ) {
        use crate::compatibility::types_compatible_core_id;

        for param in type_params {
            let Some(constraint) = &param.constraint else {
                continue;
            };
            let Some(&found_id) = inferred.get(&param.name_id) else {
                continue;
            };

            // Check if found type is itself a type param with matching or stronger constraint
            let found_param = {
                let arena = self.type_arena();
                if let Some(found_name_id) = arena.unwrap_type_param(found_id) {
                    self.type_param_stack.get_by_name_id(found_name_id)
                } else if let Some(type_param_id) = arena.unwrap_type_param_ref(found_id) {
                    self.type_param_stack.get_by_type_param_id(type_param_id)
                } else {
                    None
                }
            };
            if let Some(found_param) = found_param
                && constraint_satisfied(&found_param.constraint, constraint)
            {
                continue; // Constraint is satisfied
            }

            match constraint {
                crate::generic::TypeConstraint::Interface(interface_names) => {
                    // Check each interface constraint with TypeId
                    for interface_name in interface_names {
                        if !self.satisfies_interface_id(found_id, *interface_name, interner) {
                            let found_display = self.type_display_id(found_id);
                            self.add_error(
                                SemanticError::TypeParamConstraintMismatch {
                                    type_param: self.get_type_param_display_name(param, interner),
                                    expected: interner.resolve(*interface_name).to_string(),
                                    found: found_display,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
                crate::generic::TypeConstraint::UnionId(variant_ids) => {
                    // TypeId-based - no conversion needed
                    let expected_id = self.type_arena_mut().union(variant_ids.clone());
                    let is_compatible = {
                        let arena = self.type_arena();
                        types_compatible_core_id(found_id, expected_id, &arena)
                    };
                    if !is_compatible {
                        let expected_display = self.type_display_id(expected_id);
                        let found_display = self.type_display_id(found_id);
                        self.add_error(
                            SemanticError::TypeParamConstraintMismatch {
                                type_param: self.get_type_param_display_name(param, interner),
                                expected: expected_display,
                                found: found_display,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
                crate::generic::TypeConstraint::Structural(structural) => {
                    // Substitute any type params in the structural constraint before checking.
                    // This handles cases like `func foo<T, __T0: { name: T }>(a: __T0)` where
                    // the structural constraint references another type param T.
                    let substituted_structural =
                        self.substitute_structural_constraint(structural, inferred);

                    // Use TypeId-based structural constraint checking
                    if let Some(mismatch) = self.check_structural_constraint_id(
                        found_id,
                        &substituted_structural,
                        interner,
                    ) {
                        let found_display = self.type_display_id(found_id);
                        let constraint_display = self.structural_display(&substituted_structural);
                        self.add_error(
                            SemanticError::StructuralConstraintMismatch {
                                constraint: constraint_display,
                                found: found_display,
                                mismatch,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
            }
        }
    }

    /// Substitute type parameters in a structural constraint.
    /// This is needed when the structural constraint references other type params,
    /// e.g., in `func foo<T, __T0: { name: T }>(a: __T0)`, the constraint `{ name: T }`
    /// needs T substituted with the inferred type before checking.
    fn substitute_structural_constraint(
        &mut self,
        structural: &crate::type_arena::InternedStructural,
        inferred: &FxHashMap<NameId, ArenaTypeId>,
    ) -> crate::type_arena::InternedStructural {
        use crate::type_arena::{InternedStructural, InternedStructuralMethod};

        // Substitute field types
        let new_fields: smallvec::SmallVec<[(NameId, ArenaTypeId); 4]> = structural
            .fields
            .iter()
            .map(|&(name, ty)| {
                let new_ty = self.type_arena_mut().substitute(ty, inferred);
                (name, new_ty)
            })
            .collect();

        // Substitute method signatures
        let new_methods: smallvec::SmallVec<[InternedStructuralMethod; 2]> = structural
            .methods
            .iter()
            .map(|m| {
                let new_params: crate::type_arena::TypeIdVec = m
                    .params
                    .iter()
                    .map(|&p| self.type_arena_mut().substitute(p, inferred))
                    .collect();
                let new_return_type = self.type_arena_mut().substitute(m.return_type, inferred);
                InternedStructuralMethod {
                    name: m.name,
                    params: new_params,
                    return_type: new_return_type,
                }
            })
            .collect();

        InternedStructural {
            fields: new_fields,
            methods: new_methods,
        }
    }

    /// Analyze external block and register external methods in the implement registry
    fn analyze_external_block(
        &mut self,
        external: &ExternalBlock,
        target_type_id: ArenaTypeId,
        trait_name: Option<Symbol>,
        interner: &Interner,
    ) {
        let impl_type_id = match ImplTypeId::from_type_id(
            target_type_id,
            &self.type_arena(),
            &self.entity_registry(),
        ) {
            Some(id) => id,
            None => return, // Skip non-registerable types
        };

        // Get EntityRegistry TypeDefId for the target type
        // Use impl_type_id.name_id() which we already have, avoiding name_id_for_type
        let entity_type_id = self
            .type_arena()
            .type_def_id(target_type_id)
            .or_else(|| self.entity_registry().type_by_name(impl_type_id.name_id()));

        // Get interface TypeDefId if implementing an interface
        let interface_type_id = trait_name.and_then(|name| {
            let iface_str = interner.resolve(name);
            self.resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry())
        });

        for func in &external.functions {
            // Resolve parameter types directly to TypeId
            // Use target_type_id as Self when resolving external method signatures
            let param_type_ids: Vec<ArenaTypeId> = func
                .params
                .iter()
                .map(|p| self.resolve_type_id_with_self(&p.ty, interner, Some(target_type_id)))
                .collect();

            // Resolve return type directly to TypeId
            let return_type_id = match &func.return_type {
                Some(te) => self.resolve_type_id_with_self(te, interner, Some(target_type_id)),
                None => self.type_arena().void(),
            };

            let func_type = FunctionType::from_ids(&param_type_ids, return_type_id, false);

            // Determine native name: explicit or default to vole_name
            let native_name_str = func
                .native_name
                .clone()
                .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());

            // Register in implement registry
            let method_id = self.method_name_id(func.vole_name, interner);
            // Extract name IDs before struct literal to avoid overlapping borrows
            let (module_path, native_name) = {
                let builtin_module = self.name_table_mut().builtin_module();
                let mut name_table = self.name_table_mut();
                (
                    name_table.intern_raw(builtin_module, &[&external.module_path]),
                    name_table.intern_raw(builtin_module, &[&native_name_str]),
                )
            };
            let external_info = ExternalMethodInfo {
                module_path,
                native_name,
            };
            self.implement_registry_mut().register_method(
                impl_type_id,
                method_id,
                MethodImpl {
                    trait_name,
                    func_type: func_type.clone(),
                    is_builtin: false,
                    external_info: Some(external_info),
                },
            );

            // Register in EntityRegistry for method resolution
            if let Some(entity_type_id) = entity_type_id {
                use crate::entity_defs::MethodBinding;
                // For trait implementations, use the interface type id
                // For type extensions, use the type's own id as both
                let binding_type_id = interface_type_id.unwrap_or(entity_type_id);
                self.entity_registry_mut().add_method_binding(
                    entity_type_id,
                    binding_type_id,
                    MethodBinding {
                        method_name: method_id,
                        func_type,
                        is_builtin: false,
                        external_info: Some(external_info),
                    },
                );
            }
        }
    }

    /// Enter a function/method check context, saving current state.
    /// Automatically sets return/error/generator types from return_type_id.
    /// For static methods, caller should set static_method and push type params after calling.
    fn enter_function_context(&mut self, return_type_id: ArenaTypeId) -> FunctionCheckContext {
        let saved = FunctionCheckContext {
            return_type: self.current_function_return.take(),
            error_type: self.current_function_error_type.take(),
            generator_element_type: self.current_generator_element_type.take(),
            static_method: self.current_static_method.take(),
            type_param_stack_depth: self.type_param_stack.depth(),
        };

        self.current_function_return = Some(return_type_id);

        // Set error type context if this is a fallible function
        let error_type = self
            .type_arena()
            .unwrap_fallible(return_type_id)
            .map(|(_, e)| e);
        if let Some(error) = error_type {
            self.current_function_error_type = Some(error);
        }

        // Set generator context if return type is Iterator<T>
        if let Some(element_type_id) = self.extract_iterator_element_type_id(return_type_id) {
            self.current_generator_element_type = Some(element_type_id);
        }

        saved
    }

    /// Enter a function context for return type inference (no known return type).
    /// The first return statement will set current_function_return; subsequent returns check against it.
    fn enter_function_context_inferring(&mut self) -> FunctionCheckContext {
        // current_function_return stays None to signal inference mode
        FunctionCheckContext {
            return_type: self.current_function_return.take(),
            error_type: self.current_function_error_type.take(),
            generator_element_type: self.current_generator_element_type.take(),
            static_method: self.current_static_method.take(),
            type_param_stack_depth: self.type_param_stack.depth(),
        }
    }

    /// Exit function/method check context, restoring saved state.
    fn exit_function_context(&mut self, saved: FunctionCheckContext) {
        self.current_function_return = saved.return_type;
        self.current_function_error_type = saved.error_type;
        self.current_generator_element_type = saved.generator_element_type;
        self.current_static_method = saved.static_method;
        // Pop any scopes that were pushed during this context
        while self.type_param_stack.depth() > saved.type_param_stack_depth {
            self.type_param_stack.pop();
        }
    }

    /// Infer the return type from collected return_types in ReturnInfo.
    ///
    /// This enables multi-branch return type inference:
    /// - If no return types collected, returns void
    /// - If one return type, returns that type
    /// - If multiple different return types, creates a union type
    ///
    /// Example: `func foo(x: bool) { if x { return 1 } else { return "hi" } }`
    /// will infer return type `i64 | string`.
    fn infer_return_type_from_info(&mut self, info: &ReturnInfo) -> ArenaTypeId {
        if info.return_types.is_empty() {
            ArenaTypeId::VOID
        } else if info.return_types.len() == 1 {
            info.return_types[0].0
        } else {
            // Extract just the types for union creation
            let types: Vec<ArenaTypeId> = info.return_types.iter().map(|(ty, _)| *ty).collect();
            // Create union of all return types (the union method handles deduplication)
            self.type_arena_mut().union(types)
        }
    }

    fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Skip generic functions - they will be type-checked when monomorphized
        // This includes both explicitly generic functions (with type params in the AST)
        // and implicitly generified functions (with structural type parameters)
        // TODO: In M4+, we could type-check with abstract type params
        if !func.type_params.is_empty() {
            return Ok(());
        }

        // Also skip implicitly generified functions (structural types in parameters)
        // These have generic_info but no AST-level type_params
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);
        let has_generic_info = self
            .entity_registry()
            .function_by_name(name_id)
            .map(|func_id| {
                self.entity_registry()
                    .get_function(func_id)
                    .generic_info
                    .is_some()
            })
            .unwrap_or(false);
        if has_generic_info {
            return Ok(());
        }

        let func_type = self
            .functions
            .get(&func.name)
            .cloned()
            .expect("function registered in signature collection pass");

        // Determine if we need to infer the return type
        let needs_inference = func.return_type.is_none();

        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(func_type.return_type_id)
        };

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, &ty_id) in func.params.iter().zip(func_type.params_id.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Type-check parameter default expressions
        self.check_param_defaults(&func.params, &func_type.params_id, interner)?;

        // Check body
        let body_info = self.check_func_body(&func.body, interner)?;

        // If we were inferring the return type, update the function signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the function signature with the inferred return type
            if let Some(existing) = self.functions.get_mut(&func.name) {
                existing.return_type_id = inferred_return_type;
            }

            // Also update in entity_registry
            // Get func_id first, then drop borrow before mutating
            let name_id = self
                .name_table_mut()
                .intern(self.current_module, &[func.name], interner);
            let func_id = self.entity_registry().function_by_name(name_id);
            if let Some(func_id) = func_id {
                self.entity_registry_mut()
                    .update_function_return_type(func_id, inferred_return_type);
            }
        } else {
            // Check for missing return statement when return type is explicit and non-void
            let is_void = func_type.return_type_id.is_void();
            if !is_void && !body_info.definitely_returns {
                let func_name = interner.resolve(func.name).to_string();
                let expected = self.type_display_id(func_type.return_type_id);
                let hint = self.compute_missing_return_hint(
                    &func.body,
                    func_type.return_type_id,
                    interner,
                );
                self.add_error(
                    SemanticError::MissingReturn {
                        name: func_name,
                        expected,
                        hint,
                        span: func.span.into(),
                    },
                    func.span,
                );
            }
        }

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Analyze a generic function body with type substitutions applied.
    /// This discovers nested generic function calls and creates their MonomorphInstances.
    fn analyze_monomorph_body(
        &mut self,
        func: &FuncDecl,
        substitutions: &FxHashMap<NameId, ArenaTypeId>,
        interner: &Interner,
    ) {
        // Get the generic function info to resolve parameter and return types
        let name_id = self
            .name_table_mut()
            .intern(self.current_module, &[func.name], interner);
        let generic_info = {
            let registry = self.entity_registry();
            registry
                .function_by_name(name_id)
                .and_then(|fid| registry.get_function(fid).generic_info.clone())
        };

        let Some(generic_info) = generic_info else {
            return;
        };

        // Compute concrete parameter and return types
        let (concrete_param_ids, concrete_return_id) = {
            let mut arena = self.type_arena_mut();
            let param_ids: Vec<_> = generic_info
                .param_types
                .iter()
                .map(|&t| arena.substitute(t, substitutions))
                .collect();
            let return_id = arena.substitute(generic_info.return_type, substitutions);
            (param_ids, return_id)
        };

        // Set up function context with the concrete return type
        let saved_ctx = self.enter_function_context(concrete_return_id);

        // Create new scope with parameters (using concrete types)
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, &ty_id) in func.params.iter().zip(concrete_param_ids.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Set up type parameter scope with the substitutions
        // This maps type param names to their concrete types
        let mut type_param_scope = TypeParamScope::new();
        for tp in &generic_info.type_params {
            // Create TypeParamInfo with the substituted type
            type_param_scope.add(tp.clone());
        }
        self.type_param_stack.push_scope(type_param_scope);

        // Store substitutions for use during type resolution
        // We need to make type param lookups return the substituted concrete types
        // This is handled via type_arena.substitute during check_call_expr

        // Check the function body - this will discover nested generic calls
        // and create MonomorphInstances for them
        let _ = self.check_func_body(&func.body, interner);

        // Pop type parameter scope
        self.type_param_stack.pop();

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);
    }

    /// Analyze all monomorphized function bodies to discover nested generic calls.
    /// Iterates until no new MonomorphInstances are created (fixpoint).
    fn analyze_monomorph_bodies(&mut self, program: &Program, interner: &Interner) {
        // Build map of generic function names to their ASTs
        // Include both explicit generics (type_params in AST) and implicit generics
        // (structural type params that create generic_info in entity registry)
        let generic_func_asts: FxHashMap<NameId, &FuncDecl> = program
            .declarations
            .iter()
            .filter_map(|decl| {
                if let Decl::Function(func) = decl {
                    let name_id =
                        self.name_table_mut()
                            .intern(self.current_module, &[func.name], interner);

                    // Check for explicit type params OR implicit generic_info
                    let has_explicit_type_params = !func.type_params.is_empty();
                    let has_implicit_generic_info = self
                        .entity_registry()
                        .function_by_name(name_id)
                        .map(|func_id| {
                            self.entity_registry()
                                .get_function(func_id)
                                .generic_info
                                .is_some()
                        })
                        .unwrap_or(false);

                    if has_explicit_type_params || has_implicit_generic_info {
                        return Some((name_id, func));
                    }
                }
                None
            })
            .collect();

        // Track which instances we've already analyzed
        let mut analyzed_keys: HashSet<MonomorphKey> = HashSet::new();

        // Iterate until fixpoint
        loop {
            // Collect current instances that haven't been analyzed yet
            let instances: Vec<_> = self
                .entity_registry()
                .monomorph_cache
                .collect_instances()
                .into_iter()
                .filter(|inst| {
                    let key = MonomorphKey::new(
                        inst.original_name,
                        inst.substitutions.values().copied().collect(),
                    );
                    !analyzed_keys.contains(&key)
                })
                .collect();

            if instances.is_empty() {
                break;
            }

            for instance in instances {
                // Mark as analyzed
                let key = MonomorphKey::new(
                    instance.original_name,
                    instance.substitutions.values().copied().collect(),
                );
                analyzed_keys.insert(key);

                // Find the function AST
                if let Some(func) = generic_func_asts.get(&instance.original_name) {
                    // Analyze the body with substitutions
                    self.analyze_monomorph_body(func, &instance.substitutions, interner);
                }
            }
        }
    }

    /// Check if an expression is a constant expression.
    /// Constant expressions are: literals, unary/binary ops on constants,
    /// array/tuple literals with constant elements, and references to
    /// immutable globals with constant initializers.
    fn is_constant_expr(&self, expr: &Expr) -> bool {
        use ast::ExprKind;
        match &expr.kind {
            // Literals are constant
            ExprKind::IntLiteral(..)
            | ExprKind::FloatLiteral(..)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_)
            | ExprKind::Nil => true,

            // Identifier: constant if it's an immutable global with a constant initializer
            ExprKind::Identifier(sym) => self.constant_globals.contains(sym),

            // Unary operators on constants
            ExprKind::Unary(unary) => self.is_constant_expr(&unary.operand),

            // Binary operators on constants
            ExprKind::Binary(binary) => {
                self.is_constant_expr(&binary.left) && self.is_constant_expr(&binary.right)
            }

            // Array/tuple literals with all constant elements
            ExprKind::ArrayLiteral(elements) => elements.iter().all(|e| self.is_constant_expr(e)),

            // Repeat literals with constant element (count is already a usize)
            ExprKind::RepeatLiteral { element, .. } => self.is_constant_expr(element),

            // Grouping (parenthesized expression)
            ExprKind::Grouping(inner) => self.is_constant_expr(inner),

            // Everything else is not constant
            _ => false,
        }
    }

    /// Type-check parameter default expressions against their declared types.
    /// Called during function body analysis when parameters are in scope.
    fn check_param_defaults(
        &mut self,
        params: &[Param],
        param_types: &crate::type_arena::TypeIdVec,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for (param, &expected_type_id) in params.iter().zip(param_types.iter()) {
            if let Some(ref default_expr) = param.default_value {
                // Type-check the default expression
                let found_type_id = self.check_expr(default_expr, interner)?;

                // Check type compatibility
                if !self.types_compatible_id(expected_type_id, found_type_id, interner) {
                    let expected = self.type_display_id(expected_type_id);
                    let found = self.type_display_id(found_type_id);
                    self.add_error(
                        SemanticError::DefaultExprTypeMismatch {
                            expected,
                            found,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }

                // Check that the default is a constant expression
                if !self.is_constant_expr(default_expr) {
                    let name = interner.resolve(param.name).to_string();
                    self.add_error(
                        SemanticError::DefaultMustBeConstant {
                            name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }
            }
        }
        Ok(())
    }

    /// Type-check field default expressions against their declared types.
    /// Called during class/record analysis.
    fn check_field_defaults(
        &mut self,
        fields: &[FieldDef],
        field_type_ids: &[ArenaTypeId],
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        for (field, &expected_type_id) in fields.iter().zip(field_type_ids.iter()) {
            if let Some(ref default_expr) = field.default_value {
                // Type-check the default expression
                let found_type_id = self.check_expr(default_expr, interner)?;

                // Check type compatibility
                if !self.types_compatible_id(expected_type_id, found_type_id, interner) {
                    let expected = self.type_display_id(expected_type_id);
                    let found = self.type_display_id(found_type_id);
                    let field_name = interner.resolve(field.name).to_string();
                    self.add_error(
                        SemanticError::FieldDefaultTypeMismatch {
                            expected,
                            found,
                            field: field_name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }

                // Check that the default is a constant expression
                if !self.is_constant_expr(default_expr) {
                    let field_name = interner.resolve(field.name).to_string();
                    self.add_error(
                        SemanticError::DefaultMustBeConstant {
                            name: field_name,
                            span: default_expr.span.into(),
                        },
                        default_expr.span,
                    );
                }
            }
        }
        Ok(())
    }

    /// Extract the element type from an Iterator<T> type.
    fn extract_iterator_element_type_id(&self, ty_id: ArenaTypeId) -> Option<ArenaTypeId> {
        let interface_info = {
            let arena = self.type_arena();
            arena
                .unwrap_interface(ty_id)
                .map(|(id, args)| (id, args.first().copied()))
        };
        let (type_def_id, first_arg) = interface_info?;
        if !self
            .name_table()
            .well_known
            .is_iterator_type_def(type_def_id)
        {
            return None;
        }
        first_arg
    }

    fn check_method(
        &mut self,
        method: &FuncDecl,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Look up method type via Resolver
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry())
            .expect("type should be registered in EntityRegistry");
        let lookup = self
            .lookup_method(type_def_id, method.name, interner)
            .expect("method should be registered in EntityRegistry");

        // Get signature components from arena
        let (params_id, return_type_id) = {
            let arena = self.type_arena();
            let (params, ret, _) = arena
                .unwrap_function(lookup.signature_id)
                .expect("method signature must be a function type");
            (params.clone(), ret)
        };

        // Determine if we need to infer the return type
        let needs_inference = method.return_type.is_none();

        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Create scope with 'self' and parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add 'self' to scope
        // Note: "self" should already be interned by the parser when it parses method bodies
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        // Build self type directly as TypeId.
        // For generic types, include type parameter TypeIds as type args so that
        // method calls on `self` (e.g. self.getItem()) properly record class method
        // monomorphizations with the type parameters.
        let kind = {
            let registry = self.entity_registry();
            registry.get_type(type_def_id).kind
        };
        let type_args = {
            let generic_info = {
                let registry = self.entity_registry();
                registry.get_generic_info(type_def_id).cloned()
            };
            if let Some(gi) = generic_info {
                let mut args = crate::type_arena::TypeIdVec::new();
                for tp in &gi.type_params {
                    let tp_type_id = self.type_arena_mut().type_param(tp.name_id);
                    args.push(tp_type_id);
                }
                args
            } else {
                crate::type_arena::TypeIdVec::new()
            }
        };
        let self_type_id = match kind {
            TypeDefKind::Class => self.type_arena_mut().class(type_def_id, type_args),
            TypeDefKind::Record => self.type_arena_mut().record(type_def_id, type_args),
            _ => self.type_arena().invalid(),
        };
        self.scope.define(
            self_sym,
            Variable {
                ty: self_type_id,
                mutable: false,
            },
        );

        // Add parameters
        for (param, &ty_id) in method.params.iter().zip(params_id.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Type-check parameter default expressions
        self.check_param_defaults(&method.params, &params_id, interner)?;

        // Check body
        let body_info = self.check_func_body(&method.body, interner)?;

        // If we were inferring the return type, update the method signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the method's return type in EntityRegistry
            {
                let mut db = self.db.borrow_mut();
                let CompilationDb {
                    ref mut entities,
                    ref mut types,
                    ..
                } = *db;
                Rc::make_mut(entities).update_method_return_type(
                    lookup.method_id,
                    inferred_return_type,
                    Rc::make_mut(types),
                );
            }
        } else {
            // Check for missing return statement when return type is explicit and non-void
            let is_void = return_type_id.is_void();
            if !is_void && !body_info.definitely_returns {
                let method_name = interner.resolve(method.name).to_string();
                let expected = self.type_display_id(return_type_id);
                let hint = self.compute_missing_return_hint(&method.body, return_type_id, interner);
                self.add_error(
                    SemanticError::MissingReturn {
                        name: method_name,
                        expected,
                        hint,
                        span: method.span.into(),
                    },
                    method.span,
                );
            }
        }

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Check a function body - either a block or a single expression
    fn check_func_body(
        &mut self,
        body: &FuncBody,
        interner: &Interner,
    ) -> Result<ReturnInfo, Vec<TypeError>> {
        match body {
            FuncBody::Block(block) => self.check_block(block, interner),
            FuncBody::Expr(expr) => {
                // Expression body is implicitly a return
                let expr_type = self.check_expr(expr, interner)?;

                // Handle return type inference or checking
                if let Some(expected_return) = self.current_function_return {
                    // Explicit return type - check for match
                    if !self.types_compatible_id(expr_type, expected_return, interner) {
                        let expected_str = self.type_display_id(expected_return);
                        let found = self.type_display_id(expr_type);
                        self.add_error(
                            SemanticError::ReturnTypeMismatch {
                                expected: expected_str,
                                found,
                                span: expr.span.into(),
                            },
                            expr.span,
                        );
                    }
                } else {
                    // Inference mode - set the return type
                    self.current_function_return = Some(expr_type);
                }
                // Expression body definitely returns with the expression type
                Ok(ReturnInfo {
                    definitely_returns: true,
                    return_types: vec![(expr_type, expr.span)],
                })
            }
        }
    }

    /// Compute the hint for a MissingReturn error.
    /// If the last statement in the block is an expression whose type matches the expected return type,
    /// suggest adding `return` before it. Otherwise, provide a generic hint.
    fn compute_missing_return_hint(
        &mut self,
        body: &FuncBody,
        expected_return_type: ArenaTypeId,
        interner: &Interner,
    ) -> String {
        if let FuncBody::Block(block) = body
            && let Some(Stmt::Expr(expr_stmt)) = block.stmts.last()
        {
            // Check if we have a recorded type for this expression
            if let Some(&expr_type) = self.expr_types.get(&expr_stmt.expr.id) {
                // Check if it matches the expected return type
                if self.types_compatible_id(expr_type, expected_return_type, interner) {
                    return "did you mean to add `return` before the last expression?".to_string();
                }
            }
        }
        // Default hint
        "add a return statement, or change return type to void".to_string()
    }

    /// Check a static method body (no `self` access allowed)
    fn check_static_method(
        &mut self,
        method: &InterfaceMethod,
        type_name: Symbol,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Resolve type name and delegate to check_static_method_with_type_def
        let type_def_id = self
            .resolver(interner)
            .resolve_type(type_name, &self.entity_registry())
            .expect("type should be registered in EntityRegistry");
        self.check_static_method_with_type_def(method, type_def_id, interner)
    }

    /// Check a static method body with the type already resolved to a TypeDefId.
    /// This is used for primitive types where we can't resolve via Symbol.
    fn check_static_method_with_type_def(
        &mut self,
        method: &InterfaceMethod,
        type_def_id: TypeDefId,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Only check methods with bodies
        let Some(ref body) = method.body else {
            return Ok(());
        };

        let method_name_id = self.method_name_id(method.name, interner);
        let method_id = self
            .entity_registry_mut()
            .find_static_method_on_type(type_def_id, method_name_id)
            .expect("static method should be registered in EntityRegistry");
        let (method_type_params, signature_id) = {
            let registry = self.entity_registry();
            let method_def = registry.get_method(method_id);
            (
                method_def.method_type_params.clone(),
                method_def.signature_id,
            )
        };

        // Get signature components from arena
        let (params_id, return_type_id) = {
            let arena = self.type_arena();
            let (params, ret, _) = arena
                .unwrap_function(signature_id)
                .expect("method signature must be a function type");
            (params.clone(), ret)
        };

        // Determine if we need to infer the return type
        let needs_inference = method.return_type.is_none();
        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Mark that we're in a static method (for self-usage detection)
        self.current_static_method = Some(interner.resolve(method.name).to_string());

        // Push method-level type params onto the stack (merged with any class/record type params)
        let has_method_type_params = !method_type_params.is_empty();
        if has_method_type_params {
            self.type_param_stack.push_merged(method_type_params);
        }

        // Create scope WITHOUT 'self'
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add parameters (no 'self' for static methods)
        for (param, &ty_id) in method.params.iter().zip(params_id.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Check body
        let body_info = self.check_func_body(body, interner)?;

        // If we were inferring the return type, update the method signature
        if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            let inferred_return_type = self.infer_return_type_from_info(&body_info);

            // Update the method signature with the inferred return type
            // Destructure db to get both entities and types to avoid RefCell conflict
            {
                let mut db = self.db.borrow_mut();
                let CompilationDb {
                    ref mut entities,
                    ref mut types,
                    ..
                } = *db;
                Rc::make_mut(entities).update_method_return_type(
                    method_id,
                    inferred_return_type,
                    Rc::make_mut(types),
                );
            }
        }

        // Restore scope and context
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    fn check_tests(
        &mut self,
        tests_decl: &TestsDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Create a scope for the tests block (scoped declarations live here)
        let module_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(module_scope);

        // Process scoped declarations
        for decl in &tests_decl.decls {
            self.check_scoped_decl(decl, interner)?;
        }

        // Check each test case (each gets its own child scope)
        for test_case in &tests_decl.tests {
            // Each test gets its own scope (child of tests block scope)
            let tests_block_scope = std::mem::take(&mut self.scope);
            self.scope = Scope::with_parent(tests_block_scope);

            // Tests implicitly return void
            let void_id = self.type_arena().void();
            let saved_ctx = self.enter_function_context(void_id);

            // Type check the test body
            let _body_info = self.check_func_body(&test_case.body, interner)?;

            // Restore to tests block scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
            self.exit_function_context(saved_ctx);
        }

        // Restore to module scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }

        Ok(())
    }

    /// Check a scoped declaration in a tests block
    fn check_scoped_decl(
        &mut self,
        decl: &Decl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        match decl {
            Decl::Function(func) => {
                self.check_scoped_function(func, interner)?;
            }
            Decl::Let(let_stmt) => {
                // Process let like a local let (check init, add to scope)
                // We create a temporary Stmt::Let wrapper to reuse the existing logic
                let _ = self.check_stmt(&Stmt::Let(let_stmt.clone()), interner)?;
            }
            _ => {
                // record, class, interface, implement, error, external
                // TODO(vole-2vgz): Support these declaration types in tests blocks
                // For now, they will be silently ignored (types won't be visible)
            }
        }
        Ok(())
    }

    /// Check a function declaration scoped to a tests block
    fn check_scoped_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Skip generic functions - not supported in tests blocks for now
        if !func.type_params.is_empty() {
            return Ok(());
        }

        // Resolve parameter types
        let param_types: Vec<ArenaTypeId> = func
            .params
            .iter()
            .map(|p| self.resolve_type_id(&p.ty, interner))
            .collect();

        // Resolve return type (or infer later)
        let declared_return_type = func
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_id(t, interner));

        // Create function type (for reference, though scoped funcs aren't in self.functions)
        let return_type_id = declared_return_type.unwrap_or_else(|| self.type_arena().void());

        // Enter function context
        let needs_inference = func.return_type.is_none();
        let saved_ctx = if needs_inference {
            self.enter_function_context_inferring()
        } else {
            self.enter_function_context(return_type_id)
        };

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, &ty_id) in func.params.iter().zip(param_types.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Type-check parameter default expressions
        let param_type_vec: crate::type_arena::TypeIdVec = param_types.iter().copied().collect();
        self.check_param_defaults(&func.params, &param_type_vec, interner)?;

        // Check body
        let body_info = self.check_func_body(&func.body, interner)?;

        // Get inferred return type if needed
        let final_return_type = if needs_inference {
            // Use ReturnInfo to infer type from all return statements (creates union if needed)
            self.infer_return_type_from_info(&body_info)
        } else {
            return_type_id
        };

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        // Build closure function type and register in scope as a variable.
        // Scoped functions are always compiled as closures, so we use is_closure=true.
        let param_ids: crate::type_arena::TypeIdVec = param_types.iter().copied().collect();
        let func_type_id = self
            .type_arena_mut()
            .function(param_ids, final_return_type, true);

        // Store the closure type for codegen to look up
        self.scoped_function_types.insert(func.span, func_type_id);

        self.scope.define(
            func.name,
            Variable {
                ty: func_type_id,
                mutable: false,
            },
        );

        Ok(())
    }

    fn is_assert_call(&self, callee: &Expr, interner: &Interner) -> bool {
        if let ExprKind::Identifier(sym) = &callee.kind {
            interner.resolve(*sym) == "assert"
        } else {
            false
        }
    }

    /// Analyze an imported module and return its type
    #[allow(clippy::result_unit_err)] // Error is added to self.errors vector
    #[tracing::instrument(skip(self, span, _interner), fields(path = %import_path))]
    pub fn analyze_module(
        &mut self,
        import_path: &str,
        span: Span,
        _interner: &Interner,
    ) -> Result<ArenaTypeId, ()> {
        // Check cache first - return cached TypeId directly
        // Note: We check again after loading to handle path canonicalization
        if let Some(&type_id) = self.module_type_ids.get(import_path) {
            return Ok(type_id);
        }

        // Load the module - use load_relative for relative imports
        let is_relative = import_path.starts_with("./") || import_path.starts_with("../");
        let module_info = if is_relative {
            // Relative import requires current file context
            match &self.current_file_path {
                Some(current_path) => {
                    match self.module_loader.load_relative(import_path, current_path) {
                        Ok(info) => info,
                        Err(e) => {
                            self.add_error(
                                SemanticError::ModuleNotFound {
                                    path: import_path.to_string(),
                                    message: e.to_string(),
                                    span: span.into(),
                                },
                                span,
                            );
                            return Err(());
                        }
                    }
                }
                None => {
                    self.add_error(
                        SemanticError::ModuleNotFound {
                            path: import_path.to_string(),
                            message: "relative imports require a source file context".to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                    return Err(());
                }
            }
        } else {
            // Standard library or other non-relative import
            match self.module_loader.load(import_path) {
                Ok(info) => info,
                Err(e) => {
                    self.add_error(
                        SemanticError::ModuleNotFound {
                            path: import_path.to_string(),
                            message: e.to_string(),
                            span: span.into(),
                        },
                        span,
                    );
                    return Err(());
                }
            }
        };

        // Use canonical path as the cache key to handle different import paths
        // pointing to the same file (e.g., "std:prelude/traits" vs "./traits")
        // Canonicalize to ensure consistent path representation
        let canonical_path = module_info
            .path
            .canonicalize()
            .unwrap_or_else(|_| module_info.path.clone())
            .to_string_lossy()
            .to_string();

        // Check cache again with canonical path
        if let Some(&type_id) = self.module_type_ids.get(&canonical_path) {
            // Also cache with original import_path for faster subsequent lookups
            self.module_type_ids
                .insert(import_path.to_string(), type_id);
            return Ok(type_id);
        }

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                self.add_error(
                    SemanticError::ModuleParseError {
                        path: import_path.to_string(),
                        message: format!("{:?}", e.error),
                        span: span.into(),
                    },
                    span,
                );
                return Err(());
            }
        };

        // Collect exports, constants, and track external functions
        let mut exports = FxHashMap::default();
        let mut constants = FxHashMap::default();
        let mut external_funcs = FxHashSet::default();
        // Interfaces are collected separately for post-analysis lookup
        let mut interface_names: Vec<(NameId, Symbol)> = Vec::new();
        let module_interner = parser.into_interner();

        // Use import_path for module_id (not canonical path) to match codegen expectations
        let module_id = self.name_table_mut().module_id(import_path);

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    // Build function type from signature - resolve directly to TypeId
                    let func_type_id = {
                        let mut ctx = TypeResolutionContext {
                            db: &self.db,
                            interner: &module_interner,
                            module_id,
                            type_params: None,
                            self_type: None,
                        };
                        let param_ids: crate::type_arena::TypeIdVec = f
                            .params
                            .iter()
                            .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                            .collect();
                        let return_id = f
                            .return_type
                            .as_ref()
                            .map(|rt| resolve_type_to_id(rt, &mut ctx))
                            .unwrap_or_else(|| self.type_arena().void());
                        self.type_arena_mut().function(param_ids, return_id, false)
                    };

                    // Store export by name string
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[f.name], &module_interner);
                    exports.insert(name_id, func_type_id);
                }
                Decl::Let(l) if !l.mutable => {
                    // Only export immutable let bindings (skip type aliases for now)
                    let init_expr = match &l.init {
                        LetInit::Expr(e) => e,
                        LetInit::TypeAlias(_) => continue, // Type aliases handled separately
                    };
                    // Infer type from literal for constants and store the value
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[l.name], &module_interner);
                    let arena = self.type_arena();
                    let (ty_id, const_val) = match &init_expr.kind {
                        ExprKind::FloatLiteral(v, _) => (arena.f64(), Some(ConstantValue::F64(*v))),
                        ExprKind::IntLiteral(v, _) => (arena.i64(), Some(ConstantValue::I64(*v))),
                        ExprKind::BoolLiteral(v) => (arena.bool(), Some(ConstantValue::Bool(*v))),
                        ExprKind::StringLiteral(v) => {
                            (arena.string(), Some(ConstantValue::String(v.clone())))
                        }
                        _ => (arena.invalid(), None), // Complex expressions need full analysis
                    };
                    drop(arena);
                    exports.insert(name_id, ty_id);
                    if let Some(cv) = const_val {
                        constants.insert(name_id, cv);
                    }
                }
                Decl::External(ext) => {
                    // External block functions become exports and are marked as external
                    for func in &ext.functions {
                        // Resolve types directly to TypeId
                        let func_type_id = {
                            let mut ctx = TypeResolutionContext {
                                db: &self.db,
                                interner: &module_interner,
                                module_id,
                                type_params: None,
                                self_type: None,
                            };
                            let param_ids: crate::type_arena::TypeIdVec = func
                                .params
                                .iter()
                                .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                                .collect();
                            let return_id = func
                                .return_type
                                .as_ref()
                                .map(|rt| resolve_type_to_id(rt, &mut ctx))
                                .unwrap_or_else(|| self.type_arena().void());
                            self.type_arena_mut().function(param_ids, return_id, false)
                        };

                        let name_id = self.name_table_mut().intern(
                            module_id,
                            &[func.vole_name],
                            &module_interner,
                        );
                        exports.insert(name_id, func_type_id);
                        // Mark as external function (FFI)
                        external_funcs.insert(name_id);
                    }
                }
                Decl::Interface(iface) => {
                    // Export interfaces to allow qualified implement syntax
                    // We'll populate the actual TypeId after sub-analysis registers them
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[iface.name], &module_interner);
                    // Store interface name for post-analysis lookup
                    interface_names.push((name_id, iface.name));
                }
                _ => {} // Skip other declarations for now
            }
        }

        // Store the program and interner for compiling pure Vole functions
        self.module_programs.insert(
            import_path.to_string(),
            (program.clone(), module_interner.clone()),
        );

        // Run semantic analysis on the module to populate expr_types for function bodies.
        // This is needed for codegen to resolve return types of calls to external functions
        // inside the module (e.g., min(max(x, lo), hi) in math.clamp).
        let mut sub_analyzer = self.create_module_sub_analyzer(module_id);
        let analyze_result = sub_analyzer.analyze(&program, &module_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "module analysis errors");
        }
        // Store module-specific expr_types (NodeIds are per-program)
        self.module_expr_types
            .insert(import_path.to_string(), sub_analyzer.expr_types);
        // Store module-specific method_resolutions (NodeIds are per-program)
        self.module_method_resolutions.insert(
            import_path.to_string(),
            sub_analyzer.method_resolutions.into_inner(),
        );

        // Now populate interface exports after sub-analysis has registered them
        for (name_id, iface_sym) in interface_names {
            // Look up interface type from entity registry
            // Use block to ensure resolver guard is dropped before type_arena_mut
            let type_def_id = {
                let iface_str = module_interner.resolve(iface_sym);
                self.resolver(&module_interner)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                // Create interface type and add to exports
                let iface_type_id = self
                    .type_arena_mut()
                    .interface(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, iface_type_id);
            }
        }

        // Create TypeId from exports and register module metadata
        let exports_vec: smallvec::SmallVec<[(NameId, ArenaTypeId); 8]> =
            exports.into_iter().collect();
        let mut arena = self.type_arena_mut();
        // Register module metadata (constants, external_funcs) for method resolution
        arena.register_module_metadata(
            module_id,
            crate::type_arena::ModuleMetadata {
                constants,
                external_funcs,
            },
        );
        let type_id = arena.module(module_id, exports_vec);
        drop(arena);

        // Cache the TypeId with canonical path for consistent lookups
        self.module_type_ids.insert(canonical_path, type_id);
        // Also cache with original import_path for faster subsequent lookups
        self.module_type_ids
            .insert(import_path.to_string(), type_id);

        Ok(type_id)
    }

    /// Create a sub-analyzer for analyzing a module's function bodies.
    /// This shares the CompilationDb so TypeIds remain valid across analyzers.
    fn create_module_sub_analyzer(&self, module_id: ModuleId) -> Analyzer {
        Analyzer {
            scope: Scope::new(),
            functions: FxHashMap::default(),
            functions_by_name: FxHashMap::default(),
            globals: FxHashMap::default(),
            constant_globals: HashSet::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: FxHashMap::default(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: FxHashMap::default(),
            is_check_results: FxHashMap::default(),
            method_resolutions: MethodResolutions::new(),
            // Use child loader to inherit sandbox settings (stdlib_root, project_root)
            module_loader: self.module_loader.new_child(),
            module_type_ids: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            generic_calls: FxHashMap::default(),
            class_method_calls: FxHashMap::default(),
            static_method_calls: FxHashMap::default(),
            substituted_return_types: FxHashMap::default(),
            lambda_defaults: FxHashMap::default(),
            lambda_variables: FxHashMap::default(),
            scoped_function_types: FxHashMap::default(),
            declared_var_types: FxHashMap::default(),
            current_module: module_id,
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,
            db: Rc::clone(&self.db), // Share the compilation db
            current_file_path: self.current_file_path.clone(), // Inherit file context
        }
    }
}

// Note: Default is not implemented because Analyzer requires file and source parameters

#[cfg(test)]
mod tests;

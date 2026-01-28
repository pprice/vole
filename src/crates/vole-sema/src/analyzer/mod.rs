// src/sema/analyzer/mod.rs

mod builtins;
mod declarations;
mod errors;
mod expr;
mod functions;
mod inference;
mod lambda;
mod methods;
mod module;
mod patterns;
mod prelude;
mod stmt;
mod type_constraints;
mod type_helpers;

use type_constraints::validate_defaults;

use crate::ExpressionData;
pub use crate::ResolverEntityExt;
use crate::analysis_cache::{IsCheckResult, ModuleCache};
use crate::compilation_db::CompilationDb;
use crate::entity_defs::{GenericFuncInfo, TypeDefKind};
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

/// Trait for type declarations (Class or Record) that share common checking logic.
/// This allows unified handling of field defaults, methods, statics, and interface validation.
trait TypeBodyDecl {
    fn name(&self) -> Symbol;
    fn type_params(&self) -> &[TypeParam];
    fn fields(&self) -> &[FieldDef];
    fn methods(&self) -> &[FuncDecl];
    fn statics(&self) -> Option<&StaticsBlock>;
    fn span(&self) -> Span;
}

impl TypeBodyDecl for ClassDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn type_params(&self) -> &[TypeParam] {
        &self.type_params
    }
    fn fields(&self) -> &[FieldDef] {
        &self.fields
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn span(&self) -> Span {
        self.span
    }
}

impl TypeBodyDecl for RecordDecl {
    fn name(&self) -> Symbol {
        self.name
    }
    fn type_params(&self) -> &[TypeParam] {
        &self.type_params
    }
    fn fields(&self) -> &[FieldDef] {
        &self.fields
    }
    fn methods(&self) -> &[FuncDecl] {
        &self.methods
    }
    fn statics(&self) -> Option<&StaticsBlock> {
        self.statics.as_ref()
    }
    fn span(&self) -> Span {
        self.span
    }
}

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

    /// Resolve a string to a TypeDefId through the resolution chain.
    pub fn resolve_type_str(&self, name: &str, registry: &EntityRegistry) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver().resolve_type_str(name, registry)
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
    /// The module ID for the main program (may differ from main_module when using shared cache)
    pub module_id: ModuleId,
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

/// Builder for creating Analyzer instances with various configurations.
/// Reduces code duplication across constructors by centralizing initialization logic.
pub struct AnalyzerBuilder {
    file: String,
    cache: Option<Rc<RefCell<ModuleCache>>>,
    project_root: Option<PathBuf>,
    auto_detect_root: bool,
}

impl AnalyzerBuilder {
    /// Create a new builder for the given file path.
    pub fn new(file: &str) -> Self {
        Self {
            file: file.to_string(),
            cache: None,
            project_root: None,
            auto_detect_root: true,
        }
    }

    /// Use a shared module cache. The analyzer will use the CompilationDb from the cache.
    pub fn with_cache(mut self, cache: Rc<RefCell<ModuleCache>>) -> Self {
        self.cache = Some(cache);
        self
    }

    /// Set an explicit project root. If None is passed, auto-detection is still used.
    pub fn with_project_root(mut self, root: Option<&std::path::Path>) -> Self {
        self.project_root = root.map(|p| p.to_path_buf());
        if root.is_some() {
            self.auto_detect_root = false;
        }
        self
    }

    /// Build the Analyzer with the configured options.
    pub fn build(self) -> Analyzer {
        // Step 1: Resolve the db (new or from cache)
        let (db, has_cache) = if let Some(ref cache) = self.cache {
            (cache.borrow().db(), true)
        } else {
            (Rc::new(RefCell::new(CompilationDb::new())), false)
        };

        // Step 2: Resolve current file path
        let file_path = std::path::Path::new(&self.file);
        let current_file_path = file_path.canonicalize().ok();

        // Step 3: Determine module ID
        // When using shared cache, each file gets its own module ID based on its path
        // to prevent type conflicts when different files define types with the same name.
        let current_module = if has_cache {
            let module_path = current_file_path
                .as_ref()
                .map(|p| p.to_string_lossy().to_string())
                .unwrap_or_else(|| self.file.clone());
            db.borrow_mut().names.module_id(&module_path)
        } else {
            db.borrow().main_module()
        };

        // Step 4: Determine effective project root
        let effective_root = if let Some(root) = self.project_root {
            Some(root)
        } else if self.auto_detect_root {
            current_file_path
                .as_ref()
                .map(|p| ModuleLoader::detect_project_root(p))
        } else {
            None
        };

        // Step 5: Create module loader with project root
        let mut module_loader = ModuleLoader::new();
        if let Some(root) = effective_root {
            module_loader.set_project_root(root);
        }

        // Step 6: Create shared context and the analyzer
        let ctx = Rc::new(AnalyzerContext::new(db, self.cache));
        let mut analyzer = Analyzer {
            ctx,
            current_module,
            current_file_path,
            module_loader,
            ..Default::default()
        };

        // Step 7: Register built-in interfaces and implementations
        analyzer.register_builtins();

        analyzer
    }
}

/// Shared state across all Analyzer instances (parent + sub-analyzers).
/// Single `Rc` clone instead of 3-4 individual `Rc` clones per sub-analyzer.
pub struct AnalyzerContext {
    /// Unified compilation database containing all registries.
    /// Shared via `Rc<RefCell>` so sub-analyzers use the same db, making TypeIds
    /// valid across all analyzers and eliminating clone/merge operations.
    pub db: Rc<RefCell<CompilationDb>>,
    /// Cached module TypeIds by import path (avoids re-parsing).
    pub module_type_ids: RefCell<FxHashMap<String, ArenaTypeId>>,
    /// Parsed module programs and their interners (for compiling pure Vole functions).
    pub module_programs: RefCell<FxHashMap<String, (Program, Interner)>>,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    pub module_cache: Option<Rc<RefCell<ModuleCache>>>,
}

impl AnalyzerContext {
    /// Create a new context with the given db and optional cache.
    fn new(db: Rc<RefCell<CompilationDb>>, cache: Option<Rc<RefCell<ModuleCache>>>) -> Self {
        Self {
            db,
            module_type_ids: RefCell::new(FxHashMap::default()),
            module_programs: RefCell::new(FxHashMap::default()),
            module_cache: cache,
        }
    }

    /// Create an empty context (for Default impl).
    fn empty() -> Self {
        Self::new(Rc::new(RefCell::new(CompilationDb::new())), None)
    }
}

pub struct Analyzer {
    // Shared state (single Rc clone for sub-analyzers)
    pub ctx: Rc<AnalyzerContext>,

    // Per-analysis state
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
    /// Current file path being analyzed (for relative imports).
    /// This is set from the file path passed to Analyzer::new() and updated
    /// when analyzing imported modules.
    current_file_path: Option<PathBuf>,
    /// Whether we are currently checking a when/match arm body.
    /// When true, block expressions are allowed to have trailing expressions.
    in_arm_body: bool,
}

/// Result of looking up a method on a type via EntityRegistry
pub struct MethodLookup {
    pub method_id: MethodId,
    pub signature_id: ArenaTypeId,
}

impl Analyzer {
    /// Create a new Analyzer for the given file.
    /// Auto-detects project root from the file path.
    pub fn new(file: &str, _source: &str) -> Self {
        AnalyzerBuilder::new(file).build()
    }

    /// Create an analyzer with a shared module cache.
    /// The cache is shared across multiple Analyzer instances to avoid
    /// re-analyzing the same modules (prelude, stdlib, user imports).
    /// The analyzer uses the CompilationDb from the cache to ensure TypeIds remain valid.
    pub fn with_cache(file: &str, _source: &str, cache: Rc<RefCell<ModuleCache>>) -> Self {
        AnalyzerBuilder::new(file).with_cache(cache).build()
    }

    /// Create an analyzer with an explicit project root override.
    /// If `project_root` is `None`, auto-detects from file path.
    pub fn with_project_root(
        file: &str,
        _source: &str,
        project_root: Option<&std::path::Path>,
    ) -> Self {
        AnalyzerBuilder::new(file)
            .with_project_root(project_root)
            .build()
    }

    /// Create an analyzer with a shared module cache and an explicit project root override.
    /// If `project_root` is `None`, auto-detects from file path.
    pub fn with_cache_and_project_root(
        file: &str,
        _source: &str,
        cache: Rc<RefCell<ModuleCache>>,
        project_root: Option<&std::path::Path>,
    ) -> Self {
        AnalyzerBuilder::new(file)
            .with_cache(cache)
            .with_project_root(project_root)
            .build()
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
        ResolverGuard::new(&self.ctx.db, interner, self.current_module)
    }

    /// Create a resolver for a specific module context.
    /// Use this when resolving types in an imported module's context.
    pub fn resolver_for_module<'a>(
        &'a self,
        interner: &'a Interner,
        module_id: ModuleId,
    ) -> ResolverGuard<'a> {
        ResolverGuard::new(&self.ctx.db, interner, module_id)
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
            module_programs: self.ctx.module_programs.borrow().clone(),
            db: Rc::clone(&self.ctx.db),
            module_id: self.current_module,
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
        std::cell::Ref::map(self.ctx.db.borrow(), |db| &*db.types)
    }

    /// Get the type arena (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn type_arena_mut(&self) -> std::cell::RefMut<'_, TypeArena> {
        std::cell::RefMut::map(self.ctx.db.borrow_mut(), |db| db.types_mut())
    }

    /// Get the entity registry (read access)
    #[inline]
    fn entity_registry(&self) -> std::cell::Ref<'_, EntityRegistry> {
        std::cell::Ref::map(self.ctx.db.borrow(), |db| &*db.entities)
    }

    /// Get the entity registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn entity_registry_mut(&self) -> std::cell::RefMut<'_, EntityRegistry> {
        std::cell::RefMut::map(self.ctx.db.borrow_mut(), |db| db.entities_mut())
    }

    /// Get the name table (read access)
    #[inline]
    fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        std::cell::Ref::map(self.ctx.db.borrow(), |db| &db.names)
    }

    /// Get the name table (write access)
    #[inline]
    fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        std::cell::RefMut::map(self.ctx.db.borrow_mut(), |db| &mut db.names)
    }

    /// Get the implement registry (read access)
    #[inline]
    fn implement_registry(&self) -> std::cell::Ref<'_, ImplementRegistry> {
        std::cell::Ref::map(self.ctx.db.borrow(), |db| &*db.implements)
    }

    /// Get the implement registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn implement_registry_mut(&self) -> std::cell::RefMut<'_, ImplementRegistry> {
        std::cell::RefMut::map(self.ctx.db.borrow_mut(), |db| db.implements_mut())
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
        let programs = self.ctx.module_programs.borrow();
        let (_, module_interner) = programs.get(&module_path)?;
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
        let type_params_len = self.entity_registry().type_params(type_def_id).len();

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
        let signature_id = self.entity_registry().method_signature(method_id);
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
            let mut db = self.ctx.db.borrow_mut();
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
        // Handle QualifiedPath specially - we need scope access for module bindings.
        // This is not in TypeResolutionContext because it requires scope access.
        if let TypeExpr::QualifiedPath { segments, args } = ty {
            return self.resolve_qualified_type_id(segments, args, interner, self_type_id);
        }

        // Handle container types that might have QualifiedPath elements.
        // We need to handle these here so the recursive calls go through this method
        // rather than resolve_type_to_id (which can't resolve QualifiedPath).
        match ty {
            TypeExpr::Array(elem) => {
                let elem_id = self.resolve_type_id_with_self(elem, interner, self_type_id);
                return self.type_arena_mut().array(elem_id);
            }
            TypeExpr::Optional(inner) => {
                let inner_id = self.resolve_type_id_with_self(inner, interner, self_type_id);
                return self.type_arena_mut().optional(inner_id);
            }
            TypeExpr::FixedArray { element, size } => {
                let elem_id = self.resolve_type_id_with_self(element, interner, self_type_id);
                return self.type_arena_mut().fixed_array(elem_id, *size);
            }
            TypeExpr::Tuple(elements) => {
                let elem_ids: crate::type_arena::TypeIdVec = elements
                    .iter()
                    .map(|e| self.resolve_type_id_with_self(e, interner, self_type_id))
                    .collect();
                return self.type_arena_mut().tuple(elem_ids);
            }
            TypeExpr::Union(variants) => {
                let variant_ids: crate::type_arena::TypeIdVec = variants
                    .iter()
                    .map(|t| self.resolve_type_id_with_self(t, interner, self_type_id))
                    .collect();
                return self.type_arena_mut().union(variant_ids);
            }
            TypeExpr::Function {
                params,
                return_type,
            } => {
                let param_ids: crate::type_arena::TypeIdVec = params
                    .iter()
                    .map(|p| self.resolve_type_id_with_self(p, interner, self_type_id))
                    .collect();
                let ret_id = self.resolve_type_id_with_self(return_type, interner, self_type_id);
                return self.type_arena_mut().function(param_ids, ret_id, false);
            }
            TypeExpr::Fallible {
                success_type,
                error_type,
            } => {
                let success_id =
                    self.resolve_type_id_with_self(success_type, interner, self_type_id);
                let error_id = self.resolve_type_id_with_self(error_type, interner, self_type_id);
                return self.type_arena_mut().fallible(success_id, error_id);
            }
            // All other types can fall through to resolve_type_to_id
            _ => {}
        }

        let module_id = self.current_module;
        let mut ctx = TypeResolutionContext {
            db: &self.ctx.db,
            interner,
            module_id,
            type_params: self.type_param_stack.current(),
            self_type: self_type_id,
        };
        resolve_type_to_id(ty, &mut ctx)
    }

    /// Resolve a module-qualified type path like `time.Duration` or `http.Response<T>`.
    ///
    /// This handles the QualifiedPath variant of TypeExpr which allows types to be
    /// referenced via their module binding: `let time = import "std:time"; let d: time.Duration`
    fn resolve_qualified_type_id(
        &mut self,
        segments: &[Symbol],
        args: &[TypeExpr],
        interner: &Interner,
        self_type_id: Option<ArenaTypeId>,
    ) -> ArenaTypeId {
        // Must have at least two segments: module.Type
        if segments.len() < 2 {
            tracing::debug!("qualified_type: too few segments");
            return self.ty_invalid_traced_id("qualified_path_too_short");
        }

        // Look up first segment in scope to find the module binding
        let module_sym = segments[0];
        let module_name = interner.resolve(module_sym);
        tracing::debug!(module_name, "qualified_type: looking up module in scope");

        let module_var = self.scope.get(module_sym);

        let Some(var) = module_var else {
            // First segment not found in scope - this will be caught as undefined variable
            tracing::debug!(module_name, "qualified_type: module not found in scope");
            return self.ty_invalid_traced_id("qualified_path_module_not_found");
        };

        let module_type_id = var.ty;
        tracing::debug!(?module_type_id, "qualified_type: found module binding");

        // Check if the variable is a module type
        let module_info = self.type_arena().unwrap_module(module_type_id).cloned();
        let Some(module_info) = module_info else {
            // Not a module type - emit appropriate error
            let found_type = self.type_display_id(module_type_id);
            tracing::debug!(module_name, found_type, "qualified_type: not a module type");
            // We don't have the span here, but the caller will handle the invalid type
            // For better errors, we would need to pass spans through
            return self.ty_invalid_traced_id(&format!(
                "expected_module:{}:found:{}",
                module_name, found_type
            ));
        };

        // Now look up the type name in the module's exports
        let type_sym = segments[1];
        let type_name = interner.resolve(type_sym);
        tracing::debug!(type_name, ?module_info.module_id, "qualified_type: looking up type in module exports");

        // Find the export by comparing names
        let export_type_id = self
            .module_name_id(module_info.module_id, type_name)
            .and_then(|name_id| {
                tracing::debug!(?name_id, "qualified_type: got name_id for type");
                module_info
                    .exports
                    .iter()
                    .find(|(n, _)| *n == name_id)
                    .map(|&(_, type_id)| type_id)
            });

        let Some(base_type_id) = export_type_id else {
            // Export not found in module
            let module_path = self
                .name_table()
                .module_path(module_info.module_id)
                .to_string();
            tracing::debug!(
                module_path,
                type_name,
                "qualified_type: type not found in exports"
            );
            return self
                .ty_invalid_traced_id(&format!("module_no_export:{}:{}", module_path, type_name));
        };

        tracing::debug!(?base_type_id, "qualified_type: resolved type successfully");

        // If there are more than 2 segments, we don't support nested module paths yet
        if segments.len() > 2 {
            return self.ty_invalid_traced_id("nested_module_paths_not_supported");
        }

        // If there are generic type arguments, apply them
        if !args.is_empty() {
            // Resolve the type arguments
            let type_args: crate::type_arena::TypeIdVec = args
                .iter()
                .map(|arg| self.resolve_type_id_with_self(arg, interner, self_type_id))
                .collect();

            // Get the base type and apply type arguments
            use crate::type_arena::NominalKind;
            let arena = self.type_arena();
            if let Some((type_def_id, _, kind)) = arena.unwrap_nominal(base_type_id) {
                return match kind {
                    NominalKind::Record => self.type_arena_mut().record(type_def_id, type_args),
                    NominalKind::Class => self.type_arena_mut().class(type_def_id, type_args),
                    NominalKind::Interface => {
                        self.type_arena_mut().interface(type_def_id, type_args)
                    }
                    NominalKind::Error => self.type_arena_mut().error_type(type_def_id),
                };
            }
            // For other types, just return the base type (args might be ignored)
        }

        base_type_id
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

                        // Check that never is not used in variable declarations
                        if let Some(decl_type_id) = declared_type_id {
                            self.check_never_not_allowed(decl_type_id, let_stmt.span);
                        }

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
                    self.check_type_body(class, interner)?;
                }
                Decl::Record(record) => {
                    self.check_type_body(record, interner)?;
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

    /// Check field defaults, methods, and static methods for a type declaration.
    /// This is the common logic shared between Class and Record checking.
    fn check_type_body<T: TypeBodyDecl>(
        &mut self,
        decl: &T,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        let type_name = decl.name();

        // Set up type param scope for generic type methods
        let generic_type_params = if !decl.type_params().is_empty() {
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            name_id.and_then(|name_id| {
                let registry = self.entity_registry();
                registry
                    .type_by_name(name_id)
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
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            let field_types = name_id.and_then(|name_id| {
                let registry = self.entity_registry();
                registry
                    .type_by_name(name_id)
                    .and_then(|type_def_id| registry.get_generic_info(type_def_id))
                    .map(|gi| gi.field_types.clone())
            });
            if let Some(field_types) = field_types {
                self.check_field_defaults(decl.fields(), &field_types, interner)?;
            }
        }

        // Check instance methods
        for method in decl.methods() {
            self.check_method(method, type_name, interner)?;
        }

        // Check static methods if present
        if let Some(statics) = decl.statics() {
            for method in &statics.methods {
                self.check_static_method(method, type_name, interner)?;
            }
        }

        // Pop type param scope after checking methods
        if generic_type_params.is_some() {
            self.type_param_stack.pop();
        }

        // Validate interface satisfaction
        self.validate_interfaces_for_type(type_name, decl.span(), interner);

        Ok(())
    }

    /// Validate that a type satisfies all its implemented interfaces.
    fn validate_interfaces_for_type(&mut self, type_name: Symbol, span: Span, interner: &Interner) {
        let maybe_type_def_id = {
            let name_id = self
                .name_table()
                .name_id(self.current_module, &[type_name], interner);
            name_id.and_then(|name_id| self.entity_registry().type_by_name(name_id))
        };

        if let Some(type_def_id) = maybe_type_def_id {
            let type_methods = self.get_type_method_signatures(type_name, interner);
            let interface_ids = self
                .entity_registry()
                .get_implemented_interfaces(type_def_id);

            for interface_id in interface_ids {
                let interface_name_id = self.entity_registry().name_id(interface_id);
                let iface_name_str = self.name_table().last_segment_str(interface_name_id);
                if let Some(iface_name_str) = iface_name_str
                    && let Some(iface_name) = interner.lookup(&iface_name_str)
                {
                    self.validate_interface_satisfaction(
                        type_name,
                        iface_name,
                        &type_methods,
                        span,
                        interner,
                    );
                }
            }
        }
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
                db: &self.ctx.db,
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

    fn is_assert_call(&self, callee: &Expr, interner: &Interner) -> bool {
        if let ExprKind::Identifier(sym) = &callee.kind {
            interner.resolve(*sym) == "assert"
        } else {
            false
        }
    }
}

impl Default for Analyzer {
    fn default() -> Self {
        Self {
            ctx: Rc::new(AnalyzerContext::empty()),
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
            module_loader: ModuleLoader::new(),
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
            current_module: ModuleId::default(),
            type_param_stack: TypeParamScopeStack::new(),
            current_file_path: None,
            in_arm_body: false,
        }
    }
}

#[cfg(test)]
mod tests;

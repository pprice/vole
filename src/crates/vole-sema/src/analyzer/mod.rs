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
mod test_checking;
mod type_constraints;
mod type_helpers;
mod type_resolution;

use type_constraints::validate_defaults;

use crate::ExpressionData;
use crate::analysis_cache::{IsCheckResult, ModuleCache};
use crate::compilation_db::CompilationDb;
use crate::entity_defs::{GenericFuncInfo, TypeDefKind};
use crate::entity_registry::{EntityRegistry, MethodDefBuilder};
use crate::errors::{SemanticError, SemanticWarning, unknown_type_hint};
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
pub use crate::resolve::ResolverEntityExt;
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
use vole_frontend::ast::*;
use vole_frontend::{Interner, Parser, Span};
use vole_identity::{self, MethodId, ModuleId, NameId, NameTable, Namer, Resolver, TypeDefId};

/// Guard that holds a borrow of the name table and provides resolver access.
/// The name table borrow is independent of other CompilationDb fields,
/// so entities/types/implements can be borrowed simultaneously.
pub(crate) struct ResolverGuard<'a> {
    names: std::cell::Ref<'a, NameTable>,
    interner: &'a Interner,
    module_id: ModuleId,
    imports: &'a [ModuleId],
    priority_module: Option<ModuleId>,
}

impl<'a> ResolverGuard<'a> {
    fn new(
        db: &'a CompilationDb,
        interner: &'a Interner,
        module_id: ModuleId,
        imports: &'a [ModuleId],
        priority_module: Option<ModuleId>,
    ) -> Self {
        Self {
            names: db.names(),
            interner,
            module_id,
            imports,
            priority_module,
        }
    }

    /// Get the resolver. The lifetime is tied to this guard.
    pub(crate) fn resolver(&self) -> Resolver<'_> {
        Resolver::new(self.interner, &self.names, self.module_id, self.imports)
            .with_priority_module(self.priority_module)
    }

    /// Resolve a Symbol to a TypeDefId through the resolution chain.
    pub(crate) fn resolve_type(&self, sym: Symbol, registry: &EntityRegistry) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver().resolve_type(sym, registry)
    }

    /// Resolve a type with fallback to interface/class short name search.
    pub(crate) fn resolve_type_or_interface(
        &self,
        sym: Symbol,
        registry: &EntityRegistry,
    ) -> Option<TypeDefId> {
        use crate::resolve::ResolverEntityExt;
        self.resolver().resolve_type_or_interface(sym, registry)
    }

    /// Resolve a type string with fallback to interface/class short name search.
    pub(crate) fn resolve_type_str_or_interface(
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
pub(super) struct CaptureInfo {
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
    /// Shared compilation database containing all registries.
    /// Each field within CompilationDb has its own RefCell for independent borrows.
    pub db: Rc<CompilationDb>,
    /// The module ID for the main program (may differ from main_module when using shared cache)
    pub module_id: ModuleId,
}

/// Module-level data extracted from `AnalyzerContext` during `into_analysis_results`.
///
/// Both the `Ok` (sole owner, move) and `Err` (shared, clone) branches of
/// `Rc::try_unwrap` populate this struct, letting the `ExpressionData` builder
/// chain appear exactly once.
struct ExtractedModuleData {
    data: FxHashMap<String, crate::expression_data::ModuleAnalysisData>,
}

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

/// Builder for creating Analyzer instances with various configurations.
/// Reduces code duplication across constructors by centralizing initialization logic.
pub struct AnalyzerBuilder {
    file: String,
    cache: Option<Rc<RefCell<ModuleCache>>>,
    project_root: Option<PathBuf>,
    auto_detect_root: bool,
    skip_tests: bool,
}

impl AnalyzerBuilder {
    /// Create a new builder for the given file path.
    pub fn new(file: &str) -> Self {
        Self {
            file: file.to_string(),
            cache: None,
            project_root: None,
            auto_detect_root: true,
            skip_tests: false,
        }
    }

    /// Use a shared module cache. The analyzer will use the CompilationDb from the cache.
    pub fn with_cache(mut self, cache: Rc<RefCell<ModuleCache>>) -> Self {
        self.cache = Some(cache);
        self
    }

    /// Skip processing of tests blocks during analysis.
    /// When true, `Decl::Tests` is ignored in all analysis passes.
    pub fn skip_tests(mut self, skip: bool) -> Self {
        self.skip_tests = skip;
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
            (Rc::new(CompilationDb::new()), false)
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
            db.names_mut().module_id(&module_path)
        } else {
            db.main_module()
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
            module: ModuleContext {
                current_module,
                current_file_path,
                module_loader,
                skip_tests: self.skip_tests,
                ..Default::default()
            },
            ..Default::default()
        };

        // Step 7: Register built-in interfaces and implementations
        analyzer.register_builtins();

        analyzer
    }
}

/// Shared state across all Analyzer instances (parent + sub-analyzers).
/// Single `Rc` clone instead of 3-4 individual `Rc` clones per sub-analyzer.
pub(crate) struct AnalyzerContext {
    /// Unified compilation database containing all registries.
    /// Shared via `Rc` so sub-analyzers use the same db, making TypeIds
    /// valid across all analyzers and eliminating clone/merge operations.
    /// Each field within CompilationDb has its own RefCell for independent borrows.
    pub(crate) db: Rc<CompilationDb>,
    /// Cached module TypeIds by import path (avoids re-parsing).
    pub(crate) module_type_ids: RefCell<FxHashMap<String, ArenaTypeId>>,
    /// Parsed module programs and their interners (for compiling pure Vole functions).
    pub(crate) module_programs: RefCell<FxHashMap<String, (Program, Interner)>>,
    /// Per-module analysis data (module path -> ModuleAnalysisData).
    /// NodeIds are file-local and collide across modules, so each module gets
    /// its own set of NodeId-keyed maps. Uses ArenaTypeId (= TypeId) internally.
    pub(crate) module_data: RefCell<FxHashMap<String, crate::expression_data::ModuleAnalysisData>>,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    pub(crate) module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Set of modules currently being analyzed (for circular import detection).
    /// Shared across all sub-analyzers via Rc<AnalyzerContext> so that cycles
    /// are detected even across nested module imports.
    pub(crate) modules_in_progress: RefCell<FxHashSet<String>>,
}

impl AnalyzerContext {
    /// Create a new context with the given db and optional cache.
    fn new(db: Rc<CompilationDb>, cache: Option<Rc<RefCell<ModuleCache>>>) -> Self {
        Self {
            db,
            module_type_ids: RefCell::new(FxHashMap::default()),
            module_programs: RefCell::new(FxHashMap::default()),
            module_data: RefCell::new(FxHashMap::default()),
            module_cache: cache,
            modules_in_progress: RefCell::new(FxHashSet::default()),
        }
    }

    /// Create an empty context (for Default impl).
    fn empty() -> Self {
        Self::new(Rc::new(CompilationDb::new()), None)
    }
}

/// Type checking environment: scope, type overrides, and function context.
#[derive(Default)]
pub(super) struct TypeCheckEnv {
    pub scope: Scope,
    /// Type overrides from flow-sensitive narrowing (e.g., after `if x is T`)
    pub type_overrides: FxHashMap<Symbol, ArenaTypeId>,
    pub current_function_return: Option<ArenaTypeId>,
    /// Current function's error type (if fallible)
    pub current_function_error_type: Option<ArenaTypeId>,
    /// Generator context: if inside a generator function, this holds the Iterator element type.
    /// None means we're not in a generator (or not in a function at all).
    pub current_generator_element_type: Option<ArenaTypeId>,
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
pub(super) struct LambdaState {
    /// Stack of lambda scopes for capture analysis. Each entry is a FxHashMap
    /// mapping captured variable names to their capture info.
    pub captures: Vec<FxHashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    pub locals: Vec<HashSet<Symbol>>,
    /// Stack of side effect flags for currently analyzed lambdas
    pub side_effects: Vec<bool>,
    /// Variable to lambda expression mapping. Tracks which variables hold lambdas with defaults.
    /// Maps Symbol -> (lambda_node_id, required_params)
    pub variables: FxHashMap<Symbol, (NodeId, usize)>,
    /// Lambda defaults for closure calls. Maps call site NodeId to lambda info.
    pub defaults: FxHashMap<NodeId, LambdaDefaults>,
    /// Lambda analysis results (captures and side effects).
    /// Maps lambda expression NodeId -> LambdaAnalysis.
    pub analysis: FxHashMap<NodeId, crate::expression_data::LambdaAnalysis>,
}

/// Analysis results collected during type checking for codegen.
#[derive(Default)]
pub(super) struct AnalysisResults {
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their interned type handles for O(1) equality.
    pub expr_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Type check results for `is` expressions and type patterns (for codegen)
    /// Maps NodeId -> IsCheckResult to eliminate runtime type lookups
    pub is_check_results: FxHashMap<NodeId, IsCheckResult>,
    /// Resolved method calls for codegen
    pub method_resolutions: MethodResolutions,
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    pub generic_calls: FxHashMap<NodeId, MonomorphKey>,
    /// Mapping from method call expression NodeId to ClassMethodMonomorphKey (for generic class method calls)
    pub class_method_calls: FxHashMap<NodeId, ClassMethodMonomorphKey>,
    /// Mapping from static method call expression NodeId to StaticMethodMonomorphKey (for generic static method calls)
    pub static_method_calls: FxHashMap<NodeId, StaticMethodMonomorphKey>,
    /// Substituted return types for generic method calls.
    /// When a method like `list.head()` is called on `List<i32>`, the generic return type `T`
    /// is substituted to `i32`. This map stores the concrete type so codegen doesn't recompute.
    pub substituted_return_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Declared variable types for let statements with explicit type annotations.
    /// Maps init expression NodeId -> declared TypeId for codegen to use.
    pub declared_var_types: FxHashMap<NodeId, ArenaTypeId>,
    /// Virtual module IDs for tests blocks. Maps tests block span to its virtual ModuleId.
    /// Used by codegen to compile scoped type declarations (records, classes) within tests blocks.
    pub tests_virtual_modules: FxHashMap<Span, ModuleId>,
}

/// Function and global variable symbol tables.
#[derive(Default)]
pub(super) struct SymbolTables {
    pub functions: FxHashMap<Symbol, FunctionType>,
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    pub functions_by_name: FxHashMap<String, FunctionType>,
    /// Generic prelude functions by string name -> NameId (for cross-interner generic function lookup)
    pub generic_prelude_functions: FxHashMap<String, NameId>,
    pub globals: FxHashMap<Symbol, ArenaTypeId>,
    /// Globals with constant initializers (for constant expression checking)
    pub constant_globals: HashSet<Symbol>,
}

/// Module loading and file context state.
#[derive(Default)]
pub(super) struct ModuleContext {
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
pub(super) struct Diagnostics {
    pub errors: Vec<TypeError>,
    pub warnings: Vec<TypeWarning>,
}

pub struct Analyzer {
    // Shared state (single Rc clone for sub-analyzers)
    pub(crate) ctx: Rc<AnalyzerContext>,

    // Grouped per-analysis state
    pub(super) env: TypeCheckEnv,
    pub(super) lambda: LambdaState,
    pub(super) results: AnalysisResults,
    pub(super) symbols: SymbolTables,
    pub(super) module: ModuleContext,
    pub(super) diagnostics: Diagnostics,
}

/// Result of looking up a method on a type via EntityRegistry
pub(crate) struct MethodLookup {
    pub(crate) method_id: MethodId,
    pub(crate) signature_id: ArenaTypeId,
}

impl Analyzer {
    /// Create a new Analyzer for the given file.
    /// Auto-detects project root from the file path.
    pub fn new(file: &str) -> Self {
        AnalyzerBuilder::new(file).build()
    }

    /// Set whether to skip processing of tests blocks.
    /// When true, `Decl::Tests` is ignored in all analysis passes.
    pub fn set_skip_tests(&mut self, skip: bool) {
        self.module.skip_tests = skip;
    }

    /// Push a new child scope onto the scope stack.
    pub(crate) fn push_scope(&mut self) {
        self.env.scope = Scope::with_parent(std::mem::take(&mut self.env.scope));
    }

    /// Pop the current scope, restoring the parent.
    pub(crate) fn pop_scope(&mut self) {
        if let Some(parent) = std::mem::take(&mut self.env.scope).into_parent() {
            self.env.scope = parent;
        }
    }

    // Builtin registration: builtins.rs
    // Prelude loading: prelude.rs
    // Error/display helpers: errors.rs
    // Type inference: inference.rs

    /// Get the resolved expression types as interned ArenaTypeId handles.
    pub fn expr_types(&self) -> &FxHashMap<NodeId, ArenaTypeId> {
        &self.results.expr_types
    }

    /// Get the type check results for `is` expressions and type patterns.
    pub fn is_check_results(&self) -> &FxHashMap<NodeId, IsCheckResult> {
        &self.results.is_check_results
    }

    /// Get a resolver configured for the current module context.
    /// Create a resolver for name resolution.
    /// Note: The returned resolver holds a borrow of the db's name_table.
    /// Parent modules are included in the search chain for virtual test modules.
    pub(crate) fn resolver<'a>(&'a self, interner: &'a Interner) -> ResolverGuard<'a> {
        ResolverGuard::new(
            &self.ctx.db,
            interner,
            self.module.current_module,
            &self.env.parent_modules,
            self.env.type_priority_module,
        )
    }

    /// Create a resolver for a specific module context.
    /// Use this when resolving types in an imported module's context.
    pub(crate) fn resolver_for_module<'a>(
        &'a self,
        interner: &'a Interner,
        module_id: ModuleId,
    ) -> ResolverGuard<'a> {
        ResolverGuard::new(&self.ctx.db, interner, module_id, &[], None)
    }

    /// Take ownership of the expression types (consuming self)
    pub fn into_expr_types(self) -> FxHashMap<NodeId, ArenaTypeId> {
        self.results.expr_types
    }

    /// Take accumulated warnings, leaving the warnings list empty
    pub fn take_warnings(&mut self) -> Vec<TypeWarning> {
        std::mem::take(&mut self.diagnostics.warnings)
    }

    /// Take ownership of analysis results (consuming self)
    pub fn into_analysis_results(self) -> AnalysisOutput {
        // Extract per-analysis fields before consuming ctx
        let results = self.results;
        let expr_types = results.expr_types;
        let method_resolutions = results.method_resolutions.into_inner();
        let generic_calls = results.generic_calls;
        let class_method_calls = results.class_method_calls;
        let static_method_calls = results.static_method_calls;
        let substituted_return_types = results.substituted_return_types;
        let tests_virtual_modules = results.tests_virtual_modules;
        let is_check_results = results.is_check_results;
        let declared_var_types = results.declared_var_types;
        let lambda = self.lambda;
        let lambda_defaults = lambda.defaults;
        let lambda_analysis = lambda.analysis;
        let current_module = self.module.current_module;

        // Try to take ownership of the shared context to avoid cloning AST trees.
        // By this point all sub-analyzers should be dropped, so Rc strong count is 1.
        let (module_data, module_programs, db) = match Rc::try_unwrap(self.ctx) {
            Ok(ctx) => {
                // Sole owner: move data out of RefCells without cloning
                let data = ExtractedModuleData {
                    data: ctx.module_data.into_inner(),
                };
                (data, ctx.module_programs.into_inner(), ctx.db)
            }
            Err(ctx) => {
                // Other references exist: fall back to cloning (should not happen in practice)
                let data = ExtractedModuleData {
                    data: ctx.module_data.borrow().clone(),
                };
                (
                    data,
                    ctx.module_programs.borrow().clone(),
                    Rc::clone(&ctx.db),
                )
            }
        };

        let expression_data = ExpressionData::builder()
            .types(expr_types)
            .methods(method_resolutions)
            .generics(generic_calls)
            .class_method_generics(class_method_calls)
            .static_method_generics(static_method_calls)
            .module_data(module_data.data)
            .substituted_return_types(substituted_return_types)
            .lambda_defaults(lambda_defaults)
            .tests_virtual_modules(tests_virtual_modules)
            .is_check_results(is_check_results)
            .declared_var_types(declared_var_types)
            .lambda_analysis(lambda_analysis)
            .build();

        AnalysisOutput {
            expression_data,
            module_programs,
            db,
            module_id: current_module,
        }
    }

    /// Record the resolved type for an expression using TypeId directly.
    /// Also pre-creates RuntimeIterator types for Iterator<T> return types,
    /// so codegen can look them up without needing mutable arena access.
    fn record_expr_type_id(&mut self, expr: &Expr, type_id: ArenaTypeId) -> ArenaTypeId {
        // Pre-create RuntimeIterator(T) for Iterator<T> types so codegen can look them up
        self.ensure_runtime_iterator_for_iterator(type_id);
        self.results.expr_types.insert(expr.id, type_id);
        type_id
    }

    /// Record the result of a type check (is expression or type pattern) for codegen.
    fn record_is_check_result(&mut self, node_id: NodeId, result: IsCheckResult) {
        self.results.is_check_results.insert(node_id, result);
    }

    /// Get the display name for a type parameter.
    /// For synthetic type params (created for implicit generification), we use the name_id
    /// since the Symbol is not a real interned string.
    fn get_type_param_display_name(&self, param: &TypeParamInfo, interner: &Interner) -> String {
        // Synthetic type params have Symbol values >= 0x80000000
        // (we use Symbol::synthetic(i) for them)
        if param.name.index() >= 0x8000_0000 {
            // Use name_id for synthetic type params
            self.name_table()
                .last_segment_str(param.name_id)
                .unwrap_or_else(|| format!("__T{}", param.name.index() - 0x8000_0000))
        } else {
            // Try name_id first (cross-interner safe), fall back to interner
            self.name_table()
                .last_segment_str(param.name_id)
                .unwrap_or_else(|| interner.resolve(param.name).to_string())
        }
    }

    /// If the given type is Iterator<T>, ensure RuntimeIterator(T) exists in the arena.
    /// This allows codegen to convert Iterator return types to RuntimeIterator without
    /// needing mutable arena access.
    fn ensure_runtime_iterator_for_iterator(&mut self, type_id: ArenaTypeId) {
        // Primitive/reserved types (id < FIRST_DYNAMIC) are never interfaces,
        // so skip the arena lookup and RefCell borrow for the common case.
        if type_id.index() < ArenaTypeId::FIRST_DYNAMIC {
            return;
        }
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

    // === Accessors for db fields (each independently borrowable) ===

    /// Get the type arena (read access)
    #[inline]
    fn type_arena(&self) -> std::cell::Ref<'_, TypeArena> {
        self.ctx.db.types()
    }

    /// Get the type arena (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn type_arena_mut(&self) -> std::cell::RefMut<'_, TypeArena> {
        self.ctx.db.types_mut()
    }

    /// Get the entity registry (read access)
    #[inline]
    fn entity_registry(&self) -> std::cell::Ref<'_, EntityRegistry> {
        self.ctx.db.entities()
    }

    /// Get the entity registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn entity_registry_mut(&self) -> std::cell::RefMut<'_, EntityRegistry> {
        self.ctx.db.entities_mut()
    }

    /// Get the name table (read access)
    #[inline]
    fn name_table(&self) -> std::cell::Ref<'_, NameTable> {
        self.ctx.db.names()
    }

    /// Get the name table (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn name_table_mut(&self) -> std::cell::RefMut<'_, NameTable> {
        self.ctx.db.names_mut()
    }

    /// Get the implement registry (read access)
    #[inline]
    fn implement_registry(&self) -> std::cell::Ref<'_, ImplementRegistry> {
        self.ctx.db.implements()
    }

    /// Get the implement registry (write access) - uses Rc::make_mut for copy-on-write
    #[inline]
    fn implement_registry_mut(&self) -> std::cell::RefMut<'_, ImplementRegistry> {
        self.ctx.db.implements_mut()
    }

    /// Check if we're currently inside a lambda
    fn in_lambda(&self) -> bool {
        !self.lambda.captures.is_empty()
    }

    /// Check if a symbol is a local variable in the current lambda
    fn is_lambda_local(&self, sym: Symbol) -> bool {
        if let Some(locals) = self.lambda.locals.last() {
            locals.contains(&sym)
        } else {
            false
        }
    }

    /// Add a local variable to the current lambda's locals set
    fn add_lambda_local(&mut self, sym: Symbol) {
        if let Some(locals) = self.lambda.locals.last_mut() {
            locals.insert(sym);
        }
    }

    /// Record a captured variable in the current lambda and all enclosing lambdas.
    ///
    /// For transitive captures (nested closures capturing from outer scope),
    /// all intermediate lambdas must also capture the variable to pass it through.
    fn record_capture(&mut self, sym: Symbol, is_mutable: bool) {
        // Propagate capture from innermost to outermost lambda
        // Stop when we find a lambda where the variable is a local
        for i in (0..self.lambda.captures.len()).rev() {
            // Check if this variable is a local at this lambda level
            if let Some(locals) = self.lambda.locals.get(i)
                && locals.contains(&sym)
            {
                // Variable is defined at this level, no need to capture
                break;
            }

            // Not a local at this level, so it must be captured
            if let Some(captures) = self.lambda.captures.get_mut(i) {
                captures.entry(sym).or_insert(CaptureInfo {
                    name: sym,
                    is_mutable,
                    is_mutated: false,
                });
            }
        }
    }

    /// Mark a captured variable as mutated in all lambdas that capture it
    fn mark_capture_mutated(&mut self, sym: Symbol) {
        for i in (0..self.lambda.captures.len()).rev() {
            // Stop if variable is a local at this level
            if let Some(locals) = self.lambda.locals.get(i)
                && locals.contains(&sym)
            {
                break;
            }

            // Mark as mutated if captured at this level
            if let Some(captures) = self.lambda.captures.get_mut(i)
                && let Some(info) = captures.get_mut(&sym)
            {
                info.is_mutated = true;
            }
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
        if let Some(flag) = self.lambda.side_effects.last_mut() {
            *flag = true;
        }
    }

    /// Get variable type as TypeId with flow-sensitive overrides
    fn get_variable_type_id(&self, sym: Symbol) -> Option<ArenaTypeId> {
        // Check overrides first (for narrowed types inside if-blocks)
        if let Some(ty) = self.env.type_overrides.get(&sym) {
            return Some(*ty);
        }
        // Then check scope
        self.env.scope.get(sym).map(|v| v.ty)
    }

    /// Get function type if the symbol refers to a top-level function.
    /// Returns None if the symbol is not a function name.
    fn get_function_type(&self, sym: Symbol, interner: &Interner) -> Option<FunctionType> {
        // Check by Symbol first (same interner)
        if let Some(func_type) = self.symbols.functions.get(&sym) {
            return Some(func_type.clone());
        }
        // Check by name for prelude functions (cross-interner lookup)
        let name = interner.resolve(sym);
        self.symbols.functions_by_name.get(name).cloned()
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
        self.load_prelude();

        // Clear monomorph caches from any previous analysis.
        // When using a shared ModuleCache across multiple test files, the entity_registry
        // accumulates monomorph instances from previous files. These instances reference
        // class/method definitions that exist only in those previous files, causing
        // "method X not found in class Y" errors during codegen. Clearing these
        // caches ensures each main program analysis starts fresh while still benefiting
        // from cached prelude analysis (prelude modules don't have generic classes that
        // get monomorphized in the main program).
        //
        // Only clear when this is the main program analysis (loading_prelude == false).
        // Sub-analyzers for imported modules (loading_prelude == true) share the parent's
        // entity registry via ctx, so clearing here would destroy monomorph instances
        // created by earlier tests blocks that have already been analyzed.
        if !self.module.loading_prelude {
            self.entity_registry_mut().clear_monomorph_caches();
        }

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
        {
            let entities = self.entity_registry();
            let mut names = self.name_table_mut();
            crate::well_known::populate_type_def_ids(&mut names, &entities);
        }

        // Process global let declarations
        self.process_global_lets(program, interner)?;

        // Pass 2: type check function bodies and tests
        self.check_declaration_bodies(program, interner)?;

        // Pass 2.5: Propagate concrete substitutions to class method monomorphs.
        // Generic class bodies record identity monomorphs for self-calls (T -> TypeParam(T)).
        // This pass derives concrete callee instances (e.g., T -> i64) from concrete callers.
        self.propagate_class_method_monomorphs();
        self.propagate_static_method_monomorphs();

        // Pass 3: analyze monomorphized function bodies to discover nested generic calls
        // This iterates until no new MonomorphInstances are created
        self.analyze_monomorph_bodies(program, interner);

        if self.diagnostics.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.diagnostics.errors))
        }
    }

    /// Analyze a program as a virtual module (used for tests blocks).
    ///
    /// Runs the standard analysis pipeline (shells, aliases, imports, signatures,
    /// globals, bodies) but with virtual module isolation:
    /// - Type shells and type signatures are registered under `virtual_module_id`
    /// - Function signatures are registered under the parent module (current_module)
    /// - Imports resolve against the parent file path
    /// - Prelude/primitives are NOT re-loaded (already in parent)
    pub(crate) fn analyze_virtual_module(
        &mut self,
        program: &Program,
        interner: &Interner,
        virtual_module_id: ModuleId,
    ) {
        let parent_module = self.module.current_module;

        // Register type shells under the virtual module for scope isolation
        self.module.current_module = virtual_module_id;
        self.register_all_type_shells(program, interner);

        // Add the virtual module to parent_modules so the resolver can find
        // types registered under the virtual module
        self.env.parent_modules.push(virtual_module_id);

        // Set the virtual module as the priority module for type resolution.
        // Types defined in the tests block shadow parent types of the same name.
        self.env.type_priority_module = Some(virtual_module_id);

        // Resolve type aliases (uses resolver which searches parent_modules)
        self.collect_type_aliases(program, interner);

        // Process module imports under the parent module so relative import paths
        // resolve against the actual file, not the virtual module
        self.module.current_module = parent_module;
        self.process_module_imports(program, interner);

        // Collect type signatures under the virtual module (matches shells above)
        self.module.current_module = virtual_module_id;
        self.collect_type_signatures(program, interner);

        // Collect function signatures under the parent module so codegen can
        // find them via program_module() lookups
        self.module.current_module = parent_module;
        self.collect_function_signatures(program, interner);

        // Process global lets (scoped lets in the tests block)
        let _ = self.process_global_lets(program, interner);

        // Check declaration bodies (including nested tests blocks)
        let _ = self.check_declaration_bodies(program, interner);
    }

    /// Pass 0: Collect type aliases (so they're available for function signatures)
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
                    if !self.module.skip_tests {
                        self.check_tests(tests_decl, interner)?;
                    }
                }
                Decl::Let(_) | Decl::LetTuple(_) => {
                    // Already processed in process_global_lets/process_module_imports
                }
                Decl::Class(class) => {
                    self.check_type_body(class, interner)?;
                }
                Decl::Interface(interface_decl) => {
                    // Note: Interface default method bodies are NOT checked here because they
                    // are compiled in the context of implementing types, not the interface.
                    // The fallback to I64/F64 for literals in codegen handles these cases.
                    // A proper fix would analyze default methods when inherited by implementing types.

                    // Check static method default bodies
                    if let Some(ref statics) = interface_decl.statics {
                        for method in &statics.methods {
                            self.check_static_method(method, interface_decl.name, interner)?;
                        }
                    }
                }
                Decl::Implement(impl_block) => {
                    // Skip generator-transformed implement blocks - their method bodies
                    // reference variables that only exist at codegen time after full
                    // generator state machine transformation
                    let is_generated = match &impl_block.target_type.kind {
                        TypeExprKind::Named(sym) => {
                            interner.resolve(*sym).starts_with("__Generator_")
                        }
                        _ => false,
                    };

                    if !is_generated {
                        // Push type param scope for generic implement blocks so that
                        // type parameters (e.g., K, V) are available during body checking.
                        // Without this, match patterns and is-expressions inside the method
                        // body can't resolve union variant types properly.
                        let inferred_scope =
                            self.infer_implement_type_params(&impl_block.target_type, interner);
                        let has_type_param_scope = !inferred_scope.is_empty();
                        if has_type_param_scope {
                            self.env.type_param_stack.push_scope(inferred_scope);
                        }

                        // Resolve target type to TypeId for checking instance methods
                        let target_type_id =
                            self.resolve_type_id(&impl_block.target_type, interner);

                        // Check instance methods in implement blocks
                        for method in &impl_block.methods {
                            self.check_implement_method(method, target_type_id, interner)?;
                        }

                        if has_type_param_scope {
                            self.env.type_param_stack.pop();
                        }
                    }

                    // Check static methods in implement blocks
                    if let Some(ref statics) = impl_block.statics {
                        match &impl_block.target_type.kind {
                            TypeExprKind::Named(type_name) => {
                                for method in &statics.methods {
                                    self.check_static_method(method, *type_name, interner)?;
                                }
                            }
                            TypeExprKind::Primitive(prim) => {
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
                Decl::Struct(struct_decl) => {
                    self.check_type_body(struct_decl, interner)?;
                }
                Decl::Error(_) => {
                    // Error declarations fully processed in first pass
                }
                Decl::Sentinel(_) => {
                    // Sentinel declarations are processed in the first pass
                }
                Decl::External(_) => {
                    // External blocks are processed during code generation
                }
            }
        }
        Ok(())
    }

    /// Check if an expression is a constant expression.
    /// Constant expressions are: literals, unary/binary ops on constants,
    /// array/tuple literals with constant elements, and references to
    /// immutable globals with constant initializers.
    fn is_constant_expr(&self, expr: &Expr) -> bool {
        match &expr.kind {
            // Literals are constant
            ExprKind::IntLiteral(..)
            | ExprKind::FloatLiteral(..)
            | ExprKind::BoolLiteral(_)
            | ExprKind::StringLiteral(_) => true,

            // Identifier: constant if it's an immutable global with a constant initializer
            ExprKind::Identifier(sym) => self.symbols.constant_globals.contains(sym),

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
}

impl Default for Analyzer {
    fn default() -> Self {
        Self {
            ctx: Rc::new(AnalyzerContext::empty()),
            env: TypeCheckEnv::default(),
            lambda: LambdaState::default(),
            results: AnalysisResults::default(),
            symbols: SymbolTables::default(),
            module: ModuleContext::default(),
            diagnostics: Diagnostics::default(),
        }
    }
}

#[cfg(test)]
mod tests;

// Analysis output, builder, and diagnostic types for the analyzer.

use crate::ExpressionData;
use crate::FunctionType;
use crate::analysis_cache::{IsCheckResult, ModuleCache};
use crate::compilation_db::CompilationDb;
use crate::errors::{SemanticError, SemanticWarning};
use crate::generic::{ClassMethodMonomorphKey, MonomorphKey, StaticMethodMonomorphKey};
use crate::module::ModuleLoader;
use crate::resolution::MethodResolutions;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;
use vole_frontend::Span;
use vole_frontend::ast::{NodeId, Symbol};
use vole_identity::{MethodId, ModuleId, NameId};

use super::Analyzer;
use super::context::AnalyzerContext;
use super::state::ModuleContext;

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
    pub module_programs: FxHashMap<String, (vole_frontend::ast::Program, vole_frontend::Interner)>,
    /// Shared compilation database containing all registries.
    /// Each field within CompilationDb has its own RefCell for independent borrows.
    pub db: Rc<CompilationDb>,
    /// The module ID for the main program (may differ from main_module when using shared cache)
    pub module_id: ModuleId,
    /// Module paths that had sema errors during analysis.
    /// Codegen should skip compiling function bodies for these modules to avoid
    /// encountering INVALID type IDs from failed type checking.
    pub modules_with_errors: HashSet<String>,
}

/// Analysis results collected during type checking for codegen.
#[derive(Default)]
pub(crate) struct AnalysisResults {
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
    /// Resolved intrinsic keys for compiler intrinsic calls (for optimizer constant folding).
    /// Maps call-site NodeId to the resolved intrinsic key (e.g., "f64_sqrt").
    pub intrinsic_keys: FxHashMap<NodeId, String>,
}

/// Function and global variable symbol tables.
#[derive(Default)]
pub(crate) struct SymbolTables {
    pub functions: FxHashMap<Symbol, FunctionType>,
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    pub functions_by_name: FxHashMap<String, FunctionType>,
    /// Generic prelude functions by string name -> NameId (for cross-interner generic function lookup)
    pub generic_prelude_functions: FxHashMap<String, NameId>,
    pub globals: FxHashMap<Symbol, ArenaTypeId>,
    /// Globals with constant initializers (for constant expression checking)
    pub constant_globals: HashSet<Symbol>,
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

/// Result of looking up a method on a type via EntityRegistry
pub(crate) struct MethodLookup {
    pub(crate) method_id: MethodId,
    pub(crate) signature_id: ArenaTypeId,
}

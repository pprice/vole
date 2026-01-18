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

use crate::errors::{SemanticError, SemanticWarning};
use crate::frontend::*;
use crate::identity::{self, MethodId, ModuleId, NameId, NameTable, Namer, Resolver, TypeDefId};
use crate::module::ModuleLoader;
use crate::sema::EntityRegistry;
use crate::sema::ExpressionData;
use crate::sema::analysis_cache::ModuleCache;
use crate::sema::entity_defs::TypeDefKind;
use crate::sema::generic::{
    ClassMethodMonomorphKey, MonomorphInstance, MonomorphKey, StaticMethodMonomorphKey,
    TypeParamInfo, TypeParamScope, TypeParamScopeStack, TypeParamVariance,
};
use crate::sema::implement_registry::{
    ExternalMethodInfo, ImplTypeId, ImplementRegistry, MethodImpl,
};
use crate::sema::resolution::{MethodResolutions, ResolvedMethod};
use crate::sema::resolve::resolve_type_with_arena;
use crate::sema::type_arena::{TypeArena, TypeId as ArenaTypeId};
use crate::sema::types::{ConstantValue, LegacyType, ModuleType, NominalType, StructuralType};
use crate::sema::{
    ClassType, ErrorTypeInfo, FunctionType, PrimitiveType, RecordType, StructField,
    compatibility::TypeCompatibility,
    resolve::{TypeResolutionContext, resolve_type},
    scope::{Scope, Variable},
};
use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Check if a type param's constraint (found) satisfies a required constraint.
/// Returns true if found has at least as strong constraints as required.
fn constraint_satisfied(
    found: &Option<crate::sema::generic::TypeConstraint>,
    required: &crate::sema::generic::TypeConstraint,
) -> bool {
    use crate::sema::generic::TypeConstraint;

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
        // Union constraints: found must be a subset of or equal to required
        (TypeConstraint::Union(found_types), TypeConstraint::Union(required_types)) => {
            // All found types must be in the required types
            found_types
                .iter()
                .all(|f| required_types.iter().any(|r| f == r))
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
    /// Methods added via implement blocks (includes external_func_info)
    pub implement_registry: ImplementRegistry,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    pub module_programs: FxHashMap<String, (Program, Interner)>,
    /// Fully-qualified name interner for printable identities
    pub name_table: NameTable,
    /// Entity registry for first-class type/method/field/function identity (includes type_table)
    pub entity_registry: EntityRegistry,
    /// Shared type arena for interned types (needed by ExpressionData for type lookups)
    pub type_arena: Rc<RefCell<TypeArena>>,
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
    functions: HashMap<Symbol, FunctionType>,
    /// Functions registered by string name (for prelude functions that cross interner boundaries)
    functions_by_name: FxHashMap<String, FunctionType>,
    globals: HashMap<Symbol, ArenaTypeId>,
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
    type_overrides: HashMap<Symbol, ArenaTypeId>,
    /// Stack of lambda scopes for capture analysis. Each entry is a HashMap
    /// mapping captured variable names to their capture info.
    lambda_captures: Vec<HashMap<Symbol, CaptureInfo>>,
    /// Stack of sets tracking variables defined locally in each lambda
    /// (parameters and let bindings inside the lambda body)
    lambda_locals: Vec<HashSet<Symbol>>,
    /// Stack of side effect flags for currently analyzed lambdas
    lambda_side_effects: Vec<bool>,
    /// Resolved types for each expression node (for codegen)
    /// Maps expression node IDs to their interned type handles for O(1) equality.
    /// Converted to LegacyType at boundaries when passed to codegen.
    expr_types: HashMap<NodeId, ArenaTypeId>,
    /// Methods added via implement blocks
    pub implement_registry: ImplementRegistry,
    /// Resolved method calls for codegen
    pub method_resolutions: MethodResolutions,
    /// Module loader for handling imports
    module_loader: ModuleLoader,
    /// Analyzed module types by import path
    module_types: FxHashMap<String, ModuleType>,
    /// Parsed module programs and their interners (for compiling pure Vole functions)
    module_programs: FxHashMap<String, (Program, Interner)>,
    /// Expression types for module programs (keyed by module path -> NodeId -> ArenaTypeId)
    /// Stored separately since NodeIds are per-program and can't be merged into main expr_types.
    /// Uses interned ArenaTypeId handles for O(1) equality during analysis.
    pub module_expr_types: FxHashMap<String, HashMap<NodeId, ArenaTypeId>>,
    /// Method resolutions for module programs (keyed by module path -> NodeId -> ResolvedMethod)
    /// Stored separately since NodeIds are per-program and can't be merged into main method_resolutions
    pub module_method_resolutions: FxHashMap<String, HashMap<NodeId, ResolvedMethod>>,
    /// Flag to prevent recursive prelude loading
    loading_prelude: bool,
    /// Mapping from call expression NodeId to MonomorphKey (for generic function calls)
    generic_calls: HashMap<NodeId, MonomorphKey>,
    /// Mapping from method call expression NodeId to ClassMethodMonomorphKey (for generic class method calls)
    class_method_calls: HashMap<NodeId, ClassMethodMonomorphKey>,
    /// Mapping from static method call expression NodeId to StaticMethodMonomorphKey (for generic static method calls)
    static_method_calls: HashMap<NodeId, StaticMethodMonomorphKey>,
    /// Fully-qualified name interner for printable identities
    name_table: NameTable,
    /// Current module being analyzed (for proper NameId registration)
    current_module: ModuleId,
    /// Entity registry for first-class type/method/field/function identity (includes type_table)
    pub entity_registry: EntityRegistry,
    /// Stack of type parameter scopes for nested generic contexts.
    /// Used for resolving methods on LegacyType::TypeParam via constraint interfaces.
    type_param_stack: TypeParamScopeStack,
    /// Optional shared cache for module analysis results.
    /// When set, modules are cached after analysis and reused across Analyzer instances.
    module_cache: Option<Rc<RefCell<ModuleCache>>>,
    /// Shared type arena for interned types (O(1) equality, reduced allocations).
    /// Shared via Rc<RefCell> so sub-analyzers use the same arena, making TypeIds
    /// valid across all analyzers and eliminating conversion at cache boundaries.
    pub type_arena: Rc<RefCell<TypeArena>>,
}

/// Result of looking up a method on a type via EntityRegistry
pub struct MethodLookup {
    pub method_id: MethodId,
    pub signature: FunctionType,
}

impl Analyzer {
    pub fn new(_file: &str, _source: &str) -> Self {
        // Create name_table first to get main_module
        let name_table = NameTable::new();
        let main_module = name_table.main_module();

        let mut analyzer = Self {
            scope: Scope::new(),
            functions: HashMap::new(),
            functions_by_name: FxHashMap::default(),
            globals: HashMap::new(),
            current_function_return: None,
            current_function_error_type: None,
            current_generator_element_type: None,
            current_static_method: None,
            errors: Vec::new(),
            warnings: Vec::new(),
            type_overrides: HashMap::new(),
            lambda_captures: Vec::new(),
            lambda_locals: Vec::new(),
            lambda_side_effects: Vec::new(),
            expr_types: HashMap::new(),
            implement_registry: ImplementRegistry::new(),
            method_resolutions: MethodResolutions::new(),
            module_loader: ModuleLoader::new(),
            module_types: FxHashMap::default(),
            module_programs: FxHashMap::default(),
            module_expr_types: FxHashMap::default(),
            module_method_resolutions: FxHashMap::default(),
            loading_prelude: false,
            generic_calls: HashMap::new(),
            class_method_calls: HashMap::new(),
            static_method_calls: HashMap::new(),
            name_table,
            current_module: main_module,
            entity_registry: EntityRegistry::new(),
            type_param_stack: TypeParamScopeStack::new(),
            module_cache: None,
            type_arena: Rc::new(RefCell::new(TypeArena::new())),
        };

        // Register primitives in EntityRegistry so they can have static methods
        analyzer
            .entity_registry
            .register_primitives(&analyzer.name_table);

        // Register built-in interfaces and implementations
        // NOTE: This is temporary - will eventually come from stdlib/traits.void
        analyzer.register_builtins();

        analyzer
    }

    /// Create an analyzer with a shared module cache.
    /// The cache is shared across multiple Analyzer instances to avoid
    /// re-analyzing the same modules (prelude, stdlib, user imports).
    /// The analyzer uses the TypeArena from the cache to ensure TypeIds remain valid.
    pub fn with_cache(_file: &str, _source: &str, cache: Rc<RefCell<ModuleCache>>) -> Self {
        // Get the shared arena from the cache BEFORE borrowing cache again
        let shared_arena = cache.borrow().type_arena();
        let mut analyzer = Self::new(_file, _source);
        analyzer.module_cache = Some(cache);
        // Use the cache's arena instead of the freshly created one
        analyzer.type_arena = shared_arena;
        analyzer
    }

    // Builtin registration: builtins.rs
    // Prelude loading: prelude.rs
    // Error/display helpers: errors.rs
    // Type inference: inference.rs

    /// Get the resolved expression types as interned ArenaTypeId handles.
    /// Use type_arena.to_type() to convert back to LegacyType if needed.
    pub fn expr_types(&self) -> &HashMap<NodeId, ArenaTypeId> {
        &self.expr_types
    }

    /// Get a resolver configured for the current module context.
    /// Uses the resolution chain: primitives -> current module -> builtin module.
    pub fn resolver<'a>(&'a self, interner: &'a Interner) -> Resolver<'a> {
        // For now, we don't track imports at the Analyzer level.
        // The resolver will check: primitives, current module, then builtin module.
        Resolver::new(interner, &self.name_table, self.current_module, &[])
    }

    /// Take ownership of the expression types (consuming self)
    pub fn into_expr_types(self) -> HashMap<NodeId, ArenaTypeId> {
        self.expr_types
    }

    /// Take accumulated warnings, leaving the warnings list empty
    pub fn take_warnings(&mut self) -> Vec<TypeWarning> {
        std::mem::take(&mut self.warnings)
    }

    /// Take ownership of analysis results (consuming self)
    pub fn into_analysis_results(self) -> AnalysisOutput {
        // Pass Types directly - ExpressionData now stores Type handles
        // and has access to the shared arena for LegacyType conversion
        let expression_data = ExpressionData::from_analysis(
            self.expr_types,
            self.method_resolutions.into_inner(),
            self.generic_calls,
            self.class_method_calls,
            self.static_method_calls,
            self.module_expr_types,
            self.module_method_resolutions,
            self.type_arena.clone(),
        );
        AnalysisOutput {
            expression_data,
            implement_registry: self.implement_registry,
            module_programs: self.module_programs,
            name_table: self.name_table,
            entity_registry: self.entity_registry,
            type_arena: self.type_arena,
        }
    }

    /// Record the resolved type for an expression, returning the type for chaining.
    /// Interns the LegacyType to an ArenaTypeId handle for O(1) storage and comparison.
    fn record_expr_type(&mut self, expr: &Expr, ty: LegacyType) -> LegacyType {
        let type_id = self.type_arena.borrow_mut().from_type(&ty);
        self.expr_types.insert(expr.id, type_id);
        ty
    }

    /// Record the resolved type for an expression using TypeId directly.
    fn record_expr_type_id(&mut self, expr: &Expr, type_id: ArenaTypeId) -> ArenaTypeId {
        self.expr_types.insert(expr.id, type_id);
        type_id
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

    fn register_named_type(&mut self, name: Symbol, ty: LegacyType, interner: &Interner) {
        let name_id = self
            .name_table
            .intern(self.current_module, &[name], interner);
        self.entity_registry.type_table.insert_named(ty, name_id);
    }

    fn module_name_id(&self, module_id: ModuleId, name: &str) -> Option<NameId> {
        let module_path = self.name_table.module_path(module_id);
        let (_, module_interner) = self.module_programs.get(module_path)?;
        let sym = module_interner.lookup(name)?;
        self.name_table.name_id(module_id, &[sym], module_interner)
    }

    fn interface_type(
        &mut self,
        name: &str,
        type_args: Vec<LegacyType>,
        interner: &Interner,
    ) -> Option<LegacyType> {
        // Look up interface by string name using resolver with interface fallback
        let type_def_id = self
            .resolver(interner)
            .resolve_type_str_or_interface(name, &self.entity_registry)?;
        let type_def = self.entity_registry.get_type(type_def_id);

        // Check type params match
        if !type_def.type_params.is_empty() && type_def.type_params.len() != type_args.len() {
            return Some(LegacyType::invalid("propagate"));
        }

        // Convert type_args to TypeId for arena-based substitution
        let type_args_id: crate::sema::type_arena::TypeIdVec = type_args
            .iter()
            .map(|t| self.type_arena.borrow_mut().from_type(t))
            .collect();

        // Build substitution map using TypeId
        let substitutions = self
            .entity_registry
            .substitution_map_id(type_def_id, &type_args_id);

        // Build methods with substituted types using arena-based substitution
        let methods: Vec<crate::sema::types::InterfaceMethodType> = type_def
            .methods
            .iter()
            .map(|&method_id| {
                let method = self.entity_registry.get_method(method_id);

                // Ensure signature has interned IDs
                let sig = if method.signature.has_interned_ids() {
                    method.signature.clone()
                } else {
                    method
                        .signature
                        .clone()
                        .with_interned_ids(&mut self.type_arena.borrow_mut())
                };

                // Substitute using arena
                let mut arena = self.type_arena.borrow_mut();
                let new_params_id: crate::sema::type_arena::TypeIdVec = sig
                    .params_id
                    .as_ref()
                    .map(|ids| {
                        ids.iter()
                            .map(|&p| arena.substitute(p, &substitutions))
                            .collect()
                    })
                    .unwrap_or_default();
                let new_return_id = sig
                    .return_type_id
                    .map(|r| arena.substitute(r, &substitutions))
                    .unwrap_or_else(|| arena.void());

                // Convert back to LegacyType for InterfaceMethodType
                let new_params: std::sync::Arc<[LegacyType]> = new_params_id
                    .iter()
                    .map(|&id| arena.to_type(id))
                    .collect::<Vec<_>>()
                    .into();
                let new_return = arena.to_type(new_return_id);

                crate::sema::types::InterfaceMethodType {
                    name: method.name_id,
                    params: new_params,
                    return_type: Box::new(new_return),
                    has_default: method.has_default,
                }
            })
            .collect();

        Some(LegacyType::Nominal(NominalType::Interface(
            crate::sema::types::InterfaceType {
                type_def_id,
                type_args_id,
                methods: methods.into(),
                extends: type_def.extends.clone().into(),
            },
        )))
    }

    fn method_name_id(&mut self, name: Symbol, interner: &Interner) -> NameId {
        let mut namer = Namer::new(&mut self.name_table, interner);
        namer.method(name)
    }

    /// Look up a method NameId by string name (cross-interner safe)
    fn method_name_id_by_str(&self, name_str: &str, interner: &Interner) -> Option<NameId> {
        identity::method_name_id_by_str(&self.name_table, interner, name_str)
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
            .entity_registry
            .find_method_on_type(type_def_id, method_name_id)?;
        let method_def = self.entity_registry.get_method(method_id);
        Some(MethodLookup {
            method_id,
            signature: method_def.signature.clone(),
        })
    }

    /// Mark the current lambda as having side effects
    fn mark_lambda_has_side_effects(&mut self) {
        if let Some(flag) = self.lambda_side_effects.last_mut() {
            *flag = true;
        }
    }

    /// Get variable type with flow-sensitive overrides
    fn get_variable_type(&self, sym: Symbol) -> Option<LegacyType> {
        // Check overrides first (for narrowed types inside if-blocks)
        if let Some(ty) = self.type_overrides.get(&sym) {
            return Some(self.type_arena.borrow().to_type(*ty));
        }
        // Then check scope
        let arena = self.type_arena.borrow();
        self.scope.get(sym).map(|v| arena.to_type(v.ty))
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

        // Populate well-known types after prelude has registered all interfaces
        self.name_table.populate_well_known();

        // Pass 0.5: Register type shells for forward reference support
        // This allows types to reference each other regardless of declaration order
        self.register_all_type_shells(program, interner);

        // Pass 0: Resolve type aliases (now that shells exist, can reference forward types)
        self.collect_type_aliases(program, interner);

        // Pass 1: Collect signatures for all declarations (shells already exist)
        self.collect_signatures(program, interner);

        // Populate well-known TypeDefIds now that interfaces are registered
        crate::sema::well_known::populate_type_def_ids(&mut self.name_table, &self.entity_registry);

        // Process global let declarations
        self.process_global_lets(program, interner)?;

        // Pass 2: type check function bodies and tests
        self.check_declaration_bodies(program, interner)?;

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    fn resolve_type(&mut self, ty: &TypeExpr, interner: &Interner) -> LegacyType {
        self.resolve_type_with_self(ty, interner, None)
    }

    /// Resolve a type expression directly to TypeId (no LegacyType intermediate)
    pub(crate) fn resolve_type_id(&mut self, ty: &TypeExpr, interner: &Interner) -> ArenaTypeId {
        let module_id = self.current_module;
        let mut arena = self.type_arena.borrow_mut();
        let mut ctx = TypeResolutionContext {
            entity_registry: &self.entity_registry,
            interner,
            name_table: &mut self.name_table,
            module_id,
            type_params: self.type_param_stack.current(),
            self_type: None,
            type_arena: None, // Arena passed directly to resolve_type_with_arena
        };
        resolve_type_with_arena(ty, &mut ctx, &mut arena)
    }

    /// Resolve a type expression with an optional Self type for method signatures
    fn resolve_type_with_self(
        &mut self,
        ty: &TypeExpr,
        interner: &Interner,
        self_type: Option<LegacyType>,
    ) -> LegacyType {
        let module_id = self.current_module;
        // Convert self_type from LegacyType to TypeId
        let self_type_id = self_type
            .as_ref()
            .map(|t| self.type_arena.borrow_mut().from_type(t));
        let mut ctx = TypeResolutionContext {
            entity_registry: &self.entity_registry,
            interner,
            name_table: &mut self.name_table,
            module_id,
            // Propagate type param scope to nested contexts (lambdas, etc.)
            type_params: self.type_param_stack.current(),
            self_type: self_type_id,
            type_arena: Some(&*self.type_arena),
        };
        resolve_type(ty, &mut ctx)
    }

    /// Pass 0: Collect type aliases (so they're available for function signatures)
    fn collect_type_aliases(&mut self, program: &Program, interner: &Interner) {
        for decl in &program.declarations {
            if let Decl::Let(let_stmt) = decl {
                match &let_stmt.init {
                    LetInit::TypeAlias(type_expr) => {
                        let aliased_type = self.resolve_type(type_expr, interner);
                        self.register_type_alias(let_stmt.name, aliased_type, interner);
                    }
                    LetInit::Expr(init_expr) => {
                        // Legacy: handle let X: type = SomeType
                        if let ExprKind::TypeLiteral(type_expr) = &init_expr.kind {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
                        }
                    }
                }
            }
        }
    }

    /// Register a type alias in EntityRegistry
    fn register_type_alias(&mut self, name: Symbol, aliased_type: LegacyType, interner: &Interner) {
        // Lookup shell registered in register_all_type_shells
        let name_id = self
            .name_table
            .intern(self.current_module, &[name], interner);
        let type_id = self
            .entity_registry
            .type_by_name(name_id)
            .expect("alias shell registered in register_all_type_shells");
        let type_key = self.entity_registry.type_table.key_for_type(&aliased_type);
        // Convert to ArenaTypeId for storage
        let aliased_type_id = self.type_arena.borrow_mut().from_type(&aliased_type);
        self.entity_registry
            .set_aliased_type(type_id, aliased_type_id, type_key);
        // Also in type_table for display
        self.entity_registry
            .type_table
            .insert_named(aliased_type, name_id);
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
                        // Check for ambiguous type alias: let Alias = TypeName
                        if let ExprKind::Identifier(ident_sym) = &init_expr.kind {
                            let ident_name = interner.resolve(*ident_sym);
                            if self
                                .resolver(interner)
                                .resolve_type(*ident_sym, &self.entity_registry)
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

                        let declared_type =
                            let_stmt.ty.as_ref().map(|t| self.resolve_type(t, interner));
                        let init_type =
                            self.check_expr_expecting(init_expr, declared_type.as_ref(), interner)?;

                        // Check if trying to use void return value
                        if init_type == LegacyType::Void {
                            self.add_error(
                                SemanticError::VoidReturnUsed {
                                    span: init_expr.span.into(),
                                },
                                init_expr.span,
                            );
                        }

                        let var_type = declared_type.unwrap_or(init_type.clone());

                        // If this is a type alias (RHS is a type expression), store it
                        if var_type == LegacyType::MetaType
                            && let ExprKind::TypeLiteral(type_expr) = &init_expr.kind
                        {
                            let aliased_type = self.resolve_type(type_expr, interner);
                            self.register_type_alias(let_stmt.name, aliased_type, interner);
                        }

                        let var_type_id = self.type_arena.borrow_mut().from_type(&var_type);
                        self.globals.insert(let_stmt.name, var_type_id);
                        self.scope.define(
                            let_stmt.name,
                            Variable {
                                ty: var_type_id,
                                mutable: let_stmt.mutable,
                            },
                        );
                    }
                }
            }
        }
        Ok(())
    }

    /// Pass 2: LegacyType check function bodies, tests, and methods
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
                Decl::Let(_) => {
                    // Already processed in process_global_lets
                }
                Decl::Class(class) => {
                    // Set up type param scope for generic class methods
                    // This allows method resolution to use constraint interfaces
                    if !class.type_params.is_empty()
                        && let Some(class_name_id) =
                            self.name_table
                                .name_id(self.current_module, &[class.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(class_name_id)
                        && let Some(generic_info) =
                            self.entity_registry.get_generic_info(type_def_id)
                    {
                        let mut scope = TypeParamScope::new();
                        for tp in &generic_info.type_params {
                            scope.add(tp.clone());
                        }
                        self.type_param_stack.push_scope(scope);
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
                    if !class.type_params.is_empty() {
                        self.type_param_stack.pop();
                    }
                    // Validate interface satisfaction via EntityRegistry
                    if let Some(class_name_id) =
                        self.name_table
                            .name_id(self.current_module, &[class.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(class_name_id)
                    {
                        let type_methods = self.get_type_method_signatures(class.name, interner);
                        for interface_id in
                            self.entity_registry.get_implemented_interfaces(type_def_id)
                        {
                            let interface_def = self.entity_registry.get_type(interface_id);
                            if let Some(iface_name_str) =
                                self.name_table.last_segment_str(interface_def.name_id)
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
                    if !record.type_params.is_empty()
                        && let Some(record_name_id) =
                            self.name_table
                                .name_id(self.current_module, &[record.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(record_name_id)
                        && let Some(generic_info) =
                            self.entity_registry.get_generic_info(type_def_id)
                    {
                        let mut scope = TypeParamScope::new();
                        for tp in &generic_info.type_params {
                            scope.add(tp.clone());
                        }
                        self.type_param_stack.push_scope(scope);
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
                    if let Some(record_name_id) =
                        self.name_table
                            .name_id(self.current_module, &[record.name], interner)
                        && let Some(type_def_id) = self.entity_registry.type_by_name(record_name_id)
                    {
                        let type_methods = self.get_type_method_signatures(record.name, interner);
                        for interface_id in
                            self.entity_registry.get_implemented_interfaces(type_def_id)
                        {
                            let interface_def = self.entity_registry.get_type(interface_id);
                            if let Some(iface_name_str) =
                                self.name_table.last_segment_str(interface_def.name_id)
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
                                let name_id = self.name_table.primitives.from_ast(*prim);
                                if let Some(type_def_id) =
                                    self.entity_registry.type_by_name(name_id)
                                {
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
        let mut fields = Vec::new();

        for (slot, field) in decl.fields.iter().enumerate() {
            let module_id = self.current_module;
            let mut ctx = TypeResolutionContext {
                entity_registry: &self.entity_registry,
                interner,
                name_table: &mut self.name_table,
                module_id,
                type_params: None,
                self_type: None,
                type_arena: Some(&*self.type_arena),
            };
            let ty = resolve_type(&field.ty, &mut ctx);

            fields.push(StructField {
                name: interner.resolve(field.name).to_string(),
                ty,
                slot,
            });
        }

        let name_id = self
            .name_table
            .intern(self.current_module, &[decl.name], interner);

        // Register in EntityRegistry first to get TypeDefId
        let entity_type_id = self.entity_registry.register_type(
            name_id,
            TypeDefKind::ErrorType,
            self.current_module,
        );

        let error_info = ErrorTypeInfo {
            type_def_id: entity_type_id,
        };

        self.register_named_type(
            decl.name,
            LegacyType::Nominal(NominalType::Error(error_info.clone())),
            interner,
        );

        // Set error info for lookup
        self.entity_registry
            .set_error_info(entity_type_id, error_info);

        // Register fields in EntityRegistry
        let builtin_module = self.name_table.builtin_module();
        let type_name_str = interner.resolve(decl.name);
        for (i, field) in decl.fields.iter().enumerate() {
            let field_name_str = interner.resolve(field.name);
            let field_name_id = self
                .name_table
                .intern_raw(builtin_module, &[field_name_str]);
            let full_field_name_id = self
                .name_table
                .intern_raw(self.current_module, &[type_name_str, field_name_str]);
            let field_ty = fields[i].ty.clone();
            // Convert to ArenaTypeId for storage
            let field_type_id = self.type_arena.borrow_mut().from_type(&field_ty);
            self.entity_registry.register_field(
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
    ) -> Option<crate::sema::generic::TypeConstraint> {
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
                        .resolve_type(sym, &self.entity_registry)
                    {
                        let type_def = self.entity_registry.get_type(type_def_id);
                        if type_def.kind == TypeDefKind::Alias
                            && let Some(aliased_type_id) = type_def.aliased_type
                        {
                            // Convert TypeId to LegacyType for pattern matching
                            let aliased_type = self.type_arena.borrow().to_type(aliased_type_id);
                            // Convert the aliased type to a union constraint
                            let types = match &aliased_type {
                                LegacyType::Union(types) => types.to_vec(),
                                other => vec![other.clone()],
                            };
                            return Some(crate::sema::generic::TypeConstraint::Union(types));
                        }
                    }
                }

                // Validate all interfaces exist via EntityRegistry using resolver
                for sym in syms {
                    let iface_str = interner.resolve(*sym);
                    let iface_exists = self
                        .resolver(interner)
                        .resolve_type_str_or_interface(iface_str, &self.entity_registry)
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
                Some(crate::sema::generic::TypeConstraint::Interface(
                    syms.clone(),
                ))
            }
            TypeConstraint::Union(types) => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    type_param_scope,
                    &self.type_arena,
                );
                let resolved = types.iter().map(|ty| resolve_type(ty, &mut ctx)).collect();
                Some(crate::sema::generic::TypeConstraint::Union(resolved))
            }
            TypeConstraint::Structural { fields, methods } => {
                let module_id = self.current_module;
                let mut ctx = TypeResolutionContext::with_type_params_and_arena(
                    &self.entity_registry,
                    interner,
                    &mut self.name_table,
                    module_id,
                    type_param_scope,
                    &self.type_arena,
                );
                // Convert AST structural to sema structural
                let resolved_fields = fields
                    .iter()
                    .map(|f| crate::sema::types::StructuralFieldType {
                        name: ctx
                            .name_table
                            .intern(ctx.module_id, &[f.name], ctx.interner),
                        ty: resolve_type(&f.ty, &mut ctx),
                    })
                    .collect();
                let resolved_methods = methods
                    .iter()
                    .map(|m| crate::sema::types::StructuralMethodType {
                        name: ctx
                            .name_table
                            .intern(ctx.module_id, &[m.name], ctx.interner),
                        params: m.params.iter().map(|p| resolve_type(p, &mut ctx)).collect(),
                        return_type: resolve_type(&m.return_type, &mut ctx),
                    })
                    .collect();
                Some(crate::sema::generic::TypeConstraint::Structural(
                    StructuralType {
                        fields: resolved_fields,
                        methods: resolved_methods,
                    },
                ))
            }
        }
    }

    fn check_type_param_constraints(
        &mut self,
        type_params: &[TypeParamInfo],
        inferred: &HashMap<NameId, LegacyType>,
        span: Span,
        interner: &Interner,
    ) {
        for param in type_params {
            let Some(constraint) = &param.constraint else {
                continue;
            };
            let Some(found) = inferred.get(&param.name_id) else {
                continue;
            };

            // If the inferred type is itself a type param that has a matching or stronger constraint,
            // the constraint is satisfied. Check if it's a type param in our current scope.
            let found_param = match found {
                LegacyType::TypeParam(found_name_id) => {
                    self.type_param_stack.get_by_name_id(*found_name_id)
                }
                LegacyType::TypeParamRef(type_param_id) => {
                    self.type_param_stack.get_by_type_param_id(*type_param_id)
                }
                _ => None,
            };
            if let Some(found_param) = found_param
                && constraint_satisfied(&found_param.constraint, constraint)
            {
                continue; // Constraint is satisfied
            }

            match constraint {
                crate::sema::generic::TypeConstraint::Interface(interface_names) => {
                    // Must satisfy all interfaces in the constraint
                    for interface_name in interface_names {
                        if !self.satisfies_interface(found, *interface_name, interner) {
                            let found_display = self.type_display(found);
                            self.add_error(
                                SemanticError::TypeParamConstraintMismatch {
                                    type_param: interner.resolve(param.name).to_string(),
                                    expected: interner.resolve(*interface_name).to_string(),
                                    found: found_display,
                                    span: span.into(),
                                },
                                span,
                            );
                        }
                    }
                }
                crate::sema::generic::TypeConstraint::Union(variants) => {
                    let expected = LegacyType::normalize_union(variants.clone());
                    if !found.is_compatible(&expected) {
                        let expected_display = self.type_display(&expected);
                        let found_display = self.type_display(found);
                        self.add_error(
                            SemanticError::TypeParamConstraintMismatch {
                                type_param: interner.resolve(param.name).to_string(),
                                expected: expected_display,
                                found: found_display,
                                span: span.into(),
                            },
                            span,
                        );
                    }
                }
                crate::sema::generic::TypeConstraint::Structural(structural) => {
                    if let Some(mismatch) =
                        self.check_structural_constraint(found, structural, interner)
                    {
                        let found_display = self.type_display(found);
                        self.add_error(
                            SemanticError::StructuralConstraintMismatch {
                                type_param: interner.resolve(param.name).to_string(),
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

    /// Analyze external block and register external methods in the implement registry
    fn analyze_external_block(
        &mut self,
        external: &ExternalBlock,
        target_type: &LegacyType,
        trait_name: Option<Symbol>,
        interner: &Interner,
    ) {
        let type_id = match ImplTypeId::from_type(
            target_type,
            &self.entity_registry.type_table,
            &self.entity_registry,
        ) {
            Some(id) => id,
            None => return, // Skip non-registerable types
        };

        // Get EntityRegistry TypeDefId for the target type
        let entity_type_id = target_type.type_def_id().or_else(|| {
            self.name_table
                .primitives
                .name_id_for_type(target_type)
                .and_then(|name_id| self.entity_registry.type_by_name(name_id))
        });

        // Get interface TypeDefId if implementing an interface
        let interface_type_id = trait_name.and_then(|name| {
            let iface_str = interner.resolve(name);
            self.resolver(interner)
                .resolve_type_str_or_interface(iface_str, &self.entity_registry)
        });

        for func in &external.functions {
            // Resolve parameter types
            let param_types: Vec<LegacyType> = func
                .params
                .iter()
                .map(|p| self.resolve_type(&p.ty, interner))
                .collect();

            // Resolve return type
            let return_type = match &func.return_type {
                Some(te) => self.resolve_type(te, interner),
                None => LegacyType::Void,
            };

            let func_type = FunctionType {
                params: param_types.into(),
                return_type: Box::new(return_type),
                is_closure: false,
                params_id: None,
                return_type_id: None,
            };

            // Determine native name: explicit or default to vole_name
            let native_name = func
                .native_name
                .clone()
                .unwrap_or_else(|| interner.resolve(func.vole_name).to_string());

            // Register in implement registry
            let method_id = self.method_name_id(func.vole_name, interner);
            let return_type_clone = (*func_type.return_type).clone();
            let external_info = ExternalMethodInfo {
                module_path: external.module_path.clone(),
                native_name,
                return_type: Some(Box::new(return_type_clone)),
            };
            self.implement_registry.register_method(
                type_id,
                method_id,
                MethodImpl {
                    trait_name,
                    func_type: func_type.clone(),
                    is_builtin: false,
                    external_info: Some(external_info.clone()),
                },
            );

            // Register in EntityRegistry for method resolution
            if let Some(entity_type_id) = entity_type_id {
                use crate::sema::entity_defs::MethodBinding;
                // For trait implementations, use the interface type id
                // For type extensions, use the type's own id as both
                let binding_type_id = interface_type_id.unwrap_or(entity_type_id);
                self.entity_registry.add_method_binding(
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
    /// Automatically sets return/error/generator types from return_type.
    /// For static methods, caller should set static_method and push type params after calling.
    fn enter_function_context(
        &mut self,
        return_type: &LegacyType,
        _interner: &Interner,
    ) -> FunctionCheckContext {
        let saved = FunctionCheckContext {
            return_type: self.current_function_return.take(),
            error_type: self.current_function_error_type.take(),
            generator_element_type: self.current_generator_element_type.take(),
            static_method: self.current_static_method.take(),
            type_param_stack_depth: self.type_param_stack.depth(),
        };

        // Convert LegacyType to ArenaTypeId for storage
        let return_type_id = self.type_arena.borrow_mut().from_type(return_type);
        self.current_function_return = Some(return_type_id);

        // Set error type context if this is a fallible function
        if let LegacyType::Fallible(ft) = return_type {
            let error_type_id = self.type_arena.borrow_mut().from_type(&ft.error_type);
            self.current_function_error_type = Some(error_type_id);
        }

        // Set generator context if return type is Iterator<T>
        if let Some(element_type_id) = self.extract_iterator_element_type_id(return_type_id) {
            self.current_generator_element_type = Some(element_type_id);
        }

        saved
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

    fn check_function(
        &mut self,
        func: &FuncDecl,
        interner: &Interner,
    ) -> Result<(), Vec<TypeError>> {
        // Skip generic functions - they will be type-checked when monomorphized
        // TODO: In M4+, we could type-check with abstract type params
        if !func.type_params.is_empty() {
            return Ok(());
        }

        let func_type = self
            .functions
            .get(&func.name)
            .cloned()
            .expect("function registered in signature collection pass");
        let return_type = *func_type.return_type.clone();
        let saved_ctx = self.enter_function_context(&return_type, interner);

        // Create new scope with parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        for (param, ty) in func.params.iter().zip(func_type.params.iter()) {
            let ty_id = self.type_arena.borrow_mut().from_type(ty);
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(&func.body, interner)?;

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
    }

    /// Extract the element type from an Iterator<T> type using TypeId (avoids LegacyType)
    fn extract_iterator_element_type_id(&self, ty_id: ArenaTypeId) -> Option<ArenaTypeId> {
        let interface_info = {
            let arena = self.type_arena.borrow();
            arena
                .unwrap_interface(ty_id)
                .map(|(id, args)| (id, args.first().copied()))
        };
        let (type_def_id, first_arg) = interface_info?;
        if !self.name_table.well_known.is_iterator_type_def(type_def_id) {
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
            .resolve_type(type_name, &self.entity_registry)
            .expect("type should be registered in EntityRegistry");
        let lookup = self
            .lookup_method(type_def_id, method.name, interner)
            .expect("method should be registered in EntityRegistry");
        let return_type = (*lookup.signature.return_type).clone();
        let saved_ctx = self.enter_function_context(&return_type, interner);

        // Create scope with 'self' and parameters
        let parent_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(parent_scope);

        // Add 'self' to scope
        // Note: "self" should already be interned by the parser when it parses method bodies
        let self_sym = interner
            .lookup("self")
            .expect("'self' should be interned during parsing");
        // Get self type via EntityRegistry
        let type_def = self.entity_registry.get_type(type_def_id);
        let self_type = match type_def.kind {
            TypeDefKind::Class => self
                .entity_registry
                .build_class_type(type_def_id)
                .map(|c| LegacyType::Nominal(NominalType::Class(c)))
                .unwrap_or_else(|| LegacyType::invalid("unwrap_failed")),
            TypeDefKind::Record => self
                .entity_registry
                .build_record_type(type_def_id)
                .map(|r| LegacyType::Nominal(NominalType::Record(r)))
                .unwrap_or_else(|| LegacyType::invalid("unwrap_failed")),
            _ => LegacyType::invalid("fallback"),
        };
        let self_type_id = self.type_arena.borrow_mut().from_type(&self_type);
        self.scope.define(
            self_sym,
            Variable {
                ty: self_type_id,
                mutable: false,
            },
        );

        // Add parameters
        for (param, ty) in method.params.iter().zip(lookup.signature.params.iter()) {
            let ty_id = self.type_arena.borrow_mut().from_type(ty);
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(&method.body, interner)?;

        // Restore scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }
        self.exit_function_context(saved_ctx);

        Ok(())
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
            .resolve_type(type_name, &self.entity_registry)
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
            .entity_registry
            .find_static_method_on_type(type_def_id, method_name_id)
            .expect("static method should be registered in EntityRegistry");
        let method_def = self.entity_registry.get_method(method_id);
        let method_type = method_def.signature.clone();
        let method_type_params = method_def.method_type_params.clone();
        let return_type = *method_type.return_type.clone();
        let saved_ctx = self.enter_function_context(&return_type, interner);

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
        for (param, ty) in method.params.iter().zip(method_type.params.iter()) {
            let ty_id = self.type_arena.borrow_mut().from_type(ty);
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
        }

        // Check body
        self.check_block(body, interner)?;

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
        for test_case in &tests_decl.tests {
            // Each test gets its own scope
            let parent_scope = std::mem::take(&mut self.scope);
            self.scope = Scope::with_parent(parent_scope);

            // Tests implicitly return void
            let saved_ctx = self.enter_function_context(&LegacyType::Void, interner);

            // Type check all statements in the test body
            self.check_block(&test_case.body, interner)?;

            // Restore scope
            if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
                self.scope = parent;
            }
            self.exit_function_context(saved_ctx);
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

    /// Analyze an imported module and return its type
    #[allow(clippy::result_unit_err)] // Error is added to self.errors vector
    #[tracing::instrument(skip(self, span, _interner), fields(path = %import_path))]
    pub fn analyze_module(
        &mut self,
        import_path: &str,
        span: Span,
        _interner: &Interner,
    ) -> Result<LegacyType, ()> {
        // Check cache first
        if let Some(module_type) = self.module_types.get(import_path) {
            return Ok(LegacyType::Module(module_type.clone()));
        }

        // Load the module
        let module_info = match self.module_loader.load(import_path) {
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
        };

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
        let mut exports = HashMap::new();
        let mut constants = HashMap::new();
        let mut external_funcs = HashSet::new();
        let module_interner = parser.into_interner();

        let module_id = self.name_table.module_id(import_path);

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    // Build function type from signature
                    let (params, return_type) = {
                        let mut ctx = TypeResolutionContext {
                            entity_registry: &self.entity_registry,
                            interner: &module_interner,
                            name_table: &mut self.name_table,
                            module_id,
                            type_params: None,
                            self_type: None,
                            type_arena: Some(&*self.type_arena),
                        };
                        let params: Vec<LegacyType> = f
                            .params
                            .iter()
                            .map(|p| resolve_type(&p.ty, &mut ctx))
                            .collect();
                        let return_type = f
                            .return_type
                            .as_ref()
                            .map(|rt| resolve_type(rt, &mut ctx))
                            .unwrap_or(LegacyType::Void);
                        (params, return_type)
                    };

                    let func_type = LegacyType::Function(FunctionType {
                        params: params.into(),
                        return_type: Box::new(return_type),
                        is_closure: false,
                        params_id: None,
                        return_type_id: None,
                    });

                    // Store export by name string
                    let name_id = self
                        .name_table
                        .intern(module_id, &[f.name], &module_interner);
                    exports.insert(name_id, func_type);
                }
                Decl::Let(l) if !l.mutable => {
                    // Only export immutable let bindings (skip type aliases for now)
                    let init_expr = match &l.init {
                        LetInit::Expr(e) => e,
                        LetInit::TypeAlias(_) => continue, // Type aliases handled separately
                    };
                    // Infer type from literal for constants and store the value
                    let name_id = self
                        .name_table
                        .intern(module_id, &[l.name], &module_interner);
                    let (ty, const_val) = match &init_expr.kind {
                        ExprKind::FloatLiteral(v) => (
                            LegacyType::Primitive(PrimitiveType::F64),
                            Some(ConstantValue::F64(*v)),
                        ),
                        ExprKind::IntLiteral(v) => (
                            LegacyType::Primitive(PrimitiveType::I64),
                            Some(ConstantValue::I64(*v)),
                        ),
                        ExprKind::BoolLiteral(v) => (
                            LegacyType::Primitive(PrimitiveType::Bool),
                            Some(ConstantValue::Bool(*v)),
                        ),
                        ExprKind::StringLiteral(v) => (
                            LegacyType::Primitive(PrimitiveType::String),
                            Some(ConstantValue::String(v.clone())),
                        ),
                        _ => (LegacyType::unknown(), None), // Complex expressions need full analysis
                    };
                    exports.insert(name_id, ty);
                    if let Some(cv) = const_val {
                        constants.insert(name_id, cv);
                    }
                }
                Decl::External(ext) => {
                    // External block functions become exports and are marked as external
                    for func in &ext.functions {
                        let (params, return_type) = {
                            let mut ctx = TypeResolutionContext {
                                entity_registry: &self.entity_registry,
                                interner: &module_interner,
                                name_table: &mut self.name_table,
                                module_id,
                                type_params: None,
                                self_type: None,
                                type_arena: Some(&*self.type_arena),
                            };
                            let params: Vec<LegacyType> = func
                                .params
                                .iter()
                                .map(|p| resolve_type(&p.ty, &mut ctx))
                                .collect();
                            let return_type = func
                                .return_type
                                .as_ref()
                                .map(|rt| resolve_type(rt, &mut ctx))
                                .unwrap_or(LegacyType::Void);
                            (params, return_type)
                        };

                        let func_type = LegacyType::Function(FunctionType {
                            params: params.into(),
                            return_type: Box::new(return_type),
                            is_closure: false,
                            params_id: None,
                            return_type_id: None,
                        });

                        let name_id =
                            self.name_table
                                .intern(module_id, &[func.vole_name], &module_interner);
                        exports.insert(name_id, func_type);
                        // Mark as external function (FFI)
                        external_funcs.insert(name_id);
                    }
                }
                _ => {} // Skip other declarations for now
            }
        }

        let module_type = ModuleType {
            module_id,
            exports,
            constants,
            external_funcs,
        };

        self.module_types
            .insert(import_path.to_string(), module_type.clone());

        // Store the program and interner for compiling pure Vole functions
        self.module_programs
            .insert(import_path.to_string(), (program, module_interner));

        Ok(LegacyType::Module(module_type))
    }
}

// Note: Default is not implemented because Analyzer requires file and source parameters

#[cfg(test)]
mod tests;

// src/sema/analyzer/mod.rs

mod builtins;
mod context;
mod declarations;
mod errors;
mod expr;
mod functions;
mod inference;
mod lambda;
mod methods;
mod module;
mod output;
mod patterns;
mod prelude;
mod state;
mod stmt;
mod test_checking;
mod type_constraints;
mod type_helpers;
mod type_resolution;

use type_constraints::validate_defaults;

use crate::analysis_cache::IsCheckResult;
use crate::entity_defs::{GenericFuncInfo, TypeDefKind};
use crate::entity_registry::{EntityRegistry, MethodDefBuilder};
use crate::errors::{SemanticError, SemanticWarning, unknown_type_hint};
use crate::generic::{
    ClassMethodMonomorphKey, MonomorphInstance, MonomorphKey, StaticMethodMonomorphKey,
    TypeParamInfo, TypeParamScope, TypeParamVariance,
};
use crate::implement_registry::{
    ExternalMethodInfo, GenericExternalInfo, ImplTypeId, ImplementRegistry, MethodImpl,
    TypeMappingEntry,
};
use crate::resolution::ResolvedMethod;
use crate::resolve::resolve_type_to_id;
use crate::type_arena::{TypeArena, TypeId as ArenaTypeId};
use crate::types::ConstantValue;
use crate::{
    ErrorTypeInfo, FunctionType, PrimitiveType,
    resolve::TypeResolutionContext,
    scope::{Scope, Variable},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;
use vole_frontend::ast::*;
use vole_frontend::{Interner, Parser, Span};
use vole_identity::{self, MethodId, ModuleId, NameId, NameTable, Namer, TypeDefId};

pub(crate) use context::{AnalyzerContext, ResolverGuard};
pub(crate) use output::MethodLookup;
pub use output::{AnalysisOutput, AnalyzerBuilder, TypeError, TypeWarning};
pub(super) use output::{AnalysisResults, SymbolTables};
pub(crate) use state::ReturnInfo;
pub(super) use state::{CaptureInfo, Diagnostics, LambdaState, ModuleContext, TypeCheckEnv};

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

    /// Take accumulated warnings, leaving the warnings list empty
    pub fn take_warnings(&mut self) -> Vec<TypeWarning> {
        std::mem::take(&mut self.diagnostics.warnings)
    }

    /// Take ownership of analysis results (consuming self)
    pub fn into_analysis_results(self) -> AnalysisOutput {
        let mut node_map = self.results.node_map;
        let tests_virtual_modules = self.results.tests_virtual_modules;
        let current_module = self.module.current_module;

        // Try to take ownership of the shared context to avoid cloning AST trees.
        // By this point all sub-analyzers should be dropped, so Rc strong count is 1.
        let (merged_node_map, module_programs, db, modules_with_errors) =
            match Rc::try_unwrap(self.ctx) {
                Ok(ctx) => {
                    let errored = ctx.modules_with_errors.into_inner();
                    (
                        ctx.merged_node_map.into_inner(),
                        ctx.module_programs.into_inner(),
                        ctx.db,
                        errored,
                    )
                }
                Err(ctx) => {
                    let errored = ctx.modules_with_errors.borrow().clone();
                    (
                        ctx.merged_node_map.borrow().clone(),
                        ctx.module_programs.borrow().clone(),
                        Rc::clone(&ctx.db),
                        errored,
                    )
                }
            };

        // Merge sub-analyzer NodeMap data into the main-program NodeMap.
        node_map.merge(merged_node_map);

        AnalysisOutput {
            node_map,
            tests_virtual_modules,
            module_programs,
            db,
            module_id: current_module,
            modules_with_errors: modules_with_errors.into_iter().collect(),
        }
    }

    /// Record the resolved type for an expression using TypeId directly.
    /// Also pre-creates RuntimeIterator types for Iterator<T> return types,
    /// so codegen can look them up without needing mutable arena access.
    fn record_expr_type_id(&mut self, expr: &Expr, type_id: ArenaTypeId) -> ArenaTypeId {
        // Pre-create RuntimeIterator(T) for Iterator<T> types so codegen can look them up
        self.ensure_runtime_iterator_for_iterator(type_id);
        self.results.node_map.set_type(expr.id, type_id);
        type_id
    }

    /// Record the result of a type check (is expression or type pattern) for codegen.
    fn record_is_check_result(&mut self, node_id: NodeId, result: IsCheckResult) {
        self.results.node_map.set_is_check_result(node_id, result);
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
        // Fast path: check well-known cached TypeDefIds before full resolution
        let type_def_id = self.lookup_well_known_interface(name).or_else(|| {
            self.resolver(interner)
                .resolve_type_str_or_interface(name, &self.entity_registry())
        })?;
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

        // Cache well-known interface TypeDefIds for fast lookup during body checking.
        // Uses the resolver (which includes short_name fallback) to get the exact same
        // TypeDefIds that resolve_type_str_or_interface would return.
        self.populate_well_known_cache(interner);

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

    /// Extract the element type from a direct Iterator<T> interface type.
    ///
    /// Returns `Some(T)` if the type IS an `Iterator<T>` interface, `None` otherwise.
    /// Does NOT check class/struct implementations — use
    /// `extract_custom_iterator_element_type_id` for that.
    fn extract_iterator_interface_element_type_id(
        &self,
        ty_id: ArenaTypeId,
    ) -> Option<ArenaTypeId> {
        let interface_info = {
            let arena = self.type_arena();
            arena
                .unwrap_interface(ty_id)
                .map(|(id, args)| (id, args.first().copied()))
        };
        if let Some((type_def_id, first_arg)) = interface_info
            && self
                .name_table()
                .well_known
                .is_iterator_type_def(type_def_id)
        {
            return first_arg;
        }
        None
    }

    /// Extract the element type from a class/struct implementing Iterator<T>.
    ///
    /// Returns `Some(T)` if the type is a class/struct with
    /// `extend ... with Iterator<T>`, `None` otherwise.
    fn extract_custom_iterator_element_type_id(&self, ty_id: ArenaTypeId) -> Option<ArenaTypeId> {
        let type_def_id = {
            let arena = self.type_arena();
            arena.unwrap_class_or_struct(ty_id).map(|(id, _, _)| id)
        }?;
        let well_known = &self.name_table().well_known;
        let iterator_id = well_known.iterator_type_def?;
        let registry = self.entity_registry();
        let implemented = registry.get_implemented_interfaces(type_def_id);
        if !implemented.contains(&iterator_id) {
            return None;
        }
        let type_args = registry.get_implementation_type_args(type_def_id, iterator_id);
        type_args.first().copied()
    }

    /// Extract the element type from an Iterator<T> type.
    ///
    /// Handles both direct Iterator<T> interface types and class/struct types
    /// that implement Iterator<T> via `extend ... with Iterator<T>`.
    fn extract_iterator_element_type_id(&self, ty_id: ArenaTypeId) -> Option<ArenaTypeId> {
        self.extract_iterator_interface_element_type_id(ty_id)
            .or_else(|| self.extract_custom_iterator_element_type_id(ty_id))
    }

    /// Extract the element type T from a type that implements Iterable<T>.
    ///
    /// This checks if the given type is a class/struct that has an `extend ... with Iterable<T>`
    /// implementation, and if so returns the concrete element type T.
    fn extract_iterable_element_type_id(&self, ty_id: ArenaTypeId) -> Option<ArenaTypeId> {
        let type_def_id = {
            let arena = self.type_arena();
            arena.unwrap_class_or_struct(ty_id).map(|(id, _, _)| id)
        }?;
        let well_known = &self.name_table().well_known;
        let iterable_id = well_known.iterable_type_def?;
        let registry = self.entity_registry();
        let implemented = registry.get_implemented_interfaces(type_def_id);
        if !implemented.contains(&iterable_id) {
            return None;
        }
        let type_args = registry.get_implementation_type_args(type_def_id, iterable_id);
        type_args.first().copied()
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

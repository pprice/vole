// src/sema/analyzer/module.rs
//! Module-level analysis: loading, parsing, and analyzing imported modules.

use super::*;
use crate::entity_defs::MethodBinding;
use crate::optimizer::constant_folding::eval_const_expr;

/// RAII guard that removes a canonical path from the modules_in_progress set on drop.
/// Replaces the `bail_module!` macro so extracted helper functions don't need the macro.
struct ModuleInProgressGuard {
    ctx: Rc<AnalyzerContext>,
    /// None after `defuse()` — the Drop impl skips removal when this is None.
    canonical_path: Option<String>,
}

impl ModuleInProgressGuard {
    fn new(ctx: &Rc<AnalyzerContext>, canonical_path: String) -> Self {
        ctx.modules_in_progress
            .borrow_mut()
            .insert(canonical_path.clone());
        Self {
            ctx: Rc::clone(ctx),
            canonical_path: Some(canonical_path),
        }
    }

    /// Disarm the guard so it won't remove the path from in-progress on drop,
    /// while still dropping the `Rc<AnalyzerContext>` normally.
    ///
    /// Previously this used `mem::forget`, which leaked the Rc reference count
    /// and caused `Rc::try_unwrap` in `into_analysis_results` to always fail,
    /// falling back to an expensive clone of all module AST trees.
    fn defuse(&mut self) {
        self.canonical_path = None;
    }
}

impl Drop for ModuleInProgressGuard {
    fn drop(&mut self) {
        if let Some(ref canonical_path) = self.canonical_path {
            self.ctx
                .modules_in_progress
                .borrow_mut()
                .remove(canonical_path);
        }
    }
}

/// Collected declarations from a module, ready for type resolution after sub-analysis.
struct ModuleDeclarations<'a> {
    exports: FxHashMap<NameId, ArenaTypeId>,
    constants: FxHashMap<NameId, ConstantValue>,
    external_funcs: FxHashSet<NameId>,
    type_names: ModuleTypeNames,
    deferred_functions: Vec<(NameId, &'a FuncDecl)>,
    deferred_externals: Vec<(NameId, &'a ExternalFunc)>,
    deferred_generic_externals: Vec<(NameId, &'a ExternalFunc)>,
}

/// Named type declarations collected from a module for post-analysis export resolution.
#[derive(Default)]
struct ModuleTypeNames {
    interfaces: Vec<(NameId, Symbol)>,
    structs: Vec<(NameId, Symbol)>,
    classes: Vec<(NameId, Symbol)>,
    errors: Vec<(NameId, Symbol)>,
    sentinels: Vec<(NameId, Symbol)>,
}

/// Parsed and transformed module, ready for analysis.
struct ParsedModule {
    program: Program,
    interner: Interner,
    file_path: PathBuf,
}

/// Data needed to finalize a module: create the module type and store in context.
struct ModuleFinalization {
    program: Program,
    interner: Interner,
    exports: FxHashMap<NameId, ArenaTypeId>,
    constants: FxHashMap<NameId, ConstantValue>,
    external_funcs: FxHashSet<NameId>,
}

impl Analyzer {
    /// Process module imports early so they're available for qualified implement syntax.
    /// This runs before signature collection to allow `implement mod.Interface for Type`.
    pub(super) fn process_module_imports(&mut self, program: &Program, interner: &Interner) {
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
                    self.env.scope.define(
                        let_stmt.name,
                        Variable {
                            ty: module_type_id,
                            mutable: false,
                            declaration_span: let_stmt.span,
                        },
                    );
                    // Also register in globals for consistency
                    self.symbols.globals.insert(let_stmt.name, module_type_id);
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

    /// Analyze external block and register external methods in the implement registry
    pub(super) fn analyze_external_block(
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
            let method_impl = MethodImpl::external(func_type.clone(), external_info);
            let method_impl = match trait_name {
                Some(name) => method_impl.with_trait_name(name),
                None => method_impl,
            };
            self.implement_registry_mut()
                .register_method(impl_type_id, method_id, method_impl);

            // Register in EntityRegistry for method resolution
            if let Some(entity_type_id) = entity_type_id {
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

    #[expect(clippy::result_unit_err)] // Error is added to self.diagnostics.errors vector
    #[tracing::instrument(skip(self, span, _interner), fields(path = %import_path))]
    pub fn analyze_module(
        &mut self,
        import_path: &str,
        span: Span,
        _interner: &Interner,
    ) -> Result<ArenaTypeId, ()> {
        // Phase 1: Resolve path and check cache
        let canonical_path = self.resolve_module_path(import_path, span)?;

        // Check cache with canonical path
        let cached_type_id = self
            .ctx
            .module_type_ids
            .borrow()
            .get(&canonical_path)
            .copied();
        if let Some(type_id) = cached_type_id {
            tracing::debug!(import_path, %canonical_path, "analyze_module: cache HIT");
            return Ok(type_id);
        }
        tracing::debug!(import_path, %canonical_path, "analyze_module: cache MISS");

        // Phase 2: Circular import detection + RAII guard for in-progress tracking
        if self
            .ctx
            .modules_in_progress
            .borrow()
            .contains(&canonical_path)
        {
            self.add_error(
                SemanticError::CircularImport {
                    path: import_path.to_string(),
                    span: span.into(),
                },
                span,
            );
            return Err(());
        }
        let mut guard = ModuleInProgressGuard::new(&self.ctx, canonical_path.clone());

        // Compute module key and module_id before parsing so Parser gets the right ModuleId.
        let module_key = if import_path.starts_with("std:") {
            import_path.to_string()
        } else {
            canonical_path.clone()
        };
        tracing::debug!(import_path, %module_key, "analyze_module: creating module_id");
        let module_id = self.name_table_mut().module_id(&module_key);

        // Phase 3: Load, parse, and transform the module
        let parsed = self.load_and_parse_module(import_path, span, module_id)?;

        // Destructure ParsedModule so file_path can be moved independently
        let ParsedModule {
            program: module_program,
            interner: module_interner,
            file_path: module_file_path,
        } = parsed;

        // Phase 4: Collect declarations from the parsed module
        let decls = self.collect_module_declarations(&module_program, &module_interner, module_id);

        // Phase 5a: Run sub-analysis
        let mut sub_analyzer = self.fork_for_module(module_id, Some(module_file_path));
        let analyze_result = sub_analyzer.analyze(&module_program, &module_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "module analysis errors");
            for err in errors {
                if matches!(err.error, SemanticError::CircularImport { .. }) {
                    self.diagnostics.errors.push(err.clone());
                }
            }
            // Track this module as having errors so codegen can skip its function bodies.
            self.ctx
                .modules_with_errors
                .borrow_mut()
                .insert(module_key.clone());
        }
        self.store_sub_analyzer_results(&module_key, sub_analyzer);

        // Destructure decls: deferred items borrow the program and must be consumed
        // before we can move module_program into finalize_module.
        let ModuleDeclarations {
            mut exports,
            constants,
            mut external_funcs,
            type_names,
            deferred_functions,
            deferred_externals,
            deferred_generic_externals,
        } = decls;

        // Phases 5b-5d: Resolve deferred function/external types (consumes program borrows)
        for (name_id, f) in deferred_functions {
            let type_id = self.resolve_func_type(
                &f.params,
                f.return_type.as_ref(),
                &module_interner,
                module_id,
            );
            exports.insert(name_id, type_id);
        }
        for (name_id, func) in deferred_externals {
            let type_id = self.resolve_func_type(
                &func.params,
                func.return_type.as_ref(),
                &module_interner,
                module_id,
            );
            exports.insert(name_id, type_id);
            external_funcs.insert(name_id);
        }
        for (name_id, func) in deferred_generic_externals {
            self.resolve_generic_external(name_id, func, &mut exports, &module_interner, module_id);
        }

        // Phase 5e: Populate type exports after sub-analysis
        self.populate_type_exports(&mut exports, &type_names, &module_interner, module_id);

        // Phases 5f-5h: Store program, create module type, cache
        let finalization = ModuleFinalization {
            program: module_program,
            interner: module_interner,
            exports,
            constants,
            external_funcs,
        };
        let type_id = self.finalize_module(finalization, &module_key, module_id, import_path);

        // Success: remove from in-progress explicitly, then cache
        guard.defuse();
        self.ctx
            .modules_in_progress
            .borrow_mut()
            .remove(&canonical_path);
        self.ctx
            .module_type_ids
            .borrow_mut()
            .insert(canonical_path, type_id);

        Ok(type_id)
    }

    /// Phase 1: Resolve the import path and canonicalize it for use as a cache key.
    fn resolve_module_path(&mut self, import_path: &str, span: Span) -> Result<String, ()> {
        match self
            .module
            .module_loader
            .resolve_path(import_path, self.module.current_file_path.as_deref())
        {
            Ok(path) => {
                // Canonicalize to ensure consistent cache keys (resolves `..` components)
                Ok(path
                    .canonicalize()
                    .unwrap_or(path)
                    .to_string_lossy()
                    .to_string())
            }
            Err(e) => {
                self.add_error(
                    SemanticError::ModuleNotFound {
                        path: import_path.to_string(),
                        message: e.to_string(),
                        span: span.into(),
                    },
                    span,
                );
                Err(())
            }
        }
    }

    /// Phase 3: Load the module file, parse it, and run generator transforms.
    fn load_and_parse_module(
        &mut self,
        import_path: &str,
        span: Span,
        module_id: ModuleId,
    ) -> Result<ParsedModule, ()> {
        let is_relative = import_path.starts_with("./") || import_path.starts_with("../");
        let module_info = if is_relative {
            match &self.module.current_file_path {
                Some(current_path) => self
                    .module
                    .module_loader
                    .load_relative(import_path, current_path)
                    .map_err(|e| {
                        self.add_error(
                            SemanticError::ModuleNotFound {
                                path: import_path.to_string(),
                                message: e.to_string(),
                                span: span.into(),
                            },
                            span,
                        );
                    })?,
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
            self.module.module_loader.load(import_path).map_err(|e| {
                self.add_error(
                    SemanticError::ModuleNotFound {
                        path: import_path.to_string(),
                        message: e.to_string(),
                        span: span.into(),
                    },
                    span,
                );
            })?
        };

        let module_file_path = module_info.path.clone();

        // Parse the module (pass module_id so NodeIds are globally unique)
        let mut parser = Parser::new(&module_info.source, module_id);
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

        // Generator transform is no longer needed -- generators are compiled
        // directly to coroutine-backed iterators in codegen.
        let mut module_interner = parser.into_interner();
        module_interner.seed_builtin_symbols();

        Ok(ParsedModule {
            program,
            interner: module_interner,
            file_path: module_file_path,
        })
    }

    /// Phase 4: Iterate module declarations to collect exports, constants,
    /// deferred function types, and type names for post-analysis resolution.
    fn collect_module_declarations<'a>(
        &mut self,
        program: &'a Program,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> ModuleDeclarations<'a> {
        let mut decls = ModuleDeclarations {
            exports: FxHashMap::default(),
            constants: FxHashMap::default(),
            external_funcs: FxHashSet::default(),
            type_names: ModuleTypeNames::default(),
            deferred_functions: Vec::new(),
            deferred_externals: Vec::new(),
            deferred_generic_externals: Vec::new(),
        };

        // Track constants by Symbol so later declarations can reference earlier ones.
        // E.g. `let PI = 3.14159; let TWO_PI = PI * 2.0` — TWO_PI can see PI.
        let mut known_constants = std::collections::HashMap::<Symbol, ConstantValue>::new();

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[f.name], module_interner);
                    decls.deferred_functions.push((name_id, f));
                }
                Decl::Let(l) if !l.mutable => {
                    let init_expr = match &l.init {
                        LetInit::Expr(e) => e,
                        LetInit::TypeAlias(_) => continue,
                    };
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[l.name], module_interner);
                    let const_val = eval_const_expr(init_expr, &known_constants);
                    let arena = self.type_arena();
                    let ty_id = match &const_val {
                        Some(ConstantValue::F64(_)) => arena.f64(),
                        Some(ConstantValue::I64(_)) => arena.i64(),
                        Some(ConstantValue::Bool(_)) => arena.bool(),
                        Some(ConstantValue::String(_)) => arena.string(),
                        None => arena.invalid(),
                    };
                    drop(arena);
                    decls.exports.insert(name_id, ty_id);
                    if let Some(cv) = const_val {
                        known_constants.insert(l.name, cv.clone());
                        decls.constants.insert(name_id, cv);
                    }
                }
                Decl::External(ext) => {
                    for func in &ext.functions {
                        let name_id = self.name_table_mut().intern(
                            module_id,
                            &[func.vole_name],
                            module_interner,
                        );
                        if !func.type_params.is_empty() {
                            decls.deferred_generic_externals.push((name_id, func));
                        } else {
                            decls.deferred_externals.push((name_id, func));
                        }
                    }
                }
                Decl::Interface(iface) => {
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[iface.name], module_interner);
                    decls.type_names.interfaces.push((name_id, iface.name));
                }
                Decl::Struct(struct_decl) => {
                    let name_id = self.name_table_mut().intern(
                        module_id,
                        &[struct_decl.name],
                        module_interner,
                    );
                    decls.type_names.structs.push((name_id, struct_decl.name));
                }
                Decl::Class(class) => {
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[class.name], module_interner);
                    decls.type_names.classes.push((name_id, class.name));
                }
                Decl::Error(err) => {
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[err.name], module_interner);
                    decls.type_names.errors.push((name_id, err.name));
                }
                Decl::Sentinel(sentinel_decl) => {
                    let name_id = self.name_table_mut().intern(
                        module_id,
                        &[sentinel_decl.name],
                        module_interner,
                    );
                    decls
                        .type_names
                        .sentinels
                        .push((name_id, sentinel_decl.name));
                }
                _ => {}
            }
        }

        decls
    }

    /// Phase 5a (partial): Merge sub-analyzer results into the shared flat maps.
    ///
    /// Because NodeIds are now globally unique (they embed a ModuleId), there are
    /// no collisions when merging results from different modules.
    fn store_sub_analyzer_results(&mut self, _module_key: &str, sub_analyzer: Analyzer) {
        use crate::expression_data::ExpressionData;
        let module_data = ExpressionData {
            types: sub_analyzer.results.expr_types,
            methods: sub_analyzer.results.method_resolutions.into_inner(),
            generics: sub_analyzer.results.generic_calls,
            class_method_generics: sub_analyzer.results.class_method_calls,
            static_method_generics: sub_analyzer.results.static_method_calls,
            is_check_results: sub_analyzer.results.is_check_results,
            declared_var_types: sub_analyzer.results.declared_var_types,
            lambda_analysis: sub_analyzer.lambda.analysis,
            intrinsic_keys: sub_analyzer.results.intrinsic_keys,
            resolved_call_args: sub_analyzer.results.resolved_call_args,
            ..Default::default()
        };
        self.ctx.merged_expr_data.borrow_mut().merge(module_data);
    }

    /// Resolve parameter and return types into a function ArenaTypeId.
    /// Used for deferred resolution of function and external function declarations.
    fn resolve_func_type(
        &mut self,
        params: &[Param],
        return_type: Option<&TypeExpr>,
        module_interner: &Interner,
        module_id: ModuleId,
    ) -> ArenaTypeId {
        let mut ctx = TypeResolutionContext {
            db: &self.ctx.db,
            interner: module_interner,
            module_id,
            type_params: None,
            self_type: None,
            imports: &[],
            priority_module: None,
        };
        let param_ids: crate::type_arena::TypeIdVec = params
            .iter()
            .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
            .collect();
        let return_id = return_type
            .map(|rt| resolve_type_to_id(rt, &mut ctx))
            .unwrap_or_else(|| self.type_arena().void());
        self.type_arena_mut().function(param_ids, return_id, false)
    }

    /// Resolve a single generic external function type and register its generic info.
    fn resolve_generic_external(
        &mut self,
        name_id: NameId,
        func: &ExternalFunc,
        exports: &mut FxHashMap<NameId, ArenaTypeId>,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        let builtin_mod = self.name_table_mut().builtin_module();
        let mut type_param_scope = TypeParamScope::new();
        let mut type_params: Vec<TypeParamInfo> = Vec::new();
        for tp in &func.type_params {
            let tp_name_str = module_interner.resolve(tp.name);
            let tp_name_id = self
                .name_table_mut()
                .intern_raw(builtin_mod, &[tp_name_str]);
            let tp_info = TypeParamInfo {
                name: tp.name,
                name_id: tp_name_id,
                constraint: None,
                type_param_id: None,
                variance: TypeParamVariance::default(),
            };
            type_param_scope.add(tp_info.clone());
            type_params.push(tp_info);
        }

        let (func_type_id, param_type_ids, return_type_id) = {
            let mut ctx = TypeResolutionContext::with_type_params(
                &self.ctx.db,
                module_interner,
                module_id,
                &type_param_scope,
            );
            let param_ids: Vec<ArenaTypeId> = func
                .params
                .iter()
                .map(|p| resolve_type_to_id(&p.ty, &mut ctx))
                .collect();
            let return_id = func
                .return_type
                .as_ref()
                .map(|rt| resolve_type_to_id(rt, &mut ctx))
                .unwrap_or_else(|| self.type_arena().void());
            let func_id = self
                .type_arena_mut()
                .function(param_ids.clone(), return_id, false);
            (func_id, param_ids, return_id)
        };

        exports.insert(name_id, func_type_id);

        // Register in EntityRegistry so module destructuring can find generic info
        let param_names: Vec<String> = func
            .params
            .iter()
            .map(|p| module_interner.resolve(p.name).to_string())
            .collect();
        let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);
        let func_id = self.entity_registry_mut().register_function_full(
            name_id,
            name_id,
            module_id,
            signature,
            func.params.len(),
            vec![],
            param_names,
            true, // generic externals are external
        );
        self.entity_registry_mut().set_function_generic_info(
            func_id,
            GenericFuncInfo {
                type_params,
                param_types: param_type_ids,
                return_type: return_type_id,
            },
        );
    }

    /// Phase 5e: Populate type exports (interfaces, structs, classes, errors, sentinels)
    /// after sub-analysis has registered them in the entity registry.
    fn populate_type_exports(
        &mut self,
        exports: &mut FxHashMap<NameId, ArenaTypeId>,
        type_names: &ModuleTypeNames,
        module_interner: &Interner,
        module_id: ModuleId,
    ) {
        for &(name_id, iface_sym) in &type_names.interfaces {
            let type_def_id = {
                let iface_str = module_interner.resolve(iface_sym);
                self.resolver_for_module(module_interner, module_id)
                    .resolve_type_str_or_interface(iface_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let iface_type_id = self
                    .type_arena_mut()
                    .interface(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, iface_type_id);
            }
        }

        for &(name_id, struct_sym) in &type_names.structs {
            let type_def_id = {
                let struct_str = module_interner.resolve(struct_sym);
                self.resolver_for_module(module_interner, module_id)
                    .resolve_type_str_or_interface(struct_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let struct_type_id = self
                    .type_arena_mut()
                    .struct_type(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, struct_type_id);
            }
        }

        for &(name_id, class_sym) in &type_names.classes {
            let type_def_id = {
                let class_str = module_interner.resolve(class_sym);
                self.resolver_for_module(module_interner, module_id)
                    .resolve_type_str_or_interface(class_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let class_type_id = self
                    .type_arena_mut()
                    .class(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, class_type_id);
            }
        }

        for &(name_id, error_sym) in &type_names.errors {
            let type_def_id = {
                let error_str = module_interner.resolve(error_sym);
                self.resolver_for_module(module_interner, module_id)
                    .resolve_type_str_or_interface(error_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let error_type_id = self.type_arena_mut().error_type(type_def_id);
                exports.insert(name_id, error_type_id);
            }
        }

        for &(name_id, sentinel_sym) in &type_names.sentinels {
            let type_def_id = {
                let sentinel_str = module_interner.resolve(sentinel_sym);
                self.resolver_for_module(module_interner, module_id)
                    .resolve_type_str_or_interface(sentinel_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let sentinel_type_id = self
                    .type_arena_mut()
                    .struct_type(type_def_id, smallvec::smallvec![]);
                self.type_arena_mut().mark_sentinel(sentinel_type_id);
                exports.insert(name_id, sentinel_type_id);
            }
        }
    }

    /// Phases 5f-5h: Store program/interner, create module type, and log.
    fn finalize_module(
        &mut self,
        data: ModuleFinalization,
        module_key: &str,
        module_id: ModuleId,
        import_path: &str,
    ) -> ArenaTypeId {
        // Phase 5f: Store the program and interner for compiling pure Vole functions.
        // IMPORTANT: This must happen AFTER sub_analyzer.analyze() because analysis
        // populates lambda capture lists (stored in RefCell<Vec<Capture>> on AST nodes).
        self.ctx
            .module_programs
            .borrow_mut()
            .insert(module_key.to_string(), (data.program, data.interner));

        // Phase 5g: Create TypeId from exports and register module metadata
        let exports_vec: smallvec::SmallVec<[(NameId, ArenaTypeId); 8]> =
            data.exports.into_iter().collect();
        let mut arena = self.type_arena_mut();
        arena.register_module_metadata(
            module_id,
            crate::type_arena::ModuleMetadata {
                constants: data.constants,
                external_funcs: data.external_funcs,
            },
        );
        let type_id = arena.module(module_id, exports_vec);
        drop(arena);

        // Phase 5h: Debug trace
        let module_path_check = self.name_table().module_path(module_id).to_string();
        tracing::debug!(
            import_path,
            %module_key,
            ?module_id,
            %module_path_check,
            "analyze_module: created module type"
        );

        type_id
    }

    /// Fork for analyzing an imported module.
    /// Shares the `AnalyzerContext` so TypeIds remain valid across analyzers.
    ///
    /// `loading_prelude` is set to `true` to prevent redundant prelude loading
    /// (prelude definitions are already in the shared context). However, we must
    /// propagate `functions_by_name` and `generic_prelude_functions` so that
    /// prelude functions (e.g., `panic -> never`) are available for cross-interner
    /// lookup in the sub-module.
    fn fork_for_module(&self, module_id: ModuleId, module_file_path: Option<PathBuf>) -> Analyzer {
        Analyzer {
            ctx: Rc::clone(&self.ctx),
            module: ModuleContext {
                current_module: module_id,
                current_file_path: module_file_path,
                loading_prelude: true,
                module_loader: self.module.module_loader.new_child(),
                ..Default::default()
            },
            symbols: SymbolTables {
                functions_by_name: self.symbols.functions_by_name.clone(),
                generic_prelude_functions: self.symbols.generic_prelude_functions.clone(),
                ..Default::default()
            },
            ..Default::default()
        }
    }

    /// Fork for analyzing a tests block as a virtual module.
    /// Shares the `AnalyzerContext` so TypeIds remain valid, and inherits
    /// the parent's scope so test code can see parent types/functions.
    ///
    /// The sub-analyzer keeps the parent's `current_module` so that all name
    /// lookups (function calls, entity registry) work normally. The virtual
    /// `module_id` is used only for type shell registration (to isolate types).
    pub(super) fn fork_for_tests_module(&mut self, _module_id: ModuleId) -> Analyzer {
        // Build a child scope from the parent's current scope.
        // The sub-analyzer gets a fresh scope that has the parent scope as parent,
        // so lookups chain to parent definitions.
        let parent_scope = std::mem::take(&mut self.env.scope);
        let child_scope = Scope::with_parent(parent_scope);

        let mut sub = Analyzer {
            ctx: Rc::clone(&self.ctx),
            env: TypeCheckEnv {
                scope: child_scope,
                parent_modules: self.env.parent_modules.clone(),
                ..Default::default()
            },
            symbols: SymbolTables {
                functions: self.symbols.functions.clone(),
                functions_by_name: self.symbols.functions_by_name.clone(),
                globals: self.symbols.globals.clone(),
                constant_globals: self.symbols.constant_globals.clone(),
                generic_prelude_functions: self.symbols.generic_prelude_functions.clone(),
            },
            module: ModuleContext {
                current_module: self.module.current_module,
                current_file_path: self.module.current_file_path.clone(),
                loading_prelude: true,
                module_loader: self.module.module_loader.new_child(),
                ..Default::default()
            },
            ..Default::default()
        };
        // Carry over the type_param_stack so type params from parent scope are visible
        sub.env.type_param_stack = self.env.type_param_stack.clone();
        sub
    }

    /// Restore scope from a tests module sub-analyzer.
    /// The sub-analyzer's scope chain has the parent scope at its root.
    /// We pop back to recover the original parent scope.
    pub(super) fn restore_scope_from_tests_module(&mut self, mut sub: Analyzer) {
        // The sub-analyzer scope chain: sub.scope -> parent_scope
        // We want the parent scope back.
        if let Some(parent) = std::mem::take(&mut sub.env.scope).into_parent() {
            self.env.scope = parent;
        }
    }

    /// Merge analysis results from a tests module sub-analyzer back into the parent.
    pub(super) fn merge_tests_module_results(&mut self, sub: &Analyzer) {
        // Merge expr_types
        self.results
            .expr_types
            .extend(sub.results.expr_types.iter().map(|(&k, &v)| (k, v)));
        // Merge method_resolutions
        for (k, v) in sub.results.method_resolutions.clone_inner() {
            self.results.method_resolutions.insert(k, v);
        }
        // Merge generic_calls
        self.results.generic_calls.extend(
            sub.results
                .generic_calls
                .iter()
                .map(|(&k, v)| (k, v.clone())),
        );
        // Merge class_method_calls
        self.results.class_method_calls.extend(
            sub.results
                .class_method_calls
                .iter()
                .map(|(&k, v)| (k, v.clone())),
        );
        // Merge static_method_calls
        self.results.static_method_calls.extend(
            sub.results
                .static_method_calls
                .iter()
                .map(|(&k, v)| (k, v.clone())),
        );
        // Merge substituted_return_types
        self.results.substituted_return_types.extend(
            sub.results
                .substituted_return_types
                .iter()
                .map(|(&k, &v)| (k, v)),
        );
        // Merge lambda_defaults
        self.lambda
            .defaults
            .extend(sub.lambda.defaults.iter().map(|(&k, v)| (k, v.clone())));
        // Merge is_check_results
        self.results
            .is_check_results
            .extend(sub.results.is_check_results.iter().map(|(&k, v)| (k, *v)));
        // Merge declared_var_types
        self.results
            .declared_var_types
            .extend(sub.results.declared_var_types.iter().map(|(&k, &v)| (k, v)));
        // Merge tests_virtual_modules
        self.results.tests_virtual_modules.extend(
            sub.results
                .tests_virtual_modules
                .iter()
                .map(|(&k, &v)| (k, v)),
        );
        // Merge lambda_analysis
        self.lambda
            .analysis
            .extend(sub.lambda.analysis.iter().map(|(&k, v)| (k, v.clone())));
        // Merge resolved_call_args
        self.results.resolved_call_args.extend(
            sub.results
                .resolved_call_args
                .iter()
                .map(|(&k, v)| (k, v.clone())),
        );
        // Merge intrinsic_keys
        self.results.intrinsic_keys.extend(
            sub.results
                .intrinsic_keys
                .iter()
                .map(|(k, v)| (*k, v.clone())),
        );
        // Merge synthetic_it_lambdas
        self.results.synthetic_it_lambdas.extend(
            sub.results
                .synthetic_it_lambdas
                .iter()
                .map(|(&k, v)| (k, v.clone())),
        );
        // Merge errors and warnings
        self.diagnostics
            .errors
            .extend(sub.diagnostics.errors.iter().cloned());
        self.diagnostics
            .warnings
            .extend(sub.diagnostics.warnings.iter().cloned());
    }

    /// Fork for analyzing a prelude file.
    /// Shares the `AnalyzerContext` so module_expr_types, module_method_resolutions,
    /// and other shared maps are visible without cloning.
    pub(super) fn fork_for_prelude(&self, module_id: ModuleId, file_path: PathBuf) -> Analyzer {
        Analyzer {
            ctx: Rc::clone(&self.ctx),
            module: ModuleContext {
                current_module: module_id,
                current_file_path: Some(file_path),
                loading_prelude: true,
                module_loader: self.module.module_loader.new_child(),
                ..Default::default()
            },
            ..Default::default()
        }
    }
}

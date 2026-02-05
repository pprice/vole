// src/sema/analyzer/module.rs
//! Module-level analysis: loading, parsing, and analyzing imported modules.

use super::*;
use crate::entity_defs::MethodBinding;

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
                    self.scope.define(
                        let_stmt.name,
                        Variable {
                            ty: module_type_id,
                            mutable: false,
                            declaration_span: let_stmt.span,
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

    #[allow(clippy::result_unit_err)] // Error is added to self.errors vector
    #[tracing::instrument(skip(self, span, _interner), fields(path = %import_path))]
    pub fn analyze_module(
        &mut self,
        import_path: &str,
        span: Span,
        _interner: &Interner,
    ) -> Result<ArenaTypeId, ()> {
        // Resolve path first (cheap - no file content read) to get canonical path for cache lookup
        let canonical_path = match self
            .module_loader
            .resolve_path(import_path, self.current_file_path.as_deref())
        {
            Ok(path) => {
                // Canonicalize to ensure consistent cache keys (resolves `..` components)
                path.canonicalize()
                    .unwrap_or(path)
                    .to_string_lossy()
                    .to_string()
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
                return Err(());
            }
        };

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

        // Check for circular import: if this module is already being analyzed
        // somewhere in the call stack, we have a cycle.
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

        // Mark this module as in-progress before loading/analyzing
        self.ctx
            .modules_in_progress
            .borrow_mut()
            .insert(canonical_path.clone());

        // Helper macro to clean up modules_in_progress on early return
        macro_rules! bail_module {
            ($self:expr, $canonical_path:expr) => {
                $self
                    .ctx
                    .modules_in_progress
                    .borrow_mut()
                    .remove($canonical_path);
            };
        }

        // Cache miss - now load the file content
        let is_relative = import_path.starts_with("./") || import_path.starts_with("../");
        let module_info = if is_relative {
            match &self.current_file_path {
                Some(current_path) => {
                    match self.module_loader.load_relative(import_path, current_path) {
                        Ok(info) => info,
                        Err(e) => {
                            bail_module!(self, &canonical_path);
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
                    bail_module!(self, &canonical_path);
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
            match self.module_loader.load(import_path) {
                Ok(info) => info,
                Err(e) => {
                    bail_module!(self, &canonical_path);
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

        // Save the module's file path for sub-analyzer (for nested relative imports)
        let module_file_path = module_info.path.clone();

        // Parse the module
        let mut parser = Parser::new(&module_info.source);
        let mut program = match parser.parse_program() {
            Ok(p) => p,
            Err(e) => {
                bail_module!(self, &canonical_path);
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

        // Transform generators in the imported module (yield -> state machine)
        // This must happen before semantic analysis so codegen sees the desugared AST.
        let mut module_interner_mut = parser.into_interner();
        let (_, transform_errors) =
            crate::transforms::transform_generators(&mut program, &mut module_interner_mut);
        if !transform_errors.is_empty() {
            bail_module!(self, &canonical_path);
            // Report the first transform error as a module error
            self.add_error(
                SemanticError::ModuleParseError {
                    path: import_path.to_string(),
                    message: format!("generator transform error: {}", transform_errors[0].error),
                    span: span.into(),
                },
                span,
            );
            return Err(());
        }
        let module_interner = module_interner_mut;

        // Collect exports, constants, and track external functions
        let mut exports = FxHashMap::default();
        let mut constants = FxHashMap::default();
        let mut external_funcs = FxHashSet::default();
        // Interfaces are collected separately for post-analysis lookup
        let mut interface_names: Vec<(NameId, Symbol)> = Vec::new();
        let mut struct_names: Vec<(NameId, Symbol)> = Vec::new();
        let mut class_names: Vec<(NameId, Symbol)> = Vec::new();
        let mut error_names: Vec<(NameId, Symbol)> = Vec::new();
        // Functions and external functions are collected for post-analysis type resolution
        // (needed for types that reference class/error types defined in the same module,
        // e.g. fallible return types that reference module-local error types)
        let mut deferred_functions: Vec<(NameId, &FuncDecl)> = Vec::new();
        let mut deferred_externals: Vec<(NameId, &ExternalFunc)> = Vec::new();
        let mut deferred_generic_externals: Vec<(NameId, &ExternalFunc)> = Vec::new();

        // For stdlib modules, use symbolic paths like "std:math" for native registry lookups.
        // For user modules, use canonical file path for consistent deduplication.
        let module_key = if import_path.starts_with("std:") {
            import_path.to_string()
        } else {
            canonical_path.clone()
        };
        tracing::debug!(import_path, %module_key, "analyze_module: creating module_id");
        let module_id = self.name_table_mut().module_id(&module_key);

        for decl in &program.declarations {
            match decl {
                Decl::Function(f) => {
                    // Defer function type resolution until after sub_analyzer.analyze() runs.
                    // This allows functions to reference class types defined in the same module.
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[f.name], &module_interner);
                    deferred_functions.push((name_id, f));
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
                    // Defer external function type resolution until after sub_analyzer.analyze()
                    // runs. This allows fallible return types to reference error types defined
                    // in the same module (e.g. `fallible(string, NotFound | PermissionDenied)`).
                    for func in &ext.functions {
                        let name_id = self.name_table_mut().intern(
                            module_id,
                            &[func.vole_name],
                            &module_interner,
                        );
                        if !func.type_params.is_empty() {
                            deferred_generic_externals.push((name_id, func));
                        } else {
                            deferred_externals.push((name_id, func));
                        }
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
                Decl::Struct(struct_decl) => {
                    // Export structs so they can be used as types from the module
                    let name_id = self.name_table_mut().intern(
                        module_id,
                        &[struct_decl.name],
                        &module_interner,
                    );
                    struct_names.push((name_id, struct_decl.name));
                }
                Decl::Class(class) => {
                    // Export classes so they can be used as types from the module
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[class.name], &module_interner);
                    class_names.push((name_id, class.name));
                }
                Decl::Error(err) => {
                    // Export error types so they can be used in match patterns
                    let name_id =
                        self.name_table_mut()
                            .intern(module_id, &[err.name], &module_interner);
                    error_names.push((name_id, err.name));
                }
                _ => {} // Skip other declarations (implement blocks, etc.)
            }
        }

        // Store the program and interner for compiling pure Vole functions
        // Use module_key for consistent lookup with module_id
        self.ctx.module_programs.borrow_mut().insert(
            module_key.clone(),
            (program.clone(), module_interner.clone()),
        );

        // Run semantic analysis on the module to populate expr_types for function bodies.
        // This is needed for codegen to resolve return types of calls to external functions
        // inside the module (e.g., min(max(x, lo), hi) in math.clamp).
        let mut sub_analyzer = self.fork_for_module(module_id, Some(module_file_path));
        let analyze_result = sub_analyzer.analyze(&program, &module_interner);
        if let Err(ref errors) = analyze_result {
            tracing::warn!(import_path, ?errors, "module analysis errors");
            // Propagate circular import errors to the parent so they're reported to the user.
            // Without this, a self-importing file checked individually would silently succeed.
            for err in errors {
                if matches!(err.error, SemanticError::CircularImport { .. }) {
                    self.errors.push(err.clone());
                }
            }
        }
        // Store module-specific expr_types (NodeIds are per-program)
        // Nested module entries are already in the shared ctx from the sub-analyzer.
        self.ctx
            .module_expr_types
            .borrow_mut()
            .insert(module_key.clone(), sub_analyzer.expr_types.clone());
        // Store module-specific method_resolutions (NodeIds are per-program)
        self.ctx.module_method_resolutions.borrow_mut().insert(
            module_key.clone(),
            sub_analyzer.method_resolutions.into_inner(),
        );
        // Store module-specific is_check_results (NodeIds are per-program)
        self.ctx
            .module_is_check_results
            .borrow_mut()
            .insert(module_key.clone(), sub_analyzer.is_check_results.clone());

        // Now resolve deferred function types after sub-analysis has registered class types
        for (name_id, f) in deferred_functions {
            let func_type_id = {
                let mut ctx = TypeResolutionContext {
                    db: &self.ctx.db,
                    interner: &module_interner,
                    module_id,
                    type_params: None,
                    self_type: None,
                    imports: &[],
                    priority_module: None,
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
            exports.insert(name_id, func_type_id);
        }

        // Now resolve deferred non-generic external function types
        // Error types (e.g. NotFound, PermissionDenied) are now registered by sub-analysis
        for (name_id, func) in deferred_externals {
            let func_type_id = {
                let mut ctx = TypeResolutionContext {
                    db: &self.ctx.db,
                    interner: &module_interner,
                    module_id,
                    type_params: None,
                    self_type: None,
                    imports: &[],
                    priority_module: None,
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
            exports.insert(name_id, func_type_id);
            external_funcs.insert(name_id);
        }

        // Now resolve deferred generic external function types
        for (name_id, func) in deferred_generic_externals {
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
                    &module_interner,
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
            let signature = FunctionType::from_ids(&param_type_ids, return_type_id, false);
            let func_id = self.entity_registry_mut().register_function_full(
                name_id,
                name_id,
                module_id,
                signature,
                func.params.len(),
                vec![],
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

        // Now populate interface exports after sub-analysis has registered them
        for (name_id, iface_sym) in interface_names {
            // Look up interface type from entity registry
            // Use block to ensure resolver guard is dropped before type_arena_mut
            // Use resolver_for_module with the module's ID, not self.current_module
            let type_def_id = {
                let iface_str = module_interner.resolve(iface_sym);
                self.resolver_for_module(&module_interner, module_id)
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

        // Now populate struct exports after sub-analysis has registered them
        for (name_id, struct_sym) in struct_names {
            let type_def_id = {
                let struct_str = module_interner.resolve(struct_sym);
                self.resolver_for_module(&module_interner, module_id)
                    .resolve_type_str_or_interface(struct_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let struct_type_id = self
                    .type_arena_mut()
                    .struct_type(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, struct_type_id);
            }
        }

        // Now populate class exports after sub-analysis has registered them
        for (name_id, class_sym) in class_names {
            let type_def_id = {
                let class_str = module_interner.resolve(class_sym);
                // Use resolve_type_str_or_interface which has fallback to class_by_short_name
                // Use resolver_for_module with the module's ID, not self.current_module
                self.resolver_for_module(&module_interner, module_id)
                    .resolve_type_str_or_interface(class_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let class_type_id = self
                    .type_arena_mut()
                    .class(type_def_id, smallvec::smallvec![]);
                exports.insert(name_id, class_type_id);
            }
        }

        // Now populate error type exports after sub-analysis has registered them
        for (name_id, error_sym) in error_names {
            let type_def_id = {
                let error_str = module_interner.resolve(error_sym);
                self.resolver_for_module(&module_interner, module_id)
                    .resolve_type_str_or_interface(error_str, &self.entity_registry())
            };
            if let Some(type_def_id) = type_def_id {
                let error_type_id = self.type_arena_mut().error_type(type_def_id);
                exports.insert(name_id, error_type_id);
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

        // Debug: trace what module_id and module_path are being used
        let module_path_check = self.name_table().module_path(module_id).to_string();
        tracing::debug!(
            import_path,
            %module_key,
            ?module_id,
            %module_path_check,
            "analyze_module: created module type"
        );

        // Module analysis complete - remove from in-progress set
        self.ctx
            .modules_in_progress
            .borrow_mut()
            .remove(&canonical_path);

        // Cache the TypeId with canonical path for consistent lookups
        self.ctx
            .module_type_ids
            .borrow_mut()
            .insert(canonical_path, type_id);

        Ok(type_id)
    }

    /// Fork for analyzing an imported module.
    /// Shares the `AnalyzerContext` so TypeIds remain valid across analyzers.
    fn fork_for_module(&self, module_id: ModuleId, module_file_path: Option<PathBuf>) -> Analyzer {
        Analyzer {
            ctx: Rc::clone(&self.ctx),
            current_module: module_id,
            current_file_path: module_file_path,
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            module_loader: self.module_loader.new_child(),
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
        let parent_scope = std::mem::take(&mut self.scope);
        let child_scope = Scope::with_parent(parent_scope);

        let mut sub = Analyzer {
            ctx: Rc::clone(&self.ctx),
            // Keep the parent's module ID for all lookups
            current_module: self.current_module,
            current_file_path: self.current_file_path.clone(),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            module_loader: self.module_loader.new_child(),
            scope: child_scope,
            // Inherit parent functions and globals so tests can call parent functions
            functions: self.functions.clone(),
            functions_by_name: self.functions_by_name.clone(),
            globals: self.globals.clone(),
            constant_globals: self.constant_globals.clone(),
            // Inherit parent_modules chain
            parent_modules: self.parent_modules.clone(),
            // Inherit generic prelude functions so tests can call generic functions like print/println
            generic_prelude_functions: self.generic_prelude_functions.clone(),
            ..Default::default()
        };
        // Carry over the type_param_stack so type params from parent scope are visible
        sub.type_param_stack = self.type_param_stack.clone();
        sub
    }

    /// Restore scope from a tests module sub-analyzer.
    /// The sub-analyzer's scope chain has the parent scope at its root.
    /// We pop back to recover the original parent scope.
    pub(super) fn restore_scope_from_tests_module(&mut self, mut sub: Analyzer) {
        // The sub-analyzer scope chain: sub.scope -> parent_scope
        // We want the parent scope back.
        if let Some(parent) = std::mem::take(&mut sub.scope).into_parent() {
            self.scope = parent;
        }
    }

    /// Merge analysis results from a tests module sub-analyzer back into the parent.
    pub(super) fn merge_tests_module_results(&mut self, sub: &Analyzer) {
        // Merge expr_types
        self.expr_types
            .extend(sub.expr_types.iter().map(|(&k, &v)| (k, v)));
        // Merge method_resolutions
        for (k, v) in sub.method_resolutions.clone_inner() {
            self.method_resolutions.insert(k, v);
        }
        // Merge generic_calls
        self.generic_calls
            .extend(sub.generic_calls.iter().map(|(&k, v)| (k, v.clone())));
        // Merge class_method_calls
        self.class_method_calls
            .extend(sub.class_method_calls.iter().map(|(&k, v)| (k, v.clone())));
        // Merge static_method_calls
        self.static_method_calls
            .extend(sub.static_method_calls.iter().map(|(&k, v)| (k, v.clone())));
        // Merge substituted_return_types
        self.substituted_return_types
            .extend(sub.substituted_return_types.iter().map(|(&k, &v)| (k, v)));
        // Merge lambda_defaults
        self.lambda_defaults
            .extend(sub.lambda_defaults.iter().map(|(&k, v)| (k, v.clone())));
        // Merge is_check_results
        self.is_check_results
            .extend(sub.is_check_results.iter().map(|(&k, v)| (k, *v)));
        // Merge declared_var_types
        self.declared_var_types
            .extend(sub.declared_var_types.iter().map(|(&k, &v)| (k, v)));
        // Merge tests_virtual_modules
        self.tests_virtual_modules
            .extend(sub.tests_virtual_modules.iter().map(|(&k, &v)| (k, v)));
        // Merge errors and warnings
        self.errors.extend(sub.errors.iter().cloned());
        self.warnings.extend(sub.warnings.iter().cloned());
    }

    /// Fork for analyzing a prelude file.
    /// Shares the `AnalyzerContext` so module_expr_types, module_method_resolutions,
    /// and other shared maps are visible without cloning.
    pub(super) fn fork_for_prelude(&self, module_id: ModuleId, file_path: PathBuf) -> Analyzer {
        Analyzer {
            ctx: Rc::clone(&self.ctx),
            current_module: module_id,
            current_file_path: Some(file_path),
            loading_prelude: true, // Prevent sub-analyzer from loading prelude
            module_loader: self.module_loader.new_child(),
            ..Default::default()
        }
    }
}

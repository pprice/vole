use super::super::*;
use crate::expression_data::LambdaDefaults;
use crate::implement_registry::TypeMappingKind;
use crate::type_arena::TypeId as ArenaTypeId;
use rustc_hash::{FxHashMap, FxHashSet};
use vole_identity::{NameId, Namer};

impl Analyzer {
    pub(super) fn check_call_expr(
        &mut self,
        expr: &Expr,
        call: &CallExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        if let ExprKind::Identifier(sym) = &call.callee.kind {
            // First check if it's a top-level function
            let func_type = self.symbols.functions.get(sym).cloned().or_else(|| {
                // Check by name for prelude functions (cross-interner lookup)
                let name = interner.resolve(*sym);
                self.symbols.functions_by_name.get(name).cloned()
            });
            if let Some(func_type) = func_type {
                // Check if this is actually a generic function (e.g. from prelude)
                // If so, skip to the generic function resolution path below
                let is_generic = {
                    let name_id =
                        self.name_table_mut()
                            .intern(self.module.current_module, &[*sym], interner);
                    let is_gen = self
                        .entity_registry()
                        .function_by_name(name_id)
                        .is_some_and(|fid| {
                            self.entity_registry()
                                .get_function(fid)
                                .generic_info
                                .is_some()
                        });
                    // Also check prelude modules for cross-interner generic functions
                    is_gen || self.is_prelude_generic_function(*sym, interner)
                };

                if !is_generic {
                    // Calling a user-defined function - conservatively mark side effects
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }

                    // Look up required_params from entity registry if available
                    let required_params = {
                        let name_id = self.name_table_mut().intern(
                            self.module.current_module,
                            &[*sym],
                            interner,
                        );
                        self.entity_registry()
                            .function_by_name(name_id)
                            .map(|fid| self.entity_registry().get_function(fid).required_params)
                            .unwrap_or(func_type.params_id.len())
                    };

                    return self.check_call_args_with_defaults_id(
                        &call.args,
                        &func_type.params_id,
                        required_params,
                        func_type.return_type_id,
                        expr.span,
                        interner,
                    );
                }
                // Fall through to generic function resolution
            }

            // Check if it's a variable with a function type (using TypeId path)
            // This must come BEFORE checking the entity registry for generic functions
            // to ensure local scope variables shadow global generics
            if let Some(var_type_id) = self.get_variable_type_id(*sym) {
                // Check if this is a generic function that should fall through to generic
                // function lookup. Only skip for variables that:
                // 1. Have TypeParams in their signature AND
                // 2. Have a corresponding generic function registered in EntityRegistry
                // (Lambda parameters like `f: (T) -> U` have TypeParams but shouldn't skip)
                let skip_for_generic = {
                    let arena = self.type_arena();
                    let has_type_params =
                        if let Some((params, ret, _)) = arena.unwrap_function(var_type_id) {
                            params.iter().any(|&p| arena.unwrap_type_param(p).is_some())
                                || arena.unwrap_type_param(ret).is_some()
                        } else {
                            false
                        };
                    drop(arena);

                    // Only skip if there's a registered generic function with this name
                    if has_type_params {
                        let name_id = self.name_table_mut().intern(
                            self.module.current_module,
                            &[*sym],
                            interner,
                        );
                        self.entity_registry()
                            .function_by_name(name_id)
                            .is_some_and(|fid| {
                                self.entity_registry()
                                    .get_function(fid)
                                    .generic_info
                                    .is_some()
                            })
                    } else {
                        false
                    }
                };

                if !skip_for_generic {
                    // Extract function info and drop arena before any mutable operations
                    let func_info = {
                        let arena = self.type_arena();
                        arena
                            .unwrap_function(var_type_id)
                            .map(|(params, ret, _)| (params.clone(), ret))
                    };

                    if let Some((params, ret)) = func_info {
                        // Calling a function-typed variable - conservatively mark side effects
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                            // Record capture if the callee is from outer scope
                            if !self.is_lambda_local(*sym)
                                && let Some(var) = self.env.scope.get(*sym)
                            {
                                self.record_capture(*sym, var.mutable);
                            }
                        }

                        // Check if this is a lambda with default parameters
                        if let Some(&(lambda_node_id, required_params)) =
                            self.lambda.variables.get(sym)
                        {
                            // Store lambda defaults info for codegen
                            self.lambda.defaults.insert(
                                expr.id,
                                LambdaDefaults {
                                    required_params,
                                    lambda_node_id,
                                },
                            );
                            return self.check_call_args_with_defaults_id(
                                &call.args,
                                &params,
                                required_params,
                                ret,
                                expr.span,
                                interner,
                            );
                        }

                        return self
                            .check_call_args_id(&call.args, &params, ret, expr.span, interner);
                    }

                    // Check if it's a variable with a functional interface type
                    let interface_info = {
                        let arena = self.type_arena();
                        arena.unwrap_interface(var_type_id).map(|(id, _)| id)
                    };

                    if let Some(type_def_id) = interface_info
                        && let Some(func_type) =
                            self.get_functional_interface_type_by_type_def_id(type_def_id)
                    {
                        // Calling a functional interface - treat like a closure call
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
                            // Record capture if the callee is from outer scope
                            if !self.is_lambda_local(*sym)
                                && let Some(var) = self.env.scope.get(*sym)
                            {
                                self.record_capture(*sym, var.mutable);
                            }
                        }
                        return self.check_call_args_id(
                            &call.args,
                            &func_type.params_id,
                            func_type.return_type_id,
                            expr.span,
                            interner,
                        );
                    }
                }
                // If skip_for_generic is true, fall through to generic function lookup below
            }

            // Check if it's a generic function via EntityRegistry
            // Split into separate borrows to avoid borrow conflicts
            // Also get full_name_id for the original function name (for imports with renaming)
            let (generic_info, generic_required_params, original_name_id) = {
                // First try current module
                let name_id =
                    self.name_table_mut()
                        .intern(self.module.current_module, &[*sym], interner);
                let registry = self.entity_registry();
                let func_id = registry.function_by_name(name_id);
                let result = func_id.map(|fid| {
                    let func_def = registry.get_function(fid);
                    (
                        func_def.generic_info.clone(),
                        func_def.required_params,
                        func_def.full_name_id,
                    )
                });

                // If not found in current module, try builtin module
                // (for generic external functions registered globally)
                if result.is_none() || result.as_ref().is_some_and(|(gi, _, _)| gi.is_none()) {
                    drop(registry);
                    let builtin_mod = self.name_table_mut().builtin_module();
                    let builtin_name_id =
                        self.name_table_mut().intern(builtin_mod, &[*sym], interner);
                    let registry = self.entity_registry();
                    let builtin_result = registry.function_by_name(builtin_name_id).map(|fid| {
                        let func_def = registry.get_function(fid);
                        (
                            func_def.generic_info.clone(),
                            func_def.required_params,
                            func_def.full_name_id,
                        )
                    });
                    drop(registry);

                    if builtin_result.is_some() {
                        builtin_result.unwrap_or((None, 0, builtin_name_id))
                    } else {
                        // Try prelude generic functions (e.g., print, println)
                        let func_name = interner.resolve(*sym);
                        if let Some(&prelude_name_id) =
                            self.symbols.generic_prelude_functions.get(func_name)
                        {
                            let registry = self.entity_registry();
                            registry
                                .function_by_name(prelude_name_id)
                                .map(|fid| {
                                    let func_def = registry.get_function(fid);
                                    (
                                        func_def.generic_info.clone(),
                                        func_def.required_params,
                                        func_def.full_name_id,
                                    )
                                })
                                .unwrap_or((None, 0, prelude_name_id))
                        } else {
                            (None, 0, builtin_name_id)
                        }
                    }
                } else {
                    result.unwrap_or((None, 0, name_id))
                }
            };
            if let Some(generic_def) = generic_info {
                let required_params = generic_required_params;
                // Calling a generic function - infer type params and monomorphize
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }

                // First, type-check the arguments to get their types (as TypeId)
                let arg_type_ids: Vec<ArenaTypeId> = call
                    .args
                    .iter()
                    .map(|arg| self.check_expr(arg, interner))
                    .collect::<Result<Vec<_>, _>>()?;

                // Infer type parameters from argument types (using TypeId version)
                let inferred_id = self.infer_type_params_id(
                    &generic_def.type_params,
                    &generic_def.param_types,
                    &arg_type_ids,
                );
                self.check_type_param_constraints_id(
                    &generic_def.type_params,
                    &inferred_id,
                    expr.span,
                    interner,
                );

                // Create the concrete function type by substituting via arena
                // Collect substitutions into an owned map for arena.substitute
                let subs: FxHashMap<_, _> = inferred_id.iter().map(|(&k, &v)| (k, v)).collect();
                let (concrete_param_ids, concrete_return_id) = {
                    let mut arena = self.type_arena_mut();
                    // Substitute all types using TypeId-based substitutions directly
                    let param_ids: Vec<_> = generic_def
                        .param_types
                        .iter()
                        .map(|&t| arena.substitute(t, &subs))
                        .collect();
                    let return_id = arena.substitute(generic_def.return_type, &subs);
                    (param_ids, return_id)
                };

                // Check arg count: must be at least required_params and at most total_params
                let total_params = concrete_param_ids.len();
                if call.args.len() < required_params || call.args.len() > total_params {
                    self.add_wrong_arg_count_range(
                        required_params,
                        total_params,
                        call.args.len(),
                        expr.span,
                    );
                    return Ok(ArenaTypeId::INVALID);
                }

                // Type check arguments against concrete params (using TypeId)
                for (i, (arg, &expected_id)) in
                    call.args.iter().zip(concrete_param_ids.iter()).enumerate()
                {
                    let arg_ty_id = arg_type_ids[i];
                    if !self.types_compatible_id(arg_ty_id, expected_id, interner) {
                        self.add_type_mismatch_id(expected_id, arg_ty_id, arg.span);
                    }
                }

                // Get or create monomorphized instance
                let type_args_id: Vec<ArenaTypeId> = generic_def
                    .type_params
                    .iter()
                    .filter_map(|tp| inferred_id.get(&tp.name_id).copied())
                    .collect();
                tracing::debug!(
                    func = %interner.resolve(*sym),
                    type_args = ?type_args_id.iter().map(|&id| self.type_display_id(id)).collect::<Vec<_>>(),
                    "generic instantiation"
                );
                let type_keys: Vec<_> = type_args_id.to_vec();
                let module_id = self.name_table().main_module();
                let name_id = {
                    let mut table = self.name_table_mut();
                    let mut namer = Namer::new(&mut table, interner);
                    namer.intern_symbol(module_id, *sym)
                };
                let key = MonomorphKey::new(name_id, type_keys);

                if !self.entity_registry_mut().monomorph_cache.contains(&key) {
                    let id = self.entity_registry_mut().monomorph_cache.next_unique_id();
                    let module_id = self.name_table().module_of(name_id);
                    let base_str = self
                        .name_table()
                        .last_segment_str(name_id)
                        .unwrap_or_else(|| interner.resolve(*sym).to_string());
                    let mangled_name = {
                        let mut table = self.name_table_mut();
                        let mut namer = Namer::new(&mut table, interner);
                        namer.monomorph_str(module_id, &base_str, id)
                    };
                    // Use inferred_id directly as substitutions (already TypeId-based)
                    // MonomorphInstance uses std HashMap
                    let substitutions: FxHashMap<NameId, ArenaTypeId> = inferred_id.clone();
                    let func_type =
                        FunctionType::from_ids(&concrete_param_ids, concrete_return_id, false);
                    self.entity_registry_mut().monomorph_cache.insert(
                        key.clone(),
                        MonomorphInstance {
                            original_name: original_name_id, // Use original export name for codegen
                            mangled_name,
                            instance_id: id,
                            func_type,
                            substitutions,
                        },
                    );
                }

                // Record the call -> monomorph key mapping for codegen
                self.results.generic_calls.insert(expr.id, key);

                // Resolve intrinsic key for constant folding.
                // If this is a generic external with compiler intrinsic mappings
                // (e.g., math.sqrt maps to "f64_sqrt"), record the concrete key
                // so the optimizer can fold calls with constant arguments.
                {
                    let callee_name = interner.resolve(*sym);
                    let ext_info = self
                        .implement_registry()
                        .get_generic_external(callee_name)
                        .cloned();
                    if let Some(ext_info) = ext_info {
                        let sub_types: FxHashSet<ArenaTypeId> =
                            inferred_id.values().copied().collect();
                        if let Some(ikey) =
                            resolve_intrinsic_key_from_mappings(&ext_info.type_mappings, &sub_types)
                        {
                            self.results.intrinsic_keys.insert(expr.id, ikey);
                        }
                    }
                }

                return Ok(concrete_return_id);
            }

            // Check if it's a known builtin function
            let name = interner.resolve(*sym);
            if name == "print_char" || name == "flush" {
                // Impure builtins - mark side effects if inside lambda
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                for arg in &call.args {
                    self.check_expr(arg, interner)?;
                }
                return Ok(ArenaTypeId::VOID);
            }

            // Check if it's a variable with a non-function type
            if let Some(var_ty_id) = self.get_variable_type_id(*sym) {
                let ty = self.type_display_id(var_ty_id);
                self.add_error(
                    SemanticError::NotCallable {
                        ty,
                        span: call.callee.span.into(),
                    },
                    call.callee.span,
                );
                // Still check args for more errors
                for arg in &call.args {
                    self.check_expr(arg, interner)?;
                }
                return Ok(ArenaTypeId::INVALID);
            }

            // Unknown identifier - conservatively mark as having side effects
            // since we can't prove the function is pure
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }
            for arg in &call.args {
                self.check_expr(arg, interner)?;
            }
            return Ok(ArenaTypeId::VOID);
        }

        // Non-identifier callee (e.g., a lambda expression being called directly)
        let callee_ty_id = self.check_expr(&call.callee, interner)?;

        let func_info = self
            .type_arena()
            .unwrap_function(callee_ty_id)
            .map(|(params, ret, _is_closure)| (params.clone(), ret));

        if let Some((param_ids, return_id)) = func_info {
            // Calling a function-typed expression - conservatively mark side effects
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }
            return self.check_call_args_id(&call.args, &param_ids, return_id, expr.span, interner);
        }

        // Non-callable type
        if !callee_ty_id.is_invalid() {
            let ty = self.type_display_id(callee_ty_id);
            self.add_error(
                SemanticError::NotCallable {
                    ty,
                    span: call.callee.span.into(),
                },
                call.callee.span,
            );
        }
        Ok(ArenaTypeId::INVALID)
    }
}

/// Resolve an intrinsic key from type mappings and concrete substitutions.
///
/// Used during sema to tag call-site NodeIds with their concrete intrinsic key
/// (e.g., `"f64_sqrt"`) so the optimizer can fold pure intrinsic calls.
pub(super) fn resolve_intrinsic_key_from_mappings(
    type_mappings: &[TypeMappingEntry],
    sub_types: &FxHashSet<ArenaTypeId>,
) -> Option<String> {
    let mut default_key = None;
    let mut exact_match = None;

    for mapping in type_mappings {
        match &mapping.kind {
            TypeMappingKind::Exact(type_id) if sub_types.contains(type_id) => {
                exact_match = Some(mapping.intrinsic_key.clone());
            }
            TypeMappingKind::Default => {
                default_key = Some(mapping.intrinsic_key.clone());
            }
            _ => {}
        }
    }

    exact_match.or(default_key)
}

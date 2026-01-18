use super::super::*;
use crate::identity::Namer;
use crate::sema::compatibility::TypeCompatibility;
use crate::sema::type_arena::TypeId as ArenaTypeId;
use crate::sema::types::{LegacyType, NominalType};

impl Analyzer {
    pub(super) fn check_call_expr(
        &mut self,
        expr: &Expr,
        call: &CallExpr,
        interner: &Interner,
    ) -> Result<ArenaTypeId, Vec<TypeError>> {
        // Handle assert specially
        if self.is_assert_call(&call.callee, interner) {
            // Assert is an impure builtin - mark side effects if inside lambda
            if self.in_lambda() {
                self.mark_lambda_has_side_effects();
            }

            if call.args.len() != 1 {
                self.add_error(
                    SemanticError::WrongArgumentCount {
                        expected: 1,
                        found: call.args.len(),
                        span: expr.span.into(),
                    },
                    expr.span,
                );
                return Ok(ArenaTypeId::VOID);
            }

            let arg_ty_id = self.check_expr(&call.args[0], interner)?;
            if !self.is_bool_id(arg_ty_id) && !arg_ty_id.is_invalid() {
                let found = self.type_display_id(arg_ty_id);
                self.add_error(
                    SemanticError::TypeMismatch {
                        expected: "bool".to_string(),
                        found,
                        span: call.args[0].span.into(),
                    },
                    call.args[0].span,
                );
            }

            return Ok(ArenaTypeId::VOID);
        }

        if let ExprKind::Identifier(sym) = &call.callee.kind {
            // First check if it's a top-level function
            let func_type = self.functions.get(sym).cloned().or_else(|| {
                // Check by name for prelude functions (cross-interner lookup)
                let name = interner.resolve(*sym);
                self.functions_by_name.get(name).cloned()
            });
            if let Some(func_type) = func_type {
                // Calling a user-defined function - conservatively mark side effects
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(self.type_to_id(&func_type.return_type));
            }

            // Check if it's a generic function via EntityRegistry
            let generic_info = {
                let name_id = self
                    .name_table
                    .intern(self.current_module, &[*sym], interner);
                self.entity_registry
                    .function_by_name(name_id)
                    .and_then(|func_id| {
                        self.entity_registry
                            .get_function(func_id)
                            .generic_info
                            .clone()
                    })
            };
            if let Some(generic_def) = generic_info {
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

                // Convert to LegacyTypes for inference (inference still uses LegacyType)
                let arg_types: Vec<LegacyType> = {
                    let arena = self.type_arena.borrow();
                    arg_type_ids.iter().map(|&id| arena.to_type(id)).collect()
                };

                // Convert TypeIds to LegacyTypes for inference
                let param_types: Vec<LegacyType> = generic_def
                    .param_types
                    .iter()
                    .map(|&t| self.type_arena.borrow().to_type(t))
                    .collect();

                // Infer type parameters from argument types
                let inferred =
                    self.infer_type_params(&generic_def.type_params, &param_types, &arg_types);
                self.check_type_param_constraints(
                    &generic_def.type_params,
                    &inferred,
                    expr.span,
                    interner,
                );

                // Create the concrete function type by substituting via arena
                let (concrete_params, concrete_return) = {
                    let mut arena = self.type_arena.borrow_mut();
                    // Convert substitutions to TypeId-based
                    let subs_id: hashbrown::HashMap<_, _> = inferred
                        .iter()
                        .map(|(&k, v)| (k, arena.from_type(v)))
                        .collect();
                    // Substitute all types
                    let param_ids: Vec<_> = generic_def
                        .param_types
                        .iter()
                        .map(|&t| arena.substitute(t, &subs_id))
                        .collect();
                    let return_id = arena.substitute(generic_def.return_type, &subs_id);
                    // Convert back to LegacyTypes
                    let params: Vec<LegacyType> =
                        param_ids.iter().map(|&t| arena.to_type(t)).collect();
                    let ret = arena.to_type(return_id);
                    (params, ret)
                };

                // Check arg count
                if call.args.len() != concrete_params.len() {
                    self.add_wrong_arg_count(concrete_params.len(), call.args.len(), expr.span);
                    return Ok(ArenaTypeId::INVALID);
                }

                // Type check arguments against concrete params
                for (i, (arg, expected)) in call.args.iter().zip(concrete_params.iter()).enumerate()
                {
                    let arg_ty = &arg_types[i];
                    if !arg_ty.is_compatible(expected) {
                        self.add_type_mismatch(expected, arg_ty, arg.span);
                    }
                }

                // Get or create monomorphized instance
                let type_args: Vec<LegacyType> = generic_def
                    .type_params
                    .iter()
                    .filter_map(|tp| inferred.get(&tp.name_id).cloned())
                    .collect();
                tracing::debug!(
                    func = %interner.resolve(*sym),
                    type_args = ?type_args.iter().map(|t| self.type_display(t)).collect::<Vec<_>>(),
                    "generic instantiation"
                );
                let type_keys = type_args.iter().map(|ty| self.type_key_for(ty)).collect();
                let module_id = self.name_table.main_module();
                let name_id = {
                    let mut namer = Namer::new(&mut self.name_table, interner);
                    namer.intern_symbol(module_id, *sym)
                };
                let key = MonomorphKey::new(name_id, type_keys);

                if !self.entity_registry.monomorph_cache.contains(&key) {
                    let id = self.entity_registry.monomorph_cache.next_unique_id();
                    let module_id = self.name_table.module_of(name_id);
                    let base_str = self
                        .name_table
                        .last_segment_str(name_id)
                        .unwrap_or_else(|| interner.resolve(*sym).to_string());
                    let mangled_name = {
                        let mut namer = Namer::new(&mut self.name_table, interner);
                        namer.monomorph_str(module_id, &base_str, id)
                    };
                    // Convert substitutions to TypeId for storage
                    let substitutions = {
                        let mut arena = self.type_arena.borrow_mut();
                        inferred
                            .iter()
                            .map(|(k, v)| (*k, arena.from_type(v)))
                            .collect()
                    };
                    self.entity_registry.monomorph_cache.insert(
                        key.clone(),
                        MonomorphInstance {
                            original_name: name_id,
                            mangled_name,
                            instance_id: id,
                            func_type: FunctionType {
                                params: concrete_params.into(),
                                return_type: Box::new(concrete_return.clone()),
                                is_closure: false,
                                params_id: None,
                                return_type_id: None,
                            },
                            substitutions,
                        },
                    );
                }

                // Record the call -> monomorph key mapping for codegen
                self.generic_calls.insert(expr.id, key);

                return Ok(self.type_to_id(&concrete_return));
            }

            // Check if it's a variable with a function type
            if let Some(LegacyType::Function(func_type)) = self.get_variable_type(*sym) {
                // Calling a function-typed variable - conservatively mark side effects
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(self.type_to_id(&func_type.return_type));
            }

            // Check if it's a variable with a functional interface type
            if let Some(LegacyType::Nominal(NominalType::Interface(iface))) =
                self.get_variable_type(*sym)
                && let Some(func_type) =
                    self.get_functional_interface_type_by_type_def_id(iface.type_def_id)
            {
                // Calling a functional interface - treat like a closure call
                if self.in_lambda() {
                    self.mark_lambda_has_side_effects();
                }
                self.check_call_args(
                    &call.args,
                    &func_type.params,
                    expr.span,
                    true, // with_inference
                    interner,
                )?;
                return Ok(self.type_to_id(&func_type.return_type));
            }

            // Check if it's a known builtin function
            let name = interner.resolve(*sym);
            if name == "println" || name == "print_char" || name == "flush" || name == "print" {
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
            if let Some(var_ty) = self.get_variable_type(*sym) {
                let ty = self.type_display(&var_ty);
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

            // Unknown identifier - might be an undefined function
            // (will be caught by codegen or other checks)
            for arg in &call.args {
                self.check_expr(arg, interner)?;
            }
            return Ok(ArenaTypeId::VOID);
        }

        // Non-identifier callee (e.g., a lambda expression being called directly)
        let callee_ty_id = self.check_expr(&call.callee, interner)?;

        // Use arena.unwrap_function to check if callable (avoids LegacyType)
        let func_info = self
            .type_arena
            .borrow()
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

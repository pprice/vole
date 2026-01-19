use super::super::*;
use crate::identity::{NameId, Namer};
use crate::sema::type_arena::TypeId as ArenaTypeId;
use std::collections::HashMap;

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
                return self.check_call_args_id(
                    &call.args,
                    &func_type.params_id,
                    func_type.return_type_id,
                    expr.span,
                    interner,
                );
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
                // Convert std HashMap to hashbrown HashMap for arena.substitute
                let subs_hashbrown: hashbrown::HashMap<_, _> =
                    inferred_id.iter().map(|(&k, &v)| (k, v)).collect();
                let (concrete_param_ids, concrete_return_id) = {
                    let mut arena = self.type_arena.borrow_mut();
                    // Substitute all types using TypeId-based substitutions directly
                    let param_ids: Vec<_> = generic_def
                        .param_types
                        .iter()
                        .map(|&t| arena.substitute(t, &subs_hashbrown))
                        .collect();
                    let return_id = arena.substitute(generic_def.return_type, &subs_hashbrown);
                    (param_ids, return_id)
                };

                // Check arg count
                if call.args.len() != concrete_param_ids.len() {
                    self.add_wrong_arg_count(concrete_param_ids.len(), call.args.len(), expr.span);
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
                let type_keys = type_args_id
                    .iter()
                    .map(|&id| self.type_key_for_id(id))
                    .collect();
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
                    // Use inferred_id directly as substitutions (already TypeId-based)
                    // MonomorphInstance uses std HashMap
                    let substitutions: HashMap<NameId, ArenaTypeId> = inferred_id.clone();
                    let func_type = FunctionType::from_ids(
                        &concrete_param_ids,
                        concrete_return_id,
                        false,
                        &self.type_arena.borrow(),
                    );
                    self.entity_registry.monomorph_cache.insert(
                        key.clone(),
                        MonomorphInstance {
                            original_name: name_id,
                            mangled_name,
                            instance_id: id,
                            func_type,
                            substitutions,
                        },
                    );
                }

                // Record the call -> monomorph key mapping for codegen
                self.generic_calls.insert(expr.id, key);

                return Ok(concrete_return_id);
            }

            // Check if it's a variable with a function type (using TypeId path)
            if let Some(var_type_id) = self.get_variable_type_id(*sym) {
                let arena = self.type_arena.borrow();
                if let Some((params, ret, _is_closure)) = arena.unwrap_function(var_type_id) {
                    let params = params.clone();
                    drop(arena);
                    // Calling a function-typed variable - conservatively mark side effects
                    if self.in_lambda() {
                        self.mark_lambda_has_side_effects();
                    }
                    return self.check_call_args_id(&call.args, &params, ret, expr.span, interner);
                }
                // Check if it's a variable with a functional interface type
                if let Some((type_def_id, _type_args)) = arena.unwrap_interface(var_type_id) {
                    drop(arena);
                    if let Some(func_type) =
                        self.get_functional_interface_type_by_type_def_id(type_def_id)
                    {
                        // Calling a functional interface - treat like a closure call
                        if self.in_lambda() {
                            self.mark_lambda_has_side_effects();
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

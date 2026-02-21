// src/sema/analyzer/lambda.rs

use super::*;
use crate::generic::{TypeParamInfo, TypeParamVariance};
use crate::type_arena::TypeId as ArenaTypeId;
use vole_frontend::LambdaParam;

impl Analyzer {
    /// Analyze a lambda expression, optionally with an expected function type for inference.
    /// The `node_id` is the NodeId of the parent Expr containing this lambda.
    pub(crate) fn analyze_lambda(
        &mut self,
        lambda: &LambdaExpr,
        node_id: NodeId,
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> ArenaTypeId {
        // Push capture analysis stacks and side effects flag
        self.lambda.captures.push(FxHashMap::default());
        self.lambda.locals.push(HashSet::new());
        self.lambda.side_effects.push(false);

        // Build type param scope for generic lambdas
        let builtin_mod = self.name_table_mut().builtin_module();
        let type_params: Vec<TypeParamInfo> = lambda
            .type_params
            .iter()
            .map(|tp| {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self
                    .name_table_mut()
                    .intern_raw(builtin_mod, &[tp_name_str]);
                TypeParamInfo {
                    name: tp.name,
                    name_id: tp_name_id,
                    constraint: None, // Lambdas don't support constraints yet
                    type_param_id: None,
                    variance: TypeParamVariance::default(),
                }
            })
            .collect();

        // Push type params to stack if any
        if !type_params.is_empty() {
            self.env.type_param_stack.push(type_params.clone());
        }

        // Validate default parameter ordering and calculate required_params
        // Note: required_params is used for validation here; the actual value is recalculated
        // when storing lambda_variables since we need it at that point
        let _required_params = self.validate_lambda_param_defaults(&lambda.params, interner);

        // Resolve parameter types as TypeIds
        let param_type_ids =
            self.resolve_lambda_param_types(&lambda.params, expected_type, interner);

        // Push new scope for lambda body
        self.push_scope();

        // Define parameters in scope and track as locals
        for (param, &ty_id) in lambda.params.iter().zip(param_type_ids.iter()) {
            self.env.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                    declaration_span: param.span,
                },
            );
            // Parameters are locals, not captures
            self.add_lambda_local(param.name);
        }

        // Type-check default expressions (after parameters are in scope)
        self.check_lambda_default_types(&lambda.params, &param_type_ids, interner);

        // Determine return type as TypeId
        let declared_return_id = lambda
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_id(t, interner));
        let expected_return_id = expected_type
            .map(|ft| ft.return_type_id)
            .filter(|&id| !id.is_invalid());

        // Analyze body and infer return type
        // Use the same function context mechanism as regular functions
        // This ensures fallible (raise/try) and generator (yield) contexts work
        let return_type_for_context = declared_return_id.or(expected_return_id);

        let body_type_id = match &lambda.body {
            FuncBody::Expr(expr) => {
                // For expression body, set up context if we have a declared/expected type
                let saved =
                    return_type_for_context.map(|ret_id| self.enter_function_context(ret_id));

                let ty_id = match self.check_expr(expr, interner) {
                    Ok(ty_id) => ty_id,
                    Err(_) => self.ty_invalid_traced_id("fallback"),
                };

                if let Some(saved) = saved {
                    self.exit_function_context(saved);
                }
                ty_id
            }
            FuncBody::Block(block) => {
                // For blocks, use the same function context as regular functions
                let (saved, inferring) = if let Some(ret_id) = return_type_for_context {
                    (self.enter_function_context(ret_id), false)
                } else {
                    (self.enter_function_context_inferring(), true)
                };

                let block_info = self.check_block(block, interner);

                let ret = if inferring {
                    // Use ReturnInfo to infer type from all return statements (creates union if needed)
                    match block_info {
                        Ok(info) => self.infer_return_type_from_info(&info),
                        Err(_) => ArenaTypeId::VOID,
                    }
                } else {
                    return_type_for_context.unwrap_or(ArenaTypeId::VOID)
                };

                self.exit_function_context(saved);
                ret
            }
        };

        // Restore outer scope
        self.pop_scope();

        // Pop type params if we pushed any
        if !type_params.is_empty() {
            self.env.type_param_stack.pop();
        }

        // Pop capture stacks, side effects flag, and store results in the side table
        self.lambda.locals.pop();
        let has_side_effects = self.lambda.side_effects.pop().unwrap_or(false);

        let capture_list = if let Some(captures) = self.lambda.captures.pop() {
            captures
                .into_values()
                .map(|info| Capture {
                    name: info.name,
                    is_mutable: info.is_mutable,
                    is_mutated: info.is_mutated,
                })
                .collect()
        } else {
            Vec::new()
        };
        self.results.node_map.set_lambda_analysis(
            node_id,
            crate::node_map::LambdaAnalysis {
                captures: capture_list,
                has_side_effects,
            },
        );

        // Determine final return type
        let return_type_id = declared_return_id
            .or(expected_return_id)
            .unwrap_or(body_type_id);

        // Build function type using arena.
        // Lambda expressions always use closure calling convention in codegen,
        // so we set is_closure=true regardless of whether they have captures.
        // This ensures type consistency between sema and codegen.
        self.type_arena_mut()
            .function(param_type_ids, return_type_id, true)
    }

    /// Check if a lambda has fully explicit type annotations and return its function type.
    ///
    /// This is used to pre-register recursive lambdas in scope before analyzing their body.
    /// Returns `Some(type_id)` only if ALL param types AND return type are explicitly specified.
    pub(crate) fn lambda_explicit_type_id(
        &mut self,
        lambda: &LambdaExpr,
        interner: &Interner,
    ) -> Option<ArenaTypeId> {
        // Must have explicit return type
        let return_type = lambda.return_type.as_ref()?;

        // All params must have explicit types
        let mut param_type_ids = Vec::with_capacity(lambda.params.len());
        for param in &lambda.params {
            let ty = param.ty.as_ref()?;
            param_type_ids.push(self.resolve_type_id(ty, interner));
        }

        let return_type_id = self.resolve_type_id(return_type, interner);

        // Build function type (assume closure since this is a lambda)
        Some(
            self.type_arena_mut()
                .function(param_type_ids, return_type_id, true),
        )
    }

    /// Validate lambda parameter defaults ordering.
    /// Returns the number of required parameters (those without defaults).
    fn validate_lambda_param_defaults(
        &mut self,
        params: &[LambdaParam],
        interner: &Interner,
    ) -> usize {
        let (required_count, _) = validate_defaults(params, interner, |name, span| {
            self.add_error(
                SemanticError::DefaultParamNotLast {
                    name,
                    span: span.into(),
                },
                span,
            );
        });
        required_count
    }

    /// Type-check default expressions for lambda parameters.
    fn check_lambda_default_types(
        &mut self,
        params: &[LambdaParam],
        param_type_ids: &[ArenaTypeId],
        interner: &Interner,
    ) {
        for (param, &expected_type_id) in params.iter().zip(param_type_ids.iter()) {
            if let Some(default_expr) = &param.default_value {
                // Type-check the default expression
                match self.check_expr_expecting_id(default_expr, Some(expected_type_id), interner) {
                    Ok(default_type_id) => {
                        if !self.types_compatible_id(default_type_id, expected_type_id, interner) {
                            self.add_type_mismatch_id(
                                expected_type_id,
                                default_type_id,
                                default_expr.span,
                            );
                        }
                    }
                    Err(_) => {
                        // Error already recorded
                    }
                }
            }
        }
    }

    /// Resolve parameter types for a lambda expression, using explicit annotations,
    /// expected type inference, or reporting errors.
    fn resolve_lambda_param_types(
        &mut self,
        params: &[LambdaParam],
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> Vec<ArenaTypeId> {
        let mut param_type_ids = Vec::new();

        for (i, param) in params.iter().enumerate() {
            let ty_id = if let Some(type_expr) = &param.ty {
                // Explicit type annotation
                self.resolve_type_id(type_expr, interner)
            } else if let Some(expected) = expected_type {
                // Infer from expected type - use params_id directly
                if i < expected.params_id.len() {
                    expected.params_id[i]
                } else {
                    self.add_error(
                        SemanticError::CannotInferLambdaParam {
                            name: interner.resolve(param.name).to_string(),
                            span: param.span.into(),
                        },
                        param.span,
                    );
                    ArenaTypeId::INVALID
                }
            } else {
                // No type info available
                self.add_error(
                    SemanticError::CannotInferLambdaParam {
                        name: interner.resolve(param.name).to_string(),
                        span: param.span.into(),
                    },
                    param.span,
                );
                ArenaTypeId::INVALID
            };
            param_type_ids.push(ty_id);
        }
        param_type_ids
    }

    /// Calculate required_params for a lambda (used when storing lambda info).
    pub(crate) fn lambda_required_params(lambda: &LambdaExpr) -> usize {
        lambda
            .params
            .iter()
            .take_while(|p| p.default_value.is_none())
            .count()
    }
}

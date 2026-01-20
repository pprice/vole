// src/sema/analyzer/lambda.rs

use super::*;
use crate::generic::{TypeParamInfo, TypeParamVariance};
use crate::type_arena::TypeId as ArenaTypeId;

impl Analyzer {
    /// Analyze a lambda expression, optionally with an expected function type for inference.
    pub(crate) fn analyze_lambda(
        &mut self,
        lambda: &LambdaExpr,
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> ArenaTypeId {
        // Push capture analysis stacks and side effects flag
        self.lambda_captures.push(HashMap::new());
        self.lambda_locals.push(HashSet::new());
        self.lambda_side_effects.push(false);

        // Build type param scope for generic lambdas
        let builtin_mod = self.name_table.builtin_module();
        let type_params: Vec<TypeParamInfo> = lambda
            .type_params
            .iter()
            .map(|tp| {
                let tp_name_str = interner.resolve(tp.name);
                let tp_name_id = self.name_table.intern_raw(builtin_mod, &[tp_name_str]);
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
            self.type_param_stack.push(type_params.clone());
        }

        // Resolve parameter types as TypeIds
        let mut param_type_ids = Vec::new();

        for (i, param) in lambda.params.iter().enumerate() {
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

        // Push new scope for lambda body
        let outer_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(outer_scope);

        // Define parameters in scope and track as locals
        for (param, &ty_id) in lambda.params.iter().zip(param_type_ids.iter()) {
            self.scope.define(
                param.name,
                Variable {
                    ty: ty_id,
                    mutable: false,
                },
            );
            // Parameters are locals, not captures
            self.add_lambda_local(param.name);
        }

        // Determine return type as TypeId
        let declared_return_id = lambda
            .return_type
            .as_ref()
            .map(|t| self.resolve_type_id(t, interner));
        let expected_return_id = expected_type.map(|ft| ft.return_type_id);

        // Analyze body and infer return type
        // Use the same function context mechanism as regular functions
        // This ensures fallible (raise/try) and generator (yield) contexts work
        let return_type_for_context = declared_return_id.or(expected_return_id);

        let body_type_id = match &lambda.body {
            LambdaBody::Expr(expr) => {
                // For expression body, set up context if we have a declared/expected type
                let saved = if let Some(ret_id) = return_type_for_context {
                    Some(self.enter_function_context(ret_id))
                } else {
                    None
                };

                let ty_id = match self.check_expr(expr, interner) {
                    Ok(ty_id) => ty_id,
                    Err(_) => self.ty_invalid_traced_id("fallback"),
                };

                if let Some(saved) = saved {
                    self.exit_function_context(saved);
                }
                ty_id
            }
            LambdaBody::Block(block) => {
                // For blocks, use the same function context as regular functions
                let (saved, inferring) = if let Some(ret_id) = return_type_for_context {
                    (self.enter_function_context(ret_id), false)
                } else {
                    (self.enter_function_context_inferring(), true)
                };

                let _ = self.check_block(block, interner);

                let ret = if inferring {
                    self.current_function_return
                        .unwrap_or(ArenaTypeId::VOID)
                } else {
                    return_type_for_context.unwrap_or(ArenaTypeId::VOID)
                };

                self.exit_function_context(saved);
                ret
            }
        };

        // Restore outer scope
        if let Some(parent) = std::mem::take(&mut self.scope).into_parent() {
            self.scope = parent;
        }

        // Pop type params if we pushed any
        if !type_params.is_empty() {
            self.type_param_stack.pop();
        }

        // Pop capture stacks, side effects flag, and store results in the lambda
        self.lambda_locals.pop();
        let has_side_effects = self.lambda_side_effects.pop().unwrap_or(false);
        lambda.has_side_effects.set(has_side_effects);

        let has_captures = if let Some(captures) = self.lambda_captures.pop() {
            let capture_list: Vec<Capture> = captures
                .into_values()
                .map(|info| Capture {
                    name: info.name,
                    is_mutable: info.is_mutable,
                    is_mutated: info.is_mutated,
                })
                .collect();
            let has_captures = !capture_list.is_empty();
            *lambda.captures.borrow_mut() = capture_list;
            has_captures
        } else {
            false
        };

        // Determine final return type
        let return_type_id = declared_return_id
            .or(expected_return_id)
            .unwrap_or(body_type_id);

        // Build function type using arena
        self.type_arena
            .borrow_mut()
            .function(param_type_ids, return_type_id, has_captures)
    }
}

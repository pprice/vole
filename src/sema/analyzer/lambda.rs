// src/sema/analyzer/lambda.rs

use super::*;
use crate::sema::generic::{TypeParamInfo, TypeParamVariance};
use crate::sema::types::LegacyType;

impl Analyzer {
    /// Analyze a lambda expression, optionally with an expected function type for inference
    pub(crate) fn analyze_lambda(
        &mut self,
        lambda: &LambdaExpr,
        expected_type: Option<&FunctionType>,
        interner: &Interner,
    ) -> LegacyType {
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

        // Resolve parameter types
        let mut param_types = Vec::new();

        for (i, param) in lambda.params.iter().enumerate() {
            let ty = if let Some(type_expr) = &param.ty {
                // Explicit type annotation
                self.resolve_type(type_expr, interner)
            } else if let Some(expected) = expected_type {
                // Infer from expected type
                if i < expected.params.len() {
                    expected.params[i].clone()
                } else {
                    self.add_error(
                        SemanticError::CannotInferLambdaParam {
                            name: interner.resolve(param.name).to_string(),
                            span: param.span.into(),
                        },
                        param.span,
                    );
                    self.ty_invalid()
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
                self.ty_invalid()
            };
            param_types.push(ty);
        }

        // Push new scope for lambda body
        let outer_scope = std::mem::take(&mut self.scope);
        self.scope = Scope::with_parent(outer_scope);

        // Define parameters in scope and track as locals
        for (param, ty) in lambda.params.iter().zip(param_types.iter()) {
            let ty_id = self.type_arena.borrow_mut().from_type(ty);
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

        // Determine return type
        let declared_return = lambda
            .return_type
            .as_ref()
            .map(|t| self.resolve_type(t, interner));
        let expected_return = expected_type.map(|ft| (*ft.return_type).clone());

        // Analyze body and infer return type
        let body_type = match &lambda.body {
            LambdaBody::Expr(expr) => {
                // For expression body, analyze and use as return type
                match self.check_expr(expr, interner) {
                    Ok(ty_id) => self.id_to_type(ty_id),
                    Err(_) => self.ty_invalid_traced("fallback"),
                }
            }
            LambdaBody::Block(block) => {
                // For blocks, set up return type context
                let old_return = self.current_function_return.take();
                // Convert LegacyType to ArenaTypeId for storage
                let return_type = declared_return.clone().or(expected_return.clone());
                self.current_function_return =
                    return_type.map(|ty| self.type_arena.borrow_mut().from_type(&ty));

                let _ = self.check_block(block, interner);

                // Convert back to LegacyType for return
                let ret = self
                    .current_function_return
                    .take()
                    .map(|ty| self.type_arena.borrow().to_type(ty))
                    .unwrap_or(LegacyType::Void);
                self.current_function_return = old_return;
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
        let return_type = declared_return.or(expected_return).unwrap_or(body_type);

        LegacyType::Function(FunctionType {
            params: param_types.into(),
            return_type: Box::new(return_type),
            is_closure: has_captures,
            params_id: None,
            return_type_id: None,
        })
    }
}

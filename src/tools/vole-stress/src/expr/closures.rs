//! Lambda / closure expression generation.

use rand::Rng;

use super::{ExprContext, ExprGenerator, is_capturable_type};
use crate::symbols::{ParamInfo, PrimitiveType, TypeInfo};

impl<'a, R: Rng> ExprGenerator<'a, R> {
    pub fn generate_lambda(
        &mut self,
        param_types: &[TypeInfo],
        return_type: &TypeInfo,
        ctx: &ExprContext,
        depth: usize,
    ) -> String {
        // Generate parameter names
        let params: Vec<String> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("p{}: {}", i, ty.to_vole_syntax(ctx.table)))
            .collect();

        // Create a new context with the lambda parameters
        let lambda_params: Vec<ParamInfo> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| ParamInfo {
                name: format!("p{}", i),
                param_type: ty.clone(),
            })
            .collect();

        // Optionally capture outer scope variables so the closure body can
        // reference them.  Only primitive-typed variables are captured to
        // avoid complex type interactions.
        let captured_locals: Vec<(String, TypeInfo)> = if self.config.closure_capture_probability
            > 0.0
            && self.rng.gen_bool(self.config.closure_capture_probability)
        {
            let mut captures = Vec::new();
            for (name, ty) in ctx.locals {
                if is_capturable_type(ty) {
                    captures.push((name.clone(), ty.clone()));
                }
            }
            for param in ctx.params {
                if is_capturable_type(&param.param_type) {
                    captures.push((param.name.clone(), param.param_type.clone()));
                }
            }
            captures
        } else {
            Vec::new()
        };

        let lambda_ctx = ExprContext::new(&lambda_params, &captured_locals, ctx.table);

        let return_annotation = match return_type {
            TypeInfo::Void => String::new(),
            _ => format!(" -> {}", return_type.to_vole_syntax(ctx.table)),
        };

        // ~20% chance: multiline block body (only for non-void, primitive return types)
        let use_block_body =
            matches!(return_type, TypeInfo::Primitive(_)) && depth < 2 && self.rng.gen_bool(0.20);

        if use_block_body {
            self.generate_lambda_block_body(
                &lambda_params,
                return_type,
                &lambda_ctx,
                depth,
                &params,
                &return_annotation,
            )
        } else {
            // Expression body: (params) -> T => expr
            let body = self.generate(return_type, &lambda_ctx, depth + 1);
            format!("({}){} => {}", params.join(", "), return_annotation, body)
        }
    }

    fn generate_lambda_block_body(
        &mut self,
        lambda_params: &[ParamInfo],
        return_type: &TypeInfo,
        lambda_ctx: &ExprContext,
        depth: usize,
        params: &[String],
        return_annotation: &str,
    ) -> String {
        let use_early_return = self.rng.gen_bool(0.4);

        if use_early_return {
            self.generate_lambda_early_return(
                lambda_params,
                return_type,
                lambda_ctx,
                depth,
                params,
                return_annotation,
            )
        } else {
            self.generate_lambda_let_return(
                return_type,
                lambda_ctx,
                depth,
                params,
                return_annotation,
            )
        }
    }

    /// Block body with early return:
    /// `(params) -> T => { if cond { return val1 }; return val2 }`
    fn generate_lambda_early_return(
        &mut self,
        lambda_params: &[ParamInfo],
        return_type: &TypeInfo,
        lambda_ctx: &ExprContext,
        depth: usize,
        params: &[String],
        return_annotation: &str,
    ) -> String {
        let early_val = self.generate(return_type, lambda_ctx, depth + 1);
        let fallback_val = self.generate(return_type, lambda_ctx, depth + 1);
        // Generate a simple boolean condition using a parameter if available
        let cond = if !lambda_params.is_empty() {
            let p = &lambda_params[0];
            match &p.param_type {
                TypeInfo::Primitive(PrimitiveType::I64) => format!("{} > 0", p.name),
                TypeInfo::Primitive(PrimitiveType::I32) => format!("{} > 0_i32", p.name),
                TypeInfo::Primitive(PrimitiveType::Bool) => p.name.clone(),
                TypeInfo::Primitive(PrimitiveType::F64) => format!("{} > 0.0", p.name),
                TypeInfo::Primitive(PrimitiveType::String) => {
                    format!("{}.length() > 0", p.name)
                }
                _ => "true".to_string(),
            }
        } else {
            "true".to_string()
        };
        format!(
            "({}){} => {{\n    if {} {{\n        return {}\n    }}\n    return {}\n}}",
            params.join(", "),
            return_annotation,
            cond,
            early_val,
            fallback_val
        )
    }

    /// Block body: `(params) -> T => { let tmp = expr; return tmp op expr }`
    fn generate_lambda_let_return(
        &mut self,
        return_type: &TypeInfo,
        lambda_ctx: &ExprContext,
        depth: usize,
        params: &[String],
        return_annotation: &str,
    ) -> String {
        let inner_expr = self.generate(return_type, lambda_ctx, depth + 1);
        let tmp_name = format!("_t{}", self.rng.gen_range(0..100));
        let final_expr = match return_type {
            TypeInfo::Primitive(PrimitiveType::I64) => {
                format!("{} + 0", tmp_name)
            }
            TypeInfo::Primitive(PrimitiveType::I32) => {
                format!("{} + 0_i32", tmp_name)
            }
            TypeInfo::Primitive(PrimitiveType::Bool) => tmp_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String) => tmp_name.clone(),
            TypeInfo::Primitive(PrimitiveType::F64) => {
                format!("{} + 0.0", tmp_name)
            }
            _ => tmp_name.clone(),
        };
        format!(
            "({}){} => {{\n    let {} = {}\n    return {}\n}}",
            params.join(", "),
            return_annotation,
            tmp_name,
            inner_expr,
            final_expr
        )
    }
}

//! Rule: lambda expression.
//!
//! Generates lambda/closure expressions for `Function` types:
//! `(p0: T0, p1: T1) -> R => body`
//!
//! Supports expression bodies and block bodies with early return.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct LambdaExpr;

impl ExprRule for LambdaExpr {
    fn name(&self) -> &'static str {
        "lambda_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        let (param_types, return_type) = match expected_type {
            TypeInfo::Function {
                param_types,
                return_type,
            } => (param_types, return_type.as_ref()),
            _ => return None,
        };

        // Generate parameter names with type annotations
        let params: Vec<String> = param_types
            .iter()
            .enumerate()
            .map(|(i, ty)| format!("p{}: {}", i, ty.to_vole_syntax(scope.table)))
            .collect();

        let return_annotation = match return_type {
            TypeInfo::Void => String::new(),
            _ => format!(" -> {}", return_type.to_vole_syntax(scope.table)),
        };

        // Expression body: generate sub-expression of return type
        let body = emit.sub_expr(return_type, scope);
        Some(format!(
            "({}){} => {}",
            params.join(", "),
            return_annotation,
            body
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(
            rng,
            EMPTY_STMT,
            EMPTY_EXPR,
            resolved,
            crate::symbols::SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(LambdaExpr.name(), "lambda_expr");
    }

    #[test]
    fn returns_none_for_non_function() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = LambdaExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_lambda_for_function_type() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let fn_type = TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(PrimitiveType::I64)],
            return_type: Box::new(TypeInfo::Primitive(PrimitiveType::Bool)),
        };

        let result = LambdaExpr.generate(&scope, &mut emit, &params, &fn_type);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "expected lambda, got: {text}");
        assert!(text.contains("p0:"), "expected param, got: {text}");
    }
}

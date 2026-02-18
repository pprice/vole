//! Rule: closure result used in a string concatenation or interpolation.
//!
//! Creates a lambda `(a: i64) -> i64 => a * N + M`, invokes it with an
//! i64-typed variable from scope, and concatenates the result into a string
//! via either `.to_string()` concatenation or string interpolation.
//!
//! Variant A -- `.to_string()` concat:
//! ```vole
//! let f = (a: i64) -> i64 => a * 3 + 5
//! let result = "result=" + f(x).to_string()
//! ```
//!
//! Variant B -- string interpolation:
//! ```vole
//! let f = (a: i64) -> i64 => a * 3 + 5
//! let result = "result={f(x)}"
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureConcat;

impl StmtRule for ClosureConcat {
    fn name(&self) -> &'static str {
        "closure_concat"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find i64 variables in scope for the lambda argument
        let i64_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::I64)))
            .into_iter()
            .map(|v| v.name)
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..i64_vars.len());
        let arg_var = i64_vars[idx].clone();

        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        // Generate a simple lambda: (a: i64) -> i64 => a * N + M
        let mult = emit.random_in(1, 5);
        let add = emit.gen_range(0..11); // 0..=10

        let lambda_expr = format!("(a: i64) -> i64 => a * {} + {}", mult, add);
        let call_expr = format!("{}({})", fn_name, arg_var);

        // Pick variant: .to_string() concat or string interpolation
        let str_expr = if emit.gen_bool(0.5) {
            format!("\"result=\" + {}.to_string()", call_expr)
        } else {
            format!("\"result={{{}}}\"", call_expr)
        };

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let indent = emit.indent_str();
        Some(format!(
            "let {} = {}\n{}let {} = {}",
            fn_name, lambda_expr, indent, result_name, str_expr
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
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
        assert_eq!(ClosureConcat.name(), "closure_concat");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ClosureConcat
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_lambda_and_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureConcat.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        // Should have the lambda definition
        assert!(text.contains("(a: i64) -> i64 => a *"), "got: {text}");
        // Should have string result (either interpolation or concat)
        assert!(
            text.contains("result=") || text.contains("result{"),
            "got: {text}"
        );
    }

    #[test]
    fn adds_string_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ClosureConcat.generate(&mut scope, &mut emit, &params);
        // Should have added at least one string-typed local (result_name)
        let has_string = scope
            .locals
            .iter()
            .any(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)));
        assert!(has_string);
    }
}

//! Rule: closure result in string concatenation.
//!
//! Generates a lambda `(a: i64) -> i64 => a * N + M` then uses the result
//! in string concatenation: `"result=" + f(x).to_string()`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureResultConcat;

impl StmtRule for ClosureResultConcat {
    fn name(&self) -> &'static str {
        "closure_result_concat"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let arg_var = i64_vars[emit.gen_range(0..i64_vars.len())].clone();
        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        let mult = emit.random_in(1, 5);
        let add = emit.gen_range(0..11);

        let lambda_expr = format!("(a: i64) -> i64 => a * {} + {}", mult, add);
        let call_expr = format!("{}({})", fn_name, arg_var);

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

fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(param.name.clone());
        }
    }
    out
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(ClosureResultConcat.name(), "closure_result_concat");
    }

    #[test]
    fn generates_closure_concat() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ClosureResultConcat.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("=>"), "got: {text}");
    }
}

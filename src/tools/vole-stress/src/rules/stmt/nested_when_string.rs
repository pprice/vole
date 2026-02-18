//! Rule: nested when expression with string result.
//!
//! Generates `when { a > N => when { b > M => "both", _ => "b" }, _ => "a" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedWhenString;

impl StmtRule for NestedWhenString {
    fn name(&self) -> &'static str {
        "nested_when_string"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.len() < 2 {
            return None;
        }

        let var_a = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let var_b = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let name = scope.fresh_name();

        let thresh_a = emit.gen_i64_range(0, 10);
        let thresh_b = emit.gen_i64_range(0, 10);

        let strs = ["\"both_pos\"", "\"b_neg\"", "\"a_neg\""];

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    {} > {} => when {{\n        {} > {} => {}\n        _ => {}\n    }}\n    _ => {}\n}}",
            name, var_a, thresh_a, var_b, thresh_b, strs[0], strs[1], strs[2]
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
        assert_eq!(NestedWhenString.name(), "nested_when_string");
    }

    #[test]
    fn generates_nested_when() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("a".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedWhenString.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}

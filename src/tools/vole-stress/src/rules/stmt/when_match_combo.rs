//! Rule: when expression with match inside an arm.
//!
//! Generates `when { true => match x { 0 => "a", 1 => "b", _ => "c" }, _ => "d" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenMatchCombo;

impl StmtRule for WhenMatchCombo {
    fn name(&self) -> &'static str {
        "when_match_combo"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let name = scope.fresh_name();

        let match_val0 = emit.gen_range(0..6);
        let match_val1 = match_val0 + 1 + emit.gen_range(0..4);

        let strs = ["\"a\"", "\"b\"", "\"c\"", "\"d\"", "\"e\""];

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = when {{\n    true => match {} {{\n        {} => {}\n        {} => {}\n        _ => {}\n    }}\n    _ => {}\n}}",
            name, var, match_val0, strs[0], match_val1, strs[1], strs[2], strs[3],
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
        assert_eq!(WhenMatchCombo.name(), "when_match_combo");
    }

    #[test]
    fn generates_combo() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenMatchCombo.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains("match"), "got: {text}");
    }
}

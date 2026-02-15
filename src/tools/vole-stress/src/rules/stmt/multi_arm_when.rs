//! Rule: multi-arm when expression (4+ arms).
//!
//! Generates larger when expressions with many boolean condition arms,
//! testing the compiler's handling of when expressions at scale.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MultiArmWhen;

impl StmtRule for MultiArmWhen {
    fn name(&self) -> &'static str {
        "multi_arm_when"
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
        let num_arms = emit.random_in(4, 7);
        let indent = emit.indent_str();

        let mut arms = Vec::new();
        for i in 0..num_arms {
            let thresh = (i as i64) * 10;
            let result = emit.gen_i64_range(-20, 20);
            let op = [">", "<", ">="][emit.gen_range(0..3)];
            arms.push(format!(
                "{}    {} {} {} => {}",
                indent, var, op, thresh, result
            ));
        }
        let default_val = emit.gen_i64_range(-10, 10);
        arms.push(format!("{}    _ => {}", indent, default_val));

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            name,
            arms.join("\n"),
            indent,
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
        assert_eq!(MultiArmWhen.name(), "multi_arm_when");
    }

    #[test]
    fn generates_multi_arm() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MultiArmWhen.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}

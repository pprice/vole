//! Rule: when expression with f64 variable conditions.
//!
//! Generates `when { x > 1.0 => "big", x > 0.0 => "small", _ => "zero" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenF64Cond;

impl StmtRule for WhenF64Cond {
    fn name(&self) -> &'static str {
        "when_f64_cond"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let f64_vars = collect_f64_vars(scope);
        if f64_vars.is_empty() {
            return None;
        }

        let var = &f64_vars[emit.gen_range(0..f64_vars.len())];
        let name = scope.fresh_name();
        let thresholds = ["100.0", "10.0", "1.0", "0.0"];
        let labels = ["\"high\"", "\"medium\"", "\"low\"", "\"zero\""];

        let num_arms = emit.random_in(2, 3);
        let mut arms = Vec::new();
        for i in 0..num_arms {
            if i < thresholds.len() && i < labels.len() {
                arms.push(format!("{} > {} => {}", var, thresholds[i], labels[i]));
            }
        }
        arms.push(format!("_ => {}", labels[num_arms.min(labels.len() - 1)]));

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = when {{ {} }}", name, arms.join(", ")))
    }
}

fn collect_f64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::F64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::F64)) {
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
        assert_eq!(WhenF64Cond.name(), "when_f64_cond");
    }

    #[test]
    fn generates_when() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::F64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenF64Cond.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}

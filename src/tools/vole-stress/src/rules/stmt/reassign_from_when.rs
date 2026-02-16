//! Rule: reassignment from when expression.
//!
//! Generates `r = when { x > 3 => x * 2, _ => x }` targeting a mutable
//! i64 variable, testing when expressions as assignment sources.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ReassignFromWhen;

impl StmtRule for ReassignFromWhen {
    fn name(&self) -> &'static str {
        "reassign_from_when"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find mutable i64 variables (not protected)
        let mut_i64_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(name, ty, is_mut)| {
                *is_mut
                    && !scope.protected_vars.contains(name)
                    && matches!(ty, TypeInfo::Primitive(PrimitiveType::I64))
            })
            .map(|(name, _, _)| name.clone())
            .collect();

        if mut_i64_vars.is_empty() {
            return None;
        }

        // Find i64 variables for conditions
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.is_empty() {
            return None;
        }

        let target = &mut_i64_vars[emit.gen_range(0..mut_i64_vars.len())];
        let cond_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let thresh = emit.gen_i64_range(-10, 10);
        let op = [">", "<", ">="][emit.gen_range(0..3)];
        let val_true = emit.gen_i64_range(-20, 20);
        let val_false = emit.gen_i64_range(-20, 20);

        Some(format!(
            "{} = when {{ {} {} {} => {}, _ => {} }}",
            target, cond_var, op, thresh, val_true, val_false
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
        assert_eq!(ReassignFromWhen.name(), "reassign_from_when");
    }

    #[test]
    fn returns_none_without_mutable_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ReassignFromWhen
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_reassignment() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ReassignFromWhen.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(!text.starts_with("let"), "should not be a let: {text}");
    }
}

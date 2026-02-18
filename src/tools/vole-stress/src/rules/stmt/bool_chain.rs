//! Rule: complex boolean chain expression.
//!
//! Generates `(a > 0) && (b < 10) || !c` and similar,
//! mixing bool variables, comparisons, and boolean operators.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct BoolChain;

impl StmtRule for BoolChain {
    fn name(&self) -> &'static str {
        "bool_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let bool_vars = collect_bool_vars(scope);
        let i64_vars = collect_i64_vars(scope);

        if bool_vars.is_empty() && i64_vars.is_empty() {
            return None;
        }

        let name = scope.fresh_name();
        let num_parts = emit.random_in(2, 4);
        let mut parts = Vec::new();

        for _ in 0..num_parts {
            let part = match emit.gen_range(0..4) {
                0 if !bool_vars.is_empty() => bool_vars[emit.gen_range(0..bool_vars.len())].clone(),
                1 if !bool_vars.is_empty() => {
                    format!("!{}", bool_vars[emit.gen_range(0..bool_vars.len())])
                }
                2 if !i64_vars.is_empty() => {
                    let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
                    let n = emit.gen_i64_range(0, 10);
                    let op = [">", "<", "=="][emit.gen_range(0..3)];
                    format!("({} {} {})", var, op, n)
                }
                _ => if emit.gen_bool(0.5) { "true" } else { "false" }.to_string(),
            };
            parts.push(part);
        }

        let mut expr = parts[0].clone();
        for part in parts.iter().skip(1) {
            let op = if emit.gen_bool(0.6) { "&&" } else { "||" };
            expr = format!("({} {} {})", expr, op, part);
        }

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }
}

fn collect_bool_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            out.push(param.name.clone());
        }
    }
    out
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
        assert_eq!(BoolChain.name(), "bool_chain");
    }

    #[test]
    fn generates_chain() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::Bool), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BoolChain.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }
}

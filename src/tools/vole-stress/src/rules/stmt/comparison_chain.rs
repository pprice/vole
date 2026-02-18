//! Rule: comparison chain expression.
//!
//! Generates `(a > 0) == (b > 0)`, `(a != 0) && (b != 0)`, etc.
//! Tests boolean result comparison codegen.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ComparisonChain;

impl StmtRule for ComparisonChain {
    fn name(&self) -> &'static str {
        "comparison_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.len() < 2 {
            return None;
        }

        let name = scope.fresh_name();
        let a = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let b = &i64_vars[emit.gen_range(0..i64_vars.len())];

        let expr = match emit.gen_range(0..4) {
            0 => format!("({} > 0) == ({} > 0)", a, b),
            1 => format!("({} != 0) && ({} != 0)", a, b),
            2 => format!("({} >= 0) || ({} >= 0)", a, b),
            _ => {
                let n = emit.gen_i64_range(1, 10);
                format!("({} > {}) == ({} > {})", a, n, b, n)
            }
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
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
        assert_eq!(ComparisonChain.name(), "comparison_chain");
    }

    #[test]
    fn generates_comparison() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("a".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ComparisonChain.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }
}

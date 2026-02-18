//! Rule: boolean negation let-binding.
//!
//! Generates `!true`, `!false`, `!(x > 0)`, `!b`, `!(x == y)`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct BoolNegation;

impl StmtRule for BoolNegation {
    fn name(&self) -> &'static str {
        "bool_negation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let i64_vars = collect_typed_vars(scope, PrimitiveType::I64);
        let bool_vars = collect_typed_vars(scope, PrimitiveType::Bool);

        let expr = match emit.gen_range(0..5) {
            0 => "!true".to_string(),
            1 => "!false".to_string(),
            2 if !i64_vars.is_empty() => {
                let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
                let thresh = emit.gen_i64_range(-5, 10);
                format!("!({} > {})", var, thresh)
            }
            3 if !bool_vars.is_empty() => {
                let var = &bool_vars[emit.gen_range(0..bool_vars.len())];
                format!("!{}", var)
            }
            _ if i64_vars.len() >= 2 => {
                let v1 = &i64_vars[emit.gen_range(0..i64_vars.len())];
                let v2 = &i64_vars[emit.gen_range(0..i64_vars.len())];
                format!("!({} == {})", v1, v2)
            }
            _ => "!false".to_string(),
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }
}

fn collect_typed_vars(scope: &Scope, prim: PrimitiveType) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(p) if *p == prim) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(&param.param_type, TypeInfo::Primitive(p) if *p == prim) {
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
        assert_eq!(BoolNegation.name(), "bool_negation");
    }

    #[test]
    fn generates_negation() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BoolNegation.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("!"), "got: {text}");
    }
}

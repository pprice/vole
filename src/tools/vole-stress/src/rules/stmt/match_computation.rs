//! Rule: match with computed arm values.
//!
//! Finds at least two i64 variables in scope and generates a match where
//! each arm computes a result from a variable and a literal:
//! ```vole
//! let result = match x {
//!     0 => y + 3
//!     5 => y * 2
//!     _ => y - 1
//! }
//! ```

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchComputation;

impl StmtRule for MatchComputation {
    fn name(&self) -> &'static str {
        "match_computation"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.len() < 2 {
            return None;
        }

        let scrutinee_idx = emit.gen_range(0..i64_vars.len());
        let scrutinee = i64_vars[scrutinee_idx].clone();
        let name = scope.fresh_name();
        let indent = emit.indent_str();
        let num_arms = emit.random_in(2, 4);

        let mut arms = Vec::new();
        let mut used_values = HashSet::new();
        for _ in 0..num_arms {
            let mut val = emit.gen_i64_range(-5, 10);
            while used_values.contains(&val) {
                val = emit.gen_i64_range(-5, 10);
            }
            used_values.insert(val);

            let v1_idx = emit.gen_range(0..i64_vars.len());
            let v1 = &i64_vars[v1_idx];
            let op = pick_op(emit);
            let operand = emit.random_in(1, 10);
            arms.push(format!(
                "{}    {} => {} {} {}",
                indent, val, v1, op, operand
            ));
        }

        // Default arm with computation
        let v_default_idx = emit.gen_range(0..i64_vars.len());
        let v_default = &i64_vars[v_default_idx];
        let default_op = pick_op(emit);
        let default_operand = emit.random_in(1, 5);
        arms.push(format!(
            "{}    _ => {} {} {}",
            indent, v_default, default_op, default_operand
        ));

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            name,
            scrutinee,
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

fn pick_op(emit: &mut Emit) -> &'static str {
    match emit.gen_range(0..3) {
        0 => "+",
        1 => "-",
        _ => "*",
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
        assert_eq!(MatchComputation.name(), "match_computation");
    }

    #[test]
    fn returns_none_with_fewer_than_two_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchComputation
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_two_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchComputation.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match "), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }
}

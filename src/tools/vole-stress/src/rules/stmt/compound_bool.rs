//! Rule: compound boolean from numeric comparisons.
//!
//! Generates compound boolean expressions combining i64 variable comparisons:
//! ```vole
//! let b = x > 5 && y < 10
//! let b = x > y || y <= -3
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct CompoundBool;

impl StmtRule for CompoundBool {
    fn name(&self) -> &'static str {
        "compound_bool"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        if i64_vars.len() < 2 {
            return None;
        }

        let result_name = scope.fresh_name();
        let ops = [">", "<", ">=", "<=", "==", "!="];
        let logic = ["&&", "||"];

        let var1 = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let var2 = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let op1 = ops[emit.gen_range(0..ops.len())];
        let op2 = ops[emit.gen_range(0..ops.len())];
        let logic_op = logic[emit.gen_range(0..logic.len())];
        let thresh1 = emit.gen_i64_range(-20, 20);
        let thresh2 = emit.gen_i64_range(-20, 20);

        let expr = if emit.gen_bool(0.3) {
            format!(
                "{} {} {} {} {} {} {}",
                var1, op1, var2, logic_op, var2, op2, thresh2
            )
        } else {
            format!(
                "{} {} {} {} {} {} {}",
                var1, op1, thresh1, logic_op, var2, op2, thresh2
            )
        };

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );
        Some(format!("let {} = {}", result_name, expr))
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
        assert_eq!(CompoundBool.name(), "compound_bool");
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
            CompoundBool
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_compound_bool() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = CompoundBool.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("&&") || text.contains("||"), "got: {text}");
    }
}

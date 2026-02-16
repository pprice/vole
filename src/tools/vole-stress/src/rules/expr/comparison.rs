//! Rule: comparison expression.
//!
//! Generates a comparison between two numeric sub-expressions using one of
//! `==`, `!=`, `<`, `>`, `<=`, `>=`. Result type is always `bool`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct Comparison;

impl ExprRule for Comparison {
    fn name(&self) -> &'static str {
        "comparison"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.25)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Only produces bool
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let prim = match emit.gen_range(0..3_usize) {
            0 => PrimitiveType::I32,
            1 => PrimitiveType::I64,
            _ => PrimitiveType::F64,
        };
        let ty = TypeInfo::Primitive(prim);
        let left = emit.sub_expr(&ty, scope);
        let right = emit.sub_expr(&ty, scope);

        let op = match emit.gen_range(0..6_usize) {
            0 => "==",
            1 => "!=",
            2 => "<",
            3 => ">",
            4 => "<=",
            _ => ">=",
        };

        Some(format!("({} {} {})", left, op, right))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(Comparison.name(), "comparison");
    }

    #[test]
    fn returns_none_for_non_bool() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = Comparison.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_comparison_for_bool() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = Comparison.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with('(') && text.ends_with(')'), "got: {text}");
    }
}

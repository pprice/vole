//! Rule: f64 comparison edge cases.
//!
//! Generates `0.0 == 0.0`, `1.0 != 2.0`, `var >= var2`, etc.
//! Tests floating-point equality semantics.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct F64ComparisonEdge;

impl StmtRule for F64ComparisonEdge {
    fn name(&self) -> &'static str {
        "f64_comparison_edge"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::Bool),
            false,
        );

        let f64_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(n, ty, _)| {
                *n != name && matches!(ty, TypeInfo::Primitive(PrimitiveType::F64))
            })
            .map(|(n, _, _)| n.clone())
            .collect();

        let expr = match emit.gen_range(0..5) {
            0 => "0.0 == 0.0".to_string(),
            1 => "1.0 != 2.0".to_string(),
            2 => "0.0 < 1.0".to_string(),
            3 if f64_vars.len() >= 2 => {
                format!("{} >= {}", f64_vars[0], f64_vars[1])
            }
            3 => "3.14 > 2.71".to_string(),
            _ => "1.0 <= 1.0".to_string(),
        };

        Some(format!("let {} = {}", name, expr))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(F64ComparisonEdge.name(), "f64_comparison_edge");
    }

    #[test]
    fn generates_comparison() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = F64ComparisonEdge.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
    }
}

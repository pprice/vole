//! Rule: f64 literal arithmetic operations.
//!
//! Generates `let x = 1.5 + 2.3`, `let x = var / 2.0`, etc.
//! Tests floating-point codegen paths with known-safe values.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct F64LiteralOps;

impl StmtRule for F64LiteralOps {
    fn name(&self) -> &'static str {
        "f64_literal_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let literals = ["0.0", "1.0", "0.5", "2.5", "3.14", "100.0", "0.1", "99.9"];
        let a = literals[emit.gen_range(0..literals.len())];
        let b = literals[emit.gen_range(0..literals.len())];

        let f64_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::F64)))
            .map(|(name, _, _)| name.clone())
            .collect();

        match emit.gen_range(0..5) {
            0 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                Some(format!("let {} = {} + {}", name, a, b))
            }
            1 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                Some(format!("let {} = {} * {}", name, a, b))
            }
            2 => {
                let lhs = f64_vars.first().map(|v| v.as_str()).unwrap_or(a);
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                Some(format!("let {} = {} - {}", name, lhs, b))
            }
            3 => {
                let lhs = f64_vars.first().map(|v| v.as_str()).unwrap_or(a);
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = {} > {}", name, lhs, b))
            }
            _ => {
                let divisors = ["1.0", "2.0", "0.5", "3.14", "10.0"];
                let d = divisors[emit.gen_range(0..divisors.len())];
                let lhs = f64_vars.first().map(|v| v.as_str()).unwrap_or(a);
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::F64), false);
                Some(format!("let {} = {} / {}", name, lhs, d))
            }
        }
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
        assert_eq!(F64LiteralOps.name(), "f64_literal_ops");
    }

    #[test]
    fn generates_f64_op() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = F64LiteralOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
    }
}

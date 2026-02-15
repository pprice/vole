//! Rule: for-loop building a string with interpolation concatenation.
//!
//! Produces a pattern like:
//! ```vole
//! let mut s = ""
//! for i in 0..N { s = s + "item {i} " }
//! ```
//! Tests string interpolation inside a loop body with mutable string building.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct InterpolationConcat;

impl StmtRule for InterpolationConcat {
    fn name(&self) -> &'static str {
        "interpolation_concat"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let acc_name = scope.fresh_name();
        let iter_name = scope.fresh_name();
        let n = emit.random_in(2, 5);

        let prefixes = ["item", "val", "x", "n", "elem"];
        let prefix = prefixes[emit.gen_range(0..prefixes.len())];

        // Protect accumulator
        scope.protected_vars.push(acc_name.clone());

        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let mut {} = \"\"\n\
             for {} in 0..{} {{\n\
                 {} = {} + \"{}={{{}}} \"\n\
             }}",
            acc_name, iter_name, n, acc_name, acc_name, prefix, iter_name
        ))
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
    fn generates_for_loop_with_interpolation() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = InterpolationConcat.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let mut "));
        assert!(text.contains("for "));
        assert!(text.contains("0.."));
    }

    #[test]
    fn protects_accumulator() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        InterpolationConcat.generate(&mut scope, &mut emit, &params);
        assert!(!scope.protected_vars.is_empty());
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(InterpolationConcat.name(), "interpolation_concat");
    }
}

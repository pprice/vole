//! Rule: repeat literal fixed-size array.
//!
//! Generates `let arr: [T; N] = [val; N]` for various types.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct RepeatLiteral;

impl StmtRule for RepeatLiteral {
    fn name(&self) -> &'static str {
        "repeat_literal"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let count = emit.random_in(2, 8);

        let (type_str, val) = match emit.gen_range(0..4) {
            0 => ("i64", format!("{}", emit.gen_i64_range(-50, 50))),
            1 => ("i32", format!("{}_i32", emit.gen_i64_range(-50, 50))),
            2 => {
                let strs = ["\"hello\"", "\"test\"", "\"\"", "\"vole\""];
                ("string", strs[emit.gen_range(0..strs.len())].to_string())
            }
            _ => {
                let b = if emit.gen_bool(0.5) { "true" } else { "false" };
                ("bool", b.to_string())
            }
        };

        // Don't add to scope.locals -- fixed-size arrays lack .iter()/.length()
        Some(format!(
            "let {}: [{}; {}] = [{}; {}]",
            name, type_str, count, val, count
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
        assert_eq!(RepeatLiteral.name(), "repeat_literal");
    }

    #[test]
    fn generates_repeat_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RepeatLiteral.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("; "), "got: {text}");
    }
}

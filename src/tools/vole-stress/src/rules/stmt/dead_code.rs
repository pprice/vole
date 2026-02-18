//! Rule: dead-code assertion.
//!
//! Generates an unreachable code block containing `assert(false)`:
//! ```vole
//! if false {
//!     assert(false)
//! }
//! ```
//! Tests the compiler's handling of unreachable code with assertions.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;

pub struct DeadCodeAssert;

impl StmtRule for DeadCodeAssert {
    fn name(&self) -> &'static str {
        "dead_code_assert"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, _scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let variant = emit.gen_range(0..3);
        let code = match variant {
            0 => "if false {\n    assert(false)\n}".to_string(),
            1 => "if true { } else {\n    assert(false)\n}".to_string(),
            _ => "if false {\n    assert(false)\n}".to_string(),
        };
        Some(code)
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
        assert_eq!(DeadCodeAssert.name(), "dead_code_assert");
    }

    #[test]
    fn generates_dead_code_block() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = DeadCodeAssert.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("assert(false)"), "got: {text}");
        assert!(
            text.contains("false") || text.contains("true"),
            "got: {text}"
        );
    }
}

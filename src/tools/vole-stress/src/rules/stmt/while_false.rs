//! Rule: while-false dead code.
//!
//! Generates a `while false` loop whose body should never execute:
//! ```vole
//! let mut v0 = 42
//! while false {
//!     v0 = 0
//! }
//! ```
//! Tests the compiler's handling of dead loops with mutation.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhileFalse;

impl StmtRule for WhileFalse {
    fn name(&self) -> &'static str {
        "while_false"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let indent = emit.indent_str();
        let var_name = scope.fresh_name();

        scope.add_local(
            var_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.protected_vars.push(var_name.clone());

        Some(format!(
            "var {} = 42\n{}while false {{\n{}    {} = 0\n{}}}",
            var_name, indent, indent, var_name, indent,
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
        assert_eq!(WhileFalse.name(), "while_false");
    }

    #[test]
    fn generates_while_false_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhileFalse.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("while false"), "got: {text}");
        assert!(text.contains("var"), "got: {text}");
    }

    #[test]
    fn adds_mutable_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        WhileFalse.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert!(scope.locals[0].2, "should be mutable");
    }
}

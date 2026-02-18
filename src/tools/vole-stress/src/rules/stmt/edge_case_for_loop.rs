//! Rule: zero-range or single-iteration for loop.
//!
//! Generates for loops over `0..0` (zero iterations) or `0..1` (single iteration),
//! exercising boundary conditions in range-based iteration.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EdgeCaseForLoop;

impl StmtRule for EdgeCaseForLoop {
    fn name(&self) -> &'static str {
        "edge_case_for_loop"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let iter_name = scope.fresh_name();
        let range = if emit.gen_bool(0.5) {
            "0..0" // zero iterations
        } else {
            "0..1" // single iteration
        };

        let body = scope.enter_scope(|inner| {
            inner.in_loop = true;
            inner.in_while_loop = false;
            inner.add_local(
                iter_name.clone(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );
            emit.block(inner, 1)
        });

        let indent = emit.indent_str();
        Some(format!(
            "for {} in {} {{\n{}\n{}}}",
            iter_name, range, body, indent
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
        assert_eq!(EdgeCaseForLoop.name(), "edge_case_for_loop");
    }

    #[test]
    fn generates_for_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EdgeCaseForLoop.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for "), "got: {text}");
        assert!(text.contains("0.."), "got: {text}");
    }
}

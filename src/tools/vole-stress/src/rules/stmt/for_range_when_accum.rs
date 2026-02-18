//! Rule: range for-loop with when body accumulating strings.
//!
//! Generates `let mut s = ""; for i in 0..5 { s = s + when { i > 2 => "hi", _ => "lo" } }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForRangeWhenAccum;

impl StmtRule for ForRangeWhenAccum {
    fn name(&self) -> &'static str {
        "for_range_when_accum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let acc_name = scope.fresh_name();
        let iter_var = scope.fresh_name();
        let n = emit.random_in(3, 6);
        let threshold = emit.gen_range(1..n);

        scope.protected_vars.push(acc_name.clone());
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        let indent = emit.indent_str();
        Some(format!(
            "let mut {} = \"\"\n{}for {} in 0..{} {{\n{}    {} = {} + when {{ {} > {} => \"hi\", _ => \"lo\" }}\n{}}}",
            acc_name, indent, iter_var, n, indent, acc_name, acc_name, iter_var, threshold, indent
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
        assert_eq!(ForRangeWhenAccum.name(), "for_range_when_accum");
    }

    #[test]
    fn generates_for_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForRangeWhenAccum.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("for"), "got: {text}");
        assert!(text.contains("when"), "got: {text}");
    }
}

//! Rule: for-in loop over split string result.
//!
//! Generates a split+collect followed by a for loop accumulating string lengths.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SplitForLoop;

impl StmtRule for SplitForLoop {
    fn name(&self) -> &'static str {
        "split_for_loop"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let parts_name = scope.fresh_name();
        let iter_name = scope.fresh_name();
        let acc_name = scope.fresh_name();

        let words: Vec<&str> = vec!["alpha", "beta", "gamma", "delta"];
        let num_words = emit.random_in(2, 4);
        let selected: Vec<&str> = words[..num_words].to_vec();
        let input = selected.join(",");

        scope.add_local(
            parts_name.clone(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            false,
        );
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::I64),
            true,
        );
        scope.protected_vars.push(parts_name.clone());
        scope.protected_vars.push(acc_name.clone());

        let indent = emit.indent_str();

        Some(format!(
            "let {} = \"{}\".split(\",\").collect()\n\
             {}let mut {} = 0\n\
             {}for {} in {}.iter() {{\n\
             {}    {} = {} + {}.length()\n\
             {}}}",
            parts_name,
            input,
            indent,
            acc_name,
            indent,
            iter_name,
            parts_name,
            indent,
            acc_name,
            acc_name,
            iter_name,
            indent,
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
    fn name_is_correct() {
        assert_eq!(SplitForLoop.name(), "split_for_loop");
    }

    #[test]
    fn generates_split_for() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SplitForLoop.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".split("), "got: {text}");
        assert!(text.contains("for"), "got: {text}");
    }
}

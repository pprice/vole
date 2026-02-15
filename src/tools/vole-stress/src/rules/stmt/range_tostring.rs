//! Rule: for-range building string via `.to_string()`.
//!
//! Produces a pattern like:
//! ```vole
//! let mut s = ""
//! for i in 0..N { s = s + i.to_string() }
//! ```
//! Tests `.to_string()` method dispatch on the loop variable combined with
//! mutable string accumulation.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct RangeTostring;

impl StmtRule for RangeTostring {
    fn name(&self) -> &'static str {
        "range_tostring"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let acc_name = scope.fresh_name();
        let iter_var = scope.fresh_name();
        let n = emit.random_in(2, 5);
        let indent = emit.indent_str();

        scope.protected_vars.push(acc_name.clone());
        scope.add_local(
            acc_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let mut {} = \"\"\n\
             {}for {} in 0..{} {{\n\
             {}    {} = {} + {}.to_string()\n\
             {}}}",
            acc_name, indent, iter_var, n, indent, acc_name, acc_name, iter_var, indent,
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
    fn generates_for_loop_with_tostring() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RangeTostring.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let mut "));
        assert!(text.contains(".to_string()"));
        assert!(text.contains("for "));
    }

    #[test]
    fn protects_accumulator() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        RangeTostring.generate(&mut scope, &mut emit, &params);
        assert!(!scope.protected_vars.is_empty());
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(RangeTostring.name(), "range_tostring");
    }
}

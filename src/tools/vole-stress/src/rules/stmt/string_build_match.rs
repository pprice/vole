//! Rule: for-loop string build with match expression.
//!
//! Produces a pattern like:
//! ```vole
//! let mut s = ""
//! for i in 0..N {
//!     s = s + match i {
//!         0 => "a"
//!         1 => "b"
//!         _ => "c"
//!     }
//! }
//! ```
//! Tests match expressions inside loop bodies with mutable string building.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringBuildMatch;

impl StmtRule for StringBuildMatch {
    fn name(&self) -> &'static str {
        "string_build_match"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let s_name = scope.fresh_name();
        let i_name = scope.fresh_name();
        let n = emit.random_in(2, 5);
        let indent = emit.indent_str();
        let body_indent = format!("{}    ", indent);
        let match_indent = format!("{}        ", indent);

        let suffixes: &[&str] = &["a", "b", "c", "d", "x"];
        let num_arms = emit.random_in(2, 3).min(n);
        let mut arms = Vec::new();
        for j in 0..num_arms {
            arms.push(format!(
                "{}{} => \"{}\"",
                match_indent,
                j,
                suffixes[j % suffixes.len()]
            ));
        }
        arms.push(format!(
            "{}_ => \"{}\"",
            match_indent,
            suffixes[num_arms % suffixes.len()]
        ));

        scope.add_local(
            s_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );
        scope.protected_vars.push(s_name.clone());

        Some(format!(
            "let mut {} = \"\"\n\
             {}for {} in 0..{} {{\n\
             {}{} = {} + match {} {{\n\
             {}\n\
             {}}}\n\
             {}}}",
            s_name,
            body_indent,
            i_name,
            n,
            body_indent,
            s_name,
            s_name,
            i_name,
            arms.join("\n"),
            body_indent,
            body_indent,
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
    fn generates_for_loop_with_match() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringBuildMatch.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let mut "));
        assert!(text.contains("match "));
        assert!(text.contains("_ => "));
    }

    #[test]
    fn protects_accumulator() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        StringBuildMatch.generate(&mut scope, &mut emit, &params);
        assert!(!scope.protected_vars.is_empty());
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringBuildMatch.name(), "string_build_match");
    }
}

//! Rule: while-loop string building.
//!
//! Produces a pattern like:
//! ```vole
//! let mut s = "x"
//! while s.length() < 10 {
//!     s = s + "x"
//! }
//! ```
//! Tests while-loop with `.length()` method call in the condition and
//! mutable string concatenation in the body.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhileStringBuild;

impl StmtRule for WhileStringBuild {
    fn name(&self) -> &'static str {
        "while_string_build"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let str_name = scope.fresh_name();
        let indent = emit.indent_str();

        let choice = emit.gen_range(0..3);
        let (init, append) = match choice {
            0 => ("\"x\"", "\"x\""),
            1 => ("\"ab\"", "\"cd\""),
            _ => ("\"!\"", "\"!\""),
        };
        let limit = emit.random_in(5, 15);

        scope.protected_vars.push(str_name.clone());
        scope.add_local(
            str_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "let mut {} = {}\n\
             {indent}while {}.length() < {} {{\n\
             {indent}    {} = {} + {}\n\
             {indent}}}",
            str_name,
            init,
            str_name,
            limit,
            str_name,
            str_name,
            append,
            indent = indent,
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
    fn generates_while_loop() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhileStringBuild.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let mut "));
        assert!(text.contains("while "));
        assert!(text.contains(".length()"));
    }

    #[test]
    fn protects_string_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        WhileStringBuild.generate(&mut scope, &mut emit, &params);
        assert!(!scope.protected_vars.is_empty());
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(WhileStringBuild.name(), "while_string_build");
    }
}

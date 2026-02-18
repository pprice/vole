//! Rule: operations on strings with repeated characters.
//!
//! Generates `"aaa".length()`, `"aaa".replace("a", "b")`, `"   ".trim()`, etc.
//! Tests string method behavior on uniform content.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct RepeatedStringOps;

impl StmtRule for RepeatedStringOps {
    fn name(&self) -> &'static str {
        "repeated_string_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let repeated_strings = ["aaa", "   ", "111", "xxx", "ZZZ"];
        let s = repeated_strings[emit.gen_range(0..repeated_strings.len())];

        match emit.gen_range(0..5) {
            0 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = \"{}\".length()", name, s))
            }
            1 => {
                let ch = &s[0..1];
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = \"{}\".contains(\"{}\")", name, s, ch))
            }
            2 => {
                let ch = &s[0..1];
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!(
                    "let {} = \"{}\".replace(\"{}\", \"b\")",
                    name, s, ch
                ))
            }
            3 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".trim()", name, s))
            }
            _ => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".to_upper()", name, s))
            }
        }
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
        assert_eq!(RepeatedStringOps.name(), "repeated_string_ops");
    }

    #[test]
    fn generates_op() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = RepeatedStringOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }
}

//! Rule: whitespace-heavy string operations.
//!
//! Generates `"  hello  ".trim()`, `"  ".trim().length()`, etc.
//! Tests string methods on strings with leading/trailing/only whitespace.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhitespaceStringOps;

impl StmtRule for WhitespaceStringOps {
    fn name(&self) -> &'static str {
        "whitespace_string_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let ws_strings = ["  hello  ", "  ", " x ", "  spaces  here  "];
        let s = ws_strings[emit.gen_range(0..ws_strings.len())];

        match emit.gen_range(0..4) {
            0 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".trim()", name, s))
            }
            1 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = \"{}\".trim().length()", name, s))
            }
            2 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = \"{}\".contains(\" \")", name, s))
            }
            _ => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".replace(\" \", \"\")", name, s))
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
        assert_eq!(WhitespaceStringOps.name(), "whitespace_string_ops");
    }

    #[test]
    fn generates_whitespace_op() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhitespaceStringOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
    }
}

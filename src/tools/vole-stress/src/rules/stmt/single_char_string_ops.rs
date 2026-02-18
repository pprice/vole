//! Rule: operations on single-character strings.
//!
//! Generates `"x".to_upper()`, `"a".length()`, `"Z".contains("Z")` etc.,
//! testing string method behavior on minimal inputs.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SingleCharStringOps;

impl StmtRule for SingleCharStringOps {
    fn name(&self) -> &'static str {
        "single_char_string_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let chars = ["a", "Z", "0", " ", "x", "M"];
        let ch = chars[emit.gen_range(0..chars.len())];
        let name = scope.fresh_name();

        match emit.gen_range(0..6) {
            0 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".to_upper()", name, ch))
            }
            1 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".to_lower()", name, ch))
            }
            2 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = \"{}\".length()", name, ch))
            }
            3 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!("let {} = \"{}\".contains(\"{}\")", name, ch, ch))
            }
            4 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".trim()", name, ch))
            }
            _ => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"{}\".substring(0, 1)", name, ch))
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
        assert_eq!(SingleCharStringOps.name(), "single_char_string_ops");
    }

    #[test]
    fn generates_single_char_op() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SingleCharStringOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
    }
}

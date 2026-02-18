//! Rule: chained method calls on literal strings.
//!
//! Generates chains like `"hello world".split(" ").count()`,
//! `"abc".length().to_string()`, etc.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ChainedLiteralMethod;

impl StmtRule for ChainedLiteralMethod {
    fn name(&self) -> &'static str {
        "chained_literal_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        match emit.gen_range(0..4) {
            0 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!(
                    "let {} = \"hello world\".split(\" \").count()",
                    name
                ))
            }
            1 => {
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::String),
                    false,
                );
                Some(format!("let {} = \"abc\".length().to_string()", name))
            }
            2 => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = \"a,b,c\".split(\",\").count()", name))
            }
            _ => {
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
                Some(format!("let {} = \"HELLO\".to_lower().length()", name))
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
        assert_eq!(ChainedLiteralMethod.name(), "chained_literal_method");
    }

    #[test]
    fn generates_chained_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ChainedLiteralMethod.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let "), "got: {text}");
    }
}

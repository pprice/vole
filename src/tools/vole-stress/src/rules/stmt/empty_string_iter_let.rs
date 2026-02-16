//! Rule: empty string iteration.
//!
//! Generates `let s = ""; let result = s.iter().count()` (or collect, any, all, map).

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EmptyStringIterLet;

impl StmtRule for EmptyStringIterLet {
    fn name(&self) -> &'static str {
        "empty_string_iter_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let str_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        let (chain, result_type) = match emit.gen_range(0..5) {
            0 => (
                ".iter().collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            ),
            1 => (
                ".iter().count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            2 => (
                ".iter().any((c) => c == \"a\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            3 => (
                ".iter().all((c) => c != \"x\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (
                ".iter().map((c) => c + \"!\").collect()".to_string(),
                TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
            ),
        };

        scope.add_local(
            str_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = \"\"\nlet {} = {}{}",
            str_name, result_name, str_name, chain
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
        assert_eq!(EmptyStringIterLet.name(), "empty_string_iter_let");
    }

    #[test]
    fn generates_empty_string_iter() {
        let table = SymbolTable::new();
        let params = &[];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EmptyStringIterLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("\"\""), "got: {text}");
        assert!(text.contains(".iter()"), "got: {text}");
    }
}

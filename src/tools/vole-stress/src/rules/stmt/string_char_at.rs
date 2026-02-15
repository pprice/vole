//! Rule: character extraction via substring.
//!
//! Produces `let localN = "hello".substring(idx, idx+1)` to test single-character
//! extraction from known-length string literals.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringCharAt;

impl StmtRule for StringCharAt {
    fn name(&self) -> &'static str {
        "string_char_at"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();
        let strings = [
            ("hello", 5),
            ("world", 5),
            ("test", 4),
            ("abc", 3),
            ("vole", 4),
        ];
        let choice = emit.gen_range(0..strings.len());
        let (s, len) = strings[choice];
        let idx = emit.gen_range(0..len);

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = \"{}\".substring({}, {})",
            name,
            s,
            idx,
            idx + 1
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
    fn generates_substring_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringCharAt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let local0 = "));
        assert!(text.contains(".substring("));
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringCharAt.name(), "string_char_at");
    }

    #[test]
    fn adds_string_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        StringCharAt.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), 1);
        assert_eq!(
            scope.locals[0].1,
            TypeInfo::Primitive(PrimitiveType::String)
        );
    }
}

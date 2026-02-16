//! Rule: string split expression.
//!
//! Generates `strVar.split(",").collect()` to produce a `[string]` array.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringSplit;

impl ExprRule for StringSplit {
    fn name(&self) -> &'static str {
        "string_split"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .first()
            .is_some()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Result is [string]
        let is_string_array = matches!(
            expected_type,
            TypeInfo::Array(inner) if matches!(**inner, TypeInfo::Primitive(PrimitiveType::String))
        );
        if !is_string_array {
            return None;
        }

        let candidates = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var = &candidates[idx].name;

        let delimiters = [",", " ", ":", ";", "-", "::"];
        let delim = delimiters[emit.gen_range(0..delimiters.len())];

        Some(format!("{}.split(\"{}\").collect()", var, delim))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ParamValue, StmtRule};
    use crate::symbols::SymbolTable;
    use rand::SeedableRng;

    fn test_emit<'a>(rng: &'a mut dyn rand::RngCore, resolved: &'a ResolvedParams) -> Emit<'a> {
        static EMPTY_STMT: &[Box<dyn StmtRule>] = &[];
        static EMPTY_EXPR: &[Box<dyn ExprRule>] = &[];
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringSplit.name(), "string_split");
    }

    #[test]
    fn generates_split_collect() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringSplit.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".split("), "expected split, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_for_non_array_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringSplit.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_none());
    }
}

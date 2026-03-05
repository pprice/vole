//! Rule: chained string method expression.
//!
//! Generates 3-5 chained no-arg string methods on an existing string variable
//! to stress RC handling for intermediate string temporaries.
//! Example: `s.trim().to_upper().to_lower().trim_end()`

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

/// No-arg string methods that return `string`.
const NO_ARG_METHODS: &[&str] = &["trim", "to_upper", "to_lower", "trim_start", "trim_end"];

pub struct StringChain;

impl ExprRule for StringChain {
    fn name(&self) -> &'static str {
        "string_chain"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
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
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::String)) {
            return None;
        }

        let candidates = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var = &candidates[idx].name;

        // Chain length: 3-5
        let chain_len = 3 + emit.gen_range(0..3);

        let mut result = var.clone();
        for _ in 0..chain_len {
            let method = NO_ARG_METHODS[emit.gen_range(0..NO_ARG_METHODS.len())];
            result.push_str(&format!(".{}()", method));
        }

        Some(result)
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
        assert_eq!(StringChain.name(), "string_chain");
    }

    #[test]
    fn returns_none_for_non_string() {
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

        let result = StringChain.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringChain.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_chain_of_3_to_5_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        // Run with several seeds to verify chain length is always 3-5.
        for seed in 0..20 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);

            let result = StringChain.generate(
                &scope,
                &mut emit,
                &params,
                &TypeInfo::Primitive(PrimitiveType::String),
            );
            let text = result.expect("should generate for string type");
            assert!(
                text.starts_with("s."),
                "expected method chain on s, got: {text}"
            );

            // Count the number of method calls by counting ".method()" occurrences.
            let dot_count = text.matches("()").count();
            assert!(
                (3..=5).contains(&dot_count),
                "expected 3-5 chained methods, got {dot_count} in: {text}"
            );
        }
    }
}

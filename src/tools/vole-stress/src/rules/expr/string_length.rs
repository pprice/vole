//! Rule: string length expression.
//!
//! Generates `strVar.length()` when a string-typed variable is in scope
//! and the expected type is `i64`. Optionally chains a string transform
//! (`.trim()`, `.to_upper()`, `.to_lower()`) before `.length()`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringLength;

impl ExprRule for StringLength {
    fn name(&self) -> &'static str {
        "string_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.12),
            Param::prob("chain_probability", 0.20),
        ]
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
        params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            return None;
        }

        let candidates = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var = &candidates[idx].name;

        let chain_prob = params.prob("chain_probability");
        if emit.gen_bool(chain_prob) {
            let chain = random_string_chain(emit);
            Some(format!("{}{}.length()", var, chain))
        } else {
            Some(format!("{}.length()", var))
        }
    }
}

fn random_string_chain(emit: &mut Emit) -> &'static str {
    let methods = [".trim()", ".to_upper()", ".to_lower()"];
    methods[emit.gen_range(0..methods.len())]
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
        assert_eq!(StringLength.name(), "string_length");
    }

    #[test]
    fn returns_none_for_non_i64() {
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
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = StringLength.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_length_call() {
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
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(0.0)),
        ]);

        let result = StringLength.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".length()"),
            "expected .length(), got: {text}"
        );
    }
}

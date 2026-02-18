//! Rule: string chars collect expression.
//!
//! Generates `strVar.chars().collect()` to produce a `[i32]` array.
//! `.chars()` returns character codepoints as i32 values.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringChars;

impl ExprRule for StringChars {
    fn name(&self) -> &'static str {
        "string_chars"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.06),
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
        // Result is [i32]
        let is_i32_array = matches!(
            expected_type,
            TypeInfo::Array(inner) if matches!(**inner, TypeInfo::Primitive(PrimitiveType::I32))
        );
        if !is_i32_array {
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
            let chains = [".trim()", ".to_upper()", ".to_lower()"];
            let chain = chains[emit.gen_range(0..chains.len())];
            Some(format!("{}{}.chars().collect()", var, chain))
        } else {
            Some(format!("{}.chars().collect()", var))
        }
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
        assert_eq!(StringChars.name(), "string_chars");
    }

    #[test]
    fn generates_chars_collect() {
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

        let result = StringChars.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I32))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".chars().collect()"),
            "expected chars, got: {text}"
        );
    }
}

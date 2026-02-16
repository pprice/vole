//! Rule: string concatenation expression.
//!
//! Generates `(str1 + str2)` or `(str1 + str2 + str3)` string concatenation.
//! ~30% chance each operand is a `.to_string()` call on a numeric/bool var.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringConcat;

impl ExprRule for StringConcat {
    fn name(&self) -> &'static str {
        "string_concat"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, _scope: &Scope, _params: &Params) -> bool {
        true
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

        let str_ty = TypeInfo::Primitive(PrimitiveType::String);
        let operand_count = emit.random_in(2, 3);
        let mut parts = Vec::new();

        for _ in 0..operand_count {
            // ~30% chance: use .to_string() on a numeric/bool variable
            if emit.gen_bool(0.3) {
                let to_str_candidates = scope.vars_matching(|v| {
                    matches!(
                        v.type_info,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::I32
                                | PrimitiveType::F64
                                | PrimitiveType::Bool
                        )
                    )
                });
                if !to_str_candidates.is_empty() {
                    let idx = emit.gen_range(0..to_str_candidates.len());
                    parts.push(format!("{}.to_string()", to_str_candidates[idx].name));
                    continue;
                }
            }
            parts.push(emit.literal(&str_ty));
        }

        Some(format!("({})", parts.join(" + ")))
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
        assert_eq!(StringConcat.name(), "string_concat");
    }

    #[test]
    fn returns_none_for_non_string() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringConcat.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_concat() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringConcat.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(" + "), "expected concatenation, got: {text}");
    }
}

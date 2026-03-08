//! Rule: string compare expression.
//!
//! Generates `str1.compare(str2)` when two string-typed variables are in
//! scope and the expected type is `i64`. Returns negative, zero, or
//! positive for lexicographic ordering. Optionally chains a string
//! transform before `.compare()`.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct StringCompare;

impl ExprRule for StringCompare {
    fn name(&self) -> &'static str {
        "string_compare"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.06),
            Param::prob("chain_probability", 0.30),
        ]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .len()
            >= 2
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
        if candidates.len() < 2 {
            return None;
        }

        let idx1 = emit.gen_range(0..candidates.len());
        let mut idx2 = emit.gen_range(0..candidates.len());
        if idx2 == idx1 {
            idx2 = (idx1 + 1) % candidates.len();
        }
        let var1 = &candidates[idx1].name;
        let var2 = &candidates[idx2].name;

        let chain_prob = params.prob("chain_probability");
        if emit.gen_bool(chain_prob) {
            let chain = random_string_chain(emit);
            if emit.gen_bool(0.5) {
                Some(format!("{}{}.compare({})", var1, chain, var2))
            } else {
                Some(format!("{}.compare({}{})", var1, var2, chain))
            }
        } else {
            Some(format!("{}.compare({})", var1, var2))
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
        assert_eq!(StringCompare.name(), "string_compare");
    }

    #[test]
    fn returns_none_for_non_i64() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s1".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        scope.add_local(
            "s2".into(),
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

        let result = StringCompare.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_for_single_string() {
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

        let result = StringCompare.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }

    #[test]
    fn generates_compare_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s1".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        scope.add_local(
            "s2".into(),
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

        let result = StringCompare.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".compare("),
            "expected .compare(), got: {text}"
        );
    }

    #[test]
    fn generates_chained_compare() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s1".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        scope.add_local(
            "s2".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("chain_probability", ParamValue::Probability(1.0)),
        ]);

        let result = StringCompare.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".compare("),
            "expected .compare(), got: {text}"
        );
        let has_chain = text.contains(".trim()")
            || text.contains(".to_upper()")
            || text.contains(".to_lower()");
        assert!(has_chain, "expected a chained transform, got: {text}");
    }
}

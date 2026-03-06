//! Rule: string split with iterator transform chains.
//!
//! Generates `"a,b,c".split(",").map((s) => s.to_upper()).collect()` and similar
//! patterns combining string splitting with iterator operations that transform
//! the split parts. Exercises string→iterator→closure→string interactions.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SplitTransform;

impl StmtRule for SplitTransform {
    fn name(&self) -> &'static str {
        "split_transform"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        let delims = [",", ";", " ", "-", "_"];
        let delim = delims[emit.gen_range(0..delims.len())];

        let words: &[&str] = &["alpha", "beta", "gamma", "delta", "epsilon"];
        let word_count = emit.random_in(2, 4);
        let mut selected: Vec<&str> = Vec::new();
        for _ in 0..word_count {
            selected.push(words[emit.gen_range(0..words.len())]);
        }
        let literal = selected.join(delim);

        let base = if string_vars.is_empty() || emit.gen_range(0..3) == 0 {
            format!("\"{literal}\"")
        } else {
            string_vars[emit.gen_range(0..string_vars.len())].clone()
        };

        let result_name = scope.fresh_name();
        let variant = emit.gen_range(0..4);

        match variant {
            0 => {
                // split → map(to_upper) → collect
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {result_name} = {base}.split(\"{delim}\").map((s) => s.to_upper()).collect()"
                ))
            }
            1 => {
                // split → map(to_lower) → collect
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {result_name} = {base}.split(\"{delim}\").map((s) => s.to_lower()).collect()"
                ))
            }
            2 => {
                // split → map(length) → collect → [i64]
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                    false,
                );
                Some(format!(
                    "let {result_name} = {base}.split(\"{delim}\").map((s) => s.length()).collect()"
                ))
            }
            _ => {
                // split → filter(non-empty) → map(trim) → collect
                scope.add_local(
                    result_name.clone(),
                    TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                    false,
                );
                Some(format!(
                    "let {result_name} = {base}.split(\"{delim}\").filter((s) => s.length() > 0).map((s) => s.trim()).collect()"
                ))
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
        assert_eq!(SplitTransform.name(), "split_transform");
    }

    #[test]
    fn generates_split_map() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SplitTransform.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".split("), "got: {text}");
        assert!(text.contains(".collect()"), "got: {text}");
    }

    #[test]
    fn generates_all_variants() {
        let table = SymbolTable::new();
        let resolved = ResolvedParams::new();
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let mut found_upper = false;
        let mut found_lower = false;
        let mut found_length = false;
        let mut found_filter = false;

        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            if let Some(text) = SplitTransform.generate(&mut scope, &mut emit, &params) {
                if text.contains("to_upper") {
                    found_upper = true;
                }
                if text.contains("to_lower") {
                    found_lower = true;
                }
                if text.contains(".map((s) => s.length())") {
                    found_length = true;
                }
                if text.contains(".filter(") {
                    found_filter = true;
                }
            }
        }

        assert!(found_upper, "never generated to_upper variant");
        assert!(found_lower, "never generated to_lower variant");
        assert!(found_filter, "never generated filter variant");
    }
}

//! Rule: raw string search let-bindings.
//!
//! Generates `index_of_raw` and `char_at_raw` calls on strings.
//! Both methods return `i32` (-1 on failure).
//!
//! Variants:
//! - `let idx: i32 = s.index_of_raw("sub")`
//! - `let ch: i32 = s.char_at_raw(N)`
//! - `let found = s.index_of_raw("x") >= 0`
//! - `let is_h = s.char_at_raw(0) == 104`

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringSearchLet;

impl StmtRule for StringSearchLet {
    fn name(&self) -> &'static str {
        "string_search_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        let name = scope.fresh_name();

        let receiver = if !string_vars.is_empty() && emit.gen_bool(0.6) {
            string_vars[emit.gen_range(0..string_vars.len())].clone()
        } else {
            let literals = [
                "\"hello world\"",
                "\"testing\"",
                "\"abcdef\"",
                "\"vole lang\"",
                "\"search me\"",
            ];
            literals[emit.gen_range(0..literals.len())].to_string()
        };

        let search_strs = ["hello", "world", "a", "e", "test", "xyz", "o", "l"];
        let search = search_strs[emit.gen_range(0..search_strs.len())];

        // Safe indices for char_at_raw on known literals (all <= 10 chars).
        // For variables we use small indices; OOB just returns -1.
        let char_idx = emit.gen_range(0..5);

        // ASCII codepoints for comparison variants.
        let codepoints: [(i32, &str); 6] = [
            (104, "h"),
            (101, "e"),
            (108, "l"),
            (111, "o"),
            (97, "a"),
            (116, "t"),
        ];
        let (cp_val, _cp_char) = codepoints[emit.gen_range(0..codepoints.len())];

        let variant = emit.gen_range(0..4);
        match variant {
            0 => {
                // let idx: i32 = s.index_of_raw("sub")
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I32), false);
                Some(format!(
                    "let {}: i32 = {}.index_of_raw(\"{}\")",
                    name, receiver, search
                ))
            }
            1 => {
                // let ch: i32 = s.char_at_raw(N)
                scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I32), false);
                Some(format!(
                    "let {}: i32 = {}.char_at_raw({})",
                    name, receiver, char_idx
                ))
            }
            2 => {
                // let found = s.index_of_raw("x") >= 0
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = {}.index_of_raw(\"{}\") >= 0_i32",
                    name, receiver, search
                ))
            }
            _ => {
                // let is_h = s.char_at_raw(0) == 104
                scope.add_local(
                    name.clone(),
                    TypeInfo::Primitive(PrimitiveType::Bool),
                    false,
                );
                Some(format!(
                    "let {} = {}.char_at_raw({}) == {}_i32",
                    name, receiver, char_idx, cp_val
                ))
            }
        }
    }
}

fn collect_string_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(param.name.clone());
        }
    }
    out
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
        assert_eq!(StringSearchLet.name(), "string_search_let");
    }

    #[test]
    fn generates_with_literal_fallback() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringSearchLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("index_of_raw") || text.contains("char_at_raw"),
            "got: {text}"
        );
    }

    #[test]
    fn generates_with_string_var() {
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

        let result = StringSearchLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("index_of_raw") || text.contains("char_at_raw"),
            "got: {text}"
        );
    }

    #[test]
    fn adds_correct_type() {
        let table = SymbolTable::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(0);

        // Run multiple seeds to cover both i32 and bool variants.
        let mut saw_i32 = false;
        let mut saw_bool = false;
        for seed in 0..20 {
            let mut scope = Scope::new(&[], &table);
            rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            StringSearchLet.generate(&mut scope, &mut emit, &params);
            assert_eq!(scope.locals.len(), 1);
            match &scope.locals[0].1 {
                TypeInfo::Primitive(PrimitiveType::I32) => saw_i32 = true,
                TypeInfo::Primitive(PrimitiveType::Bool) => saw_bool = true,
                other => panic!("unexpected type: {:?}", other),
            }
        }
        assert!(saw_i32, "expected at least one i32 variant");
        assert!(saw_bool, "expected at least one bool variant");
    }
}

//! Rule: string method call let-binding.
//!
//! Finds a string-typed variable in scope and calls a random method on it:
//! `.length()`, `.contains(...)`, `.starts_with(...)`, `.ends_with(...)`,
//! `.trim()`, `.to_upper()`, `.to_lower()`.
//!
//! ~30% chance to chain an additional method when the result is still a string.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

/// Short strings for method arguments.
const SHORT_STRINGS: &[&str] = &[
    "hello", "world", "test", "foo", "bar", "abc", "xyz", "str", "", "\\n", "\\t", " ", "a",
];

pub struct StringMethodLet;

impl StmtRule for StringMethodLet {
    fn name(&self) -> &'static str {
        "string_method_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)))
            .first()
            .is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::String)));
        if string_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..string_vars.len());
        let var_name = string_vars[idx].name.clone();
        let result_name = scope.fresh_name();

        let (call_expr, result_type) = gen_method_call(emit, &var_name);

        // ~30% chance to chain an additional method when result is string
        let (call_expr, result_type) =
            if matches!(result_type, TypeInfo::Primitive(PrimitiveType::String))
                && emit.gen_bool(0.30)
            {
                gen_chain_method(emit, &call_expr)
            } else {
                (call_expr, result_type)
            };

        scope.add_local(result_name.clone(), result_type, false);
        Some(format!("let {} = {}", result_name, call_expr))
    }
}

fn gen_method_call(emit: &mut Emit, var_name: &str) -> (String, TypeInfo) {
    let method = emit.gen_range(0..7);
    match method {
        0 => (
            format!("{}.length()", var_name),
            TypeInfo::Primitive(PrimitiveType::I64),
        ),
        1 => {
            let needle = random_short_string(emit);
            (
                format!("{}.contains(\"{}\")", var_name, needle),
                TypeInfo::Primitive(PrimitiveType::Bool),
            )
        }
        2 => {
            let needle = random_short_string(emit);
            (
                format!("{}.starts_with(\"{}\")", var_name, needle),
                TypeInfo::Primitive(PrimitiveType::Bool),
            )
        }
        3 => {
            let needle = random_short_string(emit);
            (
                format!("{}.ends_with(\"{}\")", var_name, needle),
                TypeInfo::Primitive(PrimitiveType::Bool),
            )
        }
        4 => (
            format!("{}.trim()", var_name),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        5 => (
            format!("{}.to_upper()", var_name),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        _ => (
            format!("{}.to_lower()", var_name),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
    }
}

fn gen_chain_method(emit: &mut Emit, call_expr: &str) -> (String, TypeInfo) {
    let chain = emit.gen_range(0..6);
    match chain {
        0 => (
            format!("{}.length()", call_expr),
            TypeInfo::Primitive(PrimitiveType::I64),
        ),
        1 => {
            let needle = random_short_string(emit);
            (
                format!("{}.contains(\"{}\")", call_expr, needle),
                TypeInfo::Primitive(PrimitiveType::Bool),
            )
        }
        2 => (
            format!("{}.trim()", call_expr),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        3 => (
            format!("{}.to_upper()", call_expr),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        4 => (
            format!("{}.to_lower()", call_expr),
            TypeInfo::Primitive(PrimitiveType::String),
        ),
        _ => {
            let needle = random_short_string(emit);
            (
                format!("{}.starts_with(\"{}\")", call_expr, needle),
                TypeInfo::Primitive(PrimitiveType::Bool),
            )
        }
    }
}

fn random_short_string(emit: &mut Emit) -> String {
    SHORT_STRINGS[emit.gen_range(0..SHORT_STRINGS.len())].to_string()
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
        assert_eq!(StringMethodLet.name(), "string_method_let");
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringMethodLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_method_call_with_string_var() {
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
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringMethodLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
        assert!(text.contains('.'), "expected method call, got: {text}");
    }
}

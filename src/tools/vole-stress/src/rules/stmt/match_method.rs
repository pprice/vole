//! Rule: match on method call result (small variant).
//!
//! Finds a string or i64 variable in scope and generates a match on a
//! method call result:
//! ```vole
//! let result = match str.length() { 0 => -5, _ => 3 }
//! let result = match num.to_string() { "0" => 1, _ => -2 }
//! let result = match str.trim() { "" => true, _ => false }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchMethod;

impl StmtRule for MatchMethod {
    fn name(&self) -> &'static str {
        "match_method"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let result_name = scope.fresh_name();

        let string_vars = collect_typed_vars(scope, PrimitiveType::String);
        let i64_vars = collect_typed_vars(scope, PrimitiveType::I64);

        if string_vars.is_empty() && i64_vars.is_empty() {
            return None;
        }

        let variant = emit.gen_range(0..3);
        match variant {
            0 if !string_vars.is_empty() => {
                generate_string_length_match(scope, emit, &string_vars, &result_name)
            }
            1 if !i64_vars.is_empty() => {
                generate_tostring_match(scope, emit, &i64_vars, &result_name)
            }
            _ if !string_vars.is_empty() => {
                generate_string_method_match(scope, emit, &string_vars, &result_name)
            }
            _ => None,
        }
    }
}

/// Collect variables of a given primitive type from scope.
fn collect_typed_vars(scope: &Scope, prim: PrimitiveType) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(p) if *p == prim) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(&param.param_type, TypeInfo::Primitive(p) if *p == prim) {
            out.push(param.name.clone());
        }
    }
    out
}

/// `match str.length() { N => val0, _ => val1 }`
fn generate_string_length_match(
    scope: &mut Scope,
    emit: &mut Emit,
    string_vars: &[String],
    result_name: &str,
) -> Option<String> {
    let idx = emit.gen_range(0..string_vars.len());
    let var = &string_vars[idx];
    let val0 = emit.gen_i64_range(-5, 5);
    let val1 = emit.gen_i64_range(-5, 5);
    let arm_len = emit.random_in(0, 10);

    scope.add_local(
        result_name.to_string(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    Some(format!(
        "let {} = match {}.length() {{ {} => {}, _ => {} }}",
        result_name, var, arm_len, val0, val1
    ))
}

/// `match num.to_string() { "0" => val, _ => val }`
fn generate_tostring_match(
    scope: &mut Scope,
    emit: &mut Emit,
    i64_vars: &[String],
    result_name: &str,
) -> Option<String> {
    let idx = emit.gen_range(0..i64_vars.len());
    let var = &i64_vars[idx];
    let strs = ["\"0\"", "\"1\"", "\"-1\"", "\"42\""];
    let arm_str = strs[emit.gen_range(0..strs.len())];
    let val_true = emit.gen_i64_range(-10, 10);
    let val_false = emit.gen_i64_range(-10, 10);

    scope.add_local(
        result_name.to_string(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );
    Some(format!(
        "let {} = match {}.to_string() {{ {} => {}, _ => {} }}",
        result_name, var, arm_str, val_true, val_false
    ))
}

/// `match str.trim() { "" => true, _ => false }`
fn generate_string_method_match(
    scope: &mut Scope,
    emit: &mut Emit,
    string_vars: &[String],
    result_name: &str,
) -> Option<String> {
    let idx = emit.gen_range(0..string_vars.len());
    let var = &string_vars[idx];
    let methods = ["trim", "to_lower", "to_upper"];
    let method = methods[emit.gen_range(0..methods.len())];
    let match_strs = ["\"\"", "\"hello\"", "\"test\""];
    let match_str = match_strs[emit.gen_range(0..match_strs.len())];

    scope.add_local(
        result_name.to_string(),
        TypeInfo::Primitive(PrimitiveType::Bool),
        false,
    );
    Some(format!(
        "let {} = match {}.{}() {{ {} => true, _ => false }}",
        result_name, var, method, match_str
    ))
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
        assert_eq!(MatchMethod.name(), "match_method");
    }

    #[test]
    fn returns_none_without_variables() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchMethod
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_string_variable() {
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

        let result = MatchMethod.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match s."), "got: {text}");
    }

    #[test]
    fn generates_with_i64_variable() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        // Try multiple seeds since variant selection is random and only
        // variant 1 (to_string match) works without string vars.
        let mut generated = false;
        for seed in 0..20u64 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
            let mut test_scope = Scope::new(&[], &table);
            test_scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

            if let Some(text) = MatchMethod.generate(&mut test_scope, &mut emit, &params) {
                assert!(text.contains("to_string()"), "got: {text}");
                generated = true;
                break;
            }
        }
        assert!(generated, "expected at least one seed to produce output");
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "v".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        MatchMethod.generate(&mut scope, &mut emit, &params);
        assert_eq!(scope.locals.len(), initial_len + 1);
    }
}

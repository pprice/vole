//! Rule: iterator count expression.
//!
//! Generates `arrVar.iter().count()` or `arrVar.iter().filter(...).count()`
//! when an array-typed variable is in scope. Result type is `i64`.
//!
//! Single-param lambdas use unparenthesized `x => pred` 30% of the time
//! and implicit `it` style 20% of the time.
//! The `.iter()` call is omitted 40% of the time (direct array method call).

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

/// Replace standalone `x` tokens with `it` in a lambda body string.
fn replace_x_with_it(body: &str) -> String {
    let mut result = String::with_capacity(body.len() + 2);
    let chars: Vec<char> = body.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        if chars[i] == 'x' {
            let prev_ok = i == 0 || !chars[i - 1].is_alphanumeric() && chars[i - 1] != '_';
            let next_ok =
                i + 1 >= chars.len() || !chars[i + 1].is_alphanumeric() && chars[i + 1] != '_';
            if prev_ok && next_ok {
                result.push_str("it");
            } else {
                result.push('x');
            }
        } else {
            result.push(chars[i]);
        }
        i += 1;
    }
    result
}

/// Emit a single-param lambda, choosing style randomly:
/// - 20%: implicit `it` (replaces `x` with `it` in the body)
/// - 30%: unparenthesized `x => body`
/// - 50%: parenthesized `(x) => body`
fn emit_single_param_lambda(emit: &mut Emit, body_with_x: &str) -> String {
    let roll = emit.gen_range(0..10_usize);
    if roll < 2 {
        replace_x_with_it(body_with_x)
    } else if roll < 5 {
        format!("x => {}", body_with_x)
    } else {
        format!("(x) => {}", body_with_x)
    }
}

pub struct IterCount;

impl ExprRule for IterCount {
    fn name(&self) -> &'static str {
        "iter_count"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.08)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.array_vars().is_empty()
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            return None;
        }

        let array_vars = scope.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (var_name, elem_ty) = &array_vars[idx];

        // ~40%: call methods directly on the array (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let iter_prefix = if use_direct { "" } else { ".iter()" };

        // ~40% chance to chain a .filter() before .count()
        if emit.gen_bool(0.4)
            && let Some(pred) = gen_predicate(emit, elem_ty)
        {
            let lambda = emit_single_param_lambda(emit, &pred);
            return Some(format!(
                "{}{}.filter({}).count()",
                var_name, iter_prefix, lambda
            ));
        }

        Some(format!("{}{}.count()", var_name, iter_prefix))
    }
}

fn gen_predicate(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
        }
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
        }
        TypeInfo::Primitive(PrimitiveType::I32) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
        }
        TypeInfo::Primitive(PrimitiveType::Bool) => Some("x".to_string()),
        TypeInfo::Primitive(PrimitiveType::String) => {
            let n = emit.gen_i64_range(0, 3);
            Some(format!("x.length() > {}", n))
        }
        _ => None,
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
        assert_eq!(IterCount.name(), "iter_count");
    }

    #[test]
    fn generates_count_with_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterCount.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        // Either uses .iter() or direct array method call; always ends with .count()
        assert!(text.contains("arr"), "expected arr, got: {text}");
        assert!(text.contains(".count()"), "expected count, got: {text}");
    }
}

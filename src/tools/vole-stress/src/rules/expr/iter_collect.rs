//! Rule: iterator collect expressions.
//!
//! Generates array-producing iterator chains:
//! - `arr.iter().skip(N).take(M).collect()`
//! - `arr.iter().sorted().collect()`
//! - `arr.iter().filter((x) => pred).collect()`
//! - `arr.iter().unique().collect()`
//!
//! Target type must be `[T]` where `T` matches an existing array var element.
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

pub struct IterCollect;

impl ExprRule for IterCollect {
    fn name(&self) -> &'static str {
        "iter_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
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
        let target_elem = match expected_type {
            TypeInfo::Array(inner) => inner.as_ref(),
            _ => return None,
        };

        let array_vars = scope.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, _) = candidates[idx];

        // ~40%: call methods directly on the array (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let iter_prefix = if use_direct { "" } else { ".iter()" };

        // Pick a chain variant
        match emit.gen_range(0..5_usize) {
            0 => {
                // skip+take — only via .iter() (no direct form)
                let skip = emit.gen_i64_range(0, 1);
                let take = emit.gen_i64_range(1, 2);
                Some(format!(
                    "{}.iter().skip({}).take({}).collect()",
                    var_name, skip, take
                ))
            }
            1 => {
                // take only
                let take = emit.gen_i64_range(1, 3);
                Some(format!(
                    "{}{}.take({}).collect()",
                    var_name, iter_prefix, take
                ))
            }
            2 => {
                // sorted (only for integer types)
                if matches!(
                    target_elem,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                ) {
                    if emit.gen_bool(0.3) {
                        Some(format!(
                            "{}{}.sorted().reverse().collect()",
                            var_name, iter_prefix
                        ))
                    } else {
                        Some(format!("{}{}.sorted().collect()", var_name, iter_prefix))
                    }
                } else {
                    Some(format!("{}{}.collect()", var_name, iter_prefix))
                }
            }
            3 => {
                // filter
                if let Some(pred) = gen_filter_pred(emit, target_elem) {
                    let lambda = emit_single_param_lambda(emit, &pred);
                    Some(format!(
                        "{}{}.filter({}).collect()",
                        var_name, iter_prefix, lambda
                    ))
                } else {
                    Some(format!("{}{}.collect()", var_name, iter_prefix))
                }
            }
            _ => {
                // unique (integer types)
                if matches!(
                    target_elem,
                    TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32)
                ) {
                    Some(format!("{}{}.unique().collect()", var_name, iter_prefix))
                } else {
                    Some(format!("{}{}.collect()", var_name, iter_prefix))
                }
            }
        }
    }
}

fn gen_filter_pred(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}", n))
        }
        TypeInfo::Primitive(PrimitiveType::I32) => {
            let n = emit.gen_i64_range(0, 5);
            Some(format!("x > {}_i32", n))
        }
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
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
        assert_eq!(IterCollect.name(), "iter_collect");
    }

    #[test]
    fn generates_collect_for_array() {
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

        let result = IterCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        // Either uses .iter() or direct array method call; always ends with .collect()
        assert!(text.contains("arr"), "expected arr, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_for_non_array() {
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

        let result = IterCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}

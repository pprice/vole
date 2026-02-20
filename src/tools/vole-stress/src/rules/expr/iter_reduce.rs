//! Rule: iterator reduce expression.
//!
//! Generates `.iter().reduce()` expressions:
//! - `i64` from `[i64]`: `arr.iter().reduce(0, (acc, x) => acc + x)`
//! - `string` from `[string]`: `arr.iter().reduce("", (acc, x) => acc + x + " ")`
//! - `string` from `[i64]`: map-then-reduce
//!
//! Multi-param lambdas (`(acc, x) => ...`) always keep parentheses.
//! The single-param map lambda uses unparenthesized form 30% of the time and
//! implicit `it` style 20% of the time.
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

pub struct IterReduce;

impl ExprRule for IterReduce {
    fn name(&self) -> &'static str {
        "iter_reduce"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
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
        let array_vars = scope.array_vars();
        if array_vars.is_empty() {
            return None;
        }

        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| match expected_type {
                TypeInfo::Primitive(PrimitiveType::I64) => {
                    matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64))
                }
                TypeInfo::Primitive(PrimitiveType::String) => {
                    matches!(
                        elem_ty,
                        TypeInfo::Primitive(PrimitiveType::String | PrimitiveType::I64)
                    )
                }
                _ => false,
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        // ~40%: call methods directly on the array (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let iter_prefix = if use_direct { "" } else { ".iter()" };

        match (expected_type, elem_ty) {
            (TypeInfo::Primitive(PrimitiveType::I64), TypeInfo::Primitive(PrimitiveType::I64)) => {
                // Multi-param lambda: always keep parens
                Some(format!(
                    "{}{}.reduce(0, (acc, x) => acc + x)",
                    var_name, iter_prefix
                ))
            }
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::String),
            ) => {
                // Multi-param lambda: always keep parens
                Some(format!(
                    "{}{}.reduce(\"\", (acc, x) => acc + x + \" \")",
                    var_name, iter_prefix
                ))
            }
            (
                TypeInfo::Primitive(PrimitiveType::String),
                TypeInfo::Primitive(PrimitiveType::I64),
            ) => {
                // Single-param map lambda: can use unparenthesized/it form
                let map_lambda = emit_single_param_lambda(emit, "\"\" + x");
                // Multi-param reduce lambda: always keep parens
                Some(format!(
                    "{}{}.map({}).reduce(\"\", (acc, s) => acc + s + \",\")",
                    var_name, iter_prefix, map_lambda
                ))
            }
            _ => None,
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
        assert_eq!(IterReduce.name(), "iter_reduce");
    }

    #[test]
    fn generates_reduce_i64() {
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

        let result = IterReduce.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".reduce("), "expected reduce, got: {text}");
    }
}

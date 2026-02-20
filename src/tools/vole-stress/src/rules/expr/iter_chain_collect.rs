//! Rule: iterator chain+collect expression.
//!
//! Generates `arr1.iter().chain(arr2.iter()).collect()` from two different
//! array-typed variables with matching element types. Only supports i64
//! and i32 element types. Optionally chains `.filter()` or `.map()`.
//!
//! Single-param lambdas use unparenthesized `x => body` 30% of the time
//! and implicit `it` style 20% of the time.
//! The `.iter()` calls are omitted 40% of the time (direct array method calls).

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

pub struct IterChainCollect;

impl ExprRule for IterChainCollect {
    fn name(&self) -> &'static str {
        "iter_chain_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.06)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need at least 2 array variables
        scope.array_vars().len() >= 2
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

        // Only i64 and i32
        let is_i64 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I64));
        let is_i32 = matches!(target_elem, TypeInfo::Primitive(PrimitiveType::I32));
        if !is_i64 && !is_i32 {
            return None;
        }

        let array_vars = scope.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| elem_ty == target_elem)
            .collect();

        if candidates.len() < 2 {
            return None;
        }

        // Pick two different candidates
        let idx1 = emit.gen_range(0..candidates.len());
        let mut idx2 = emit.gen_range(0..candidates.len() - 1);
        if idx2 >= idx1 {
            idx2 += 1;
        }
        let (var1, _) = candidates[idx1];
        let (var2, _) = candidates[idx2];

        // ~40%: use direct array method calls (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let (v1_prefix, v2_iter) = if use_direct {
            ("", format!("{}", var2))
        } else {
            (".iter()", format!("{}.iter()", var2))
        };

        // Pick variant: plain chain (60%), filter (20%), map (20%)
        match emit.gen_range(0..10) {
            0..6 => Some(format!(
                "{}{}.chain({}).collect()",
                var1, v1_prefix, v2_iter
            )),
            6..8 => {
                let pred = gen_chain_pred(emit, is_i32);
                let lambda = emit_single_param_lambda(emit, &pred);
                Some(format!(
                    "{}{}.chain({}).filter({}).collect()",
                    var1, v1_prefix, v2_iter, lambda
                ))
            }
            _ => {
                let body = gen_chain_map_body(emit, is_i32);
                let lambda = emit_single_param_lambda(emit, &body);
                Some(format!(
                    "{}{}.chain({}).map({}).collect()",
                    var1, v1_prefix, v2_iter, lambda
                ))
            }
        }
    }
}

fn gen_chain_pred(emit: &mut Emit, is_i32: bool) -> String {
    if is_i32 {
        match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                format!("x > {}", n)
            }
            1 => {
                let n = emit.gen_i64_range(0, 10);
                format!("x < {}", n)
            }
            _ => "x % 2 == 0".to_string(),
        }
    } else {
        match emit.gen_range(0..4) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                format!("x > {}", n)
            }
            1 => {
                let n = emit.gen_i64_range(0, 10);
                format!("x < {}", n)
            }
            2 => "x % 2 == 0".to_string(),
            _ => {
                let n = emit.gen_i64_range(0, 5);
                format!("x != {}", n)
            }
        }
    }
}

fn gen_chain_map_body(emit: &mut Emit, is_i32: bool) -> String {
    if is_i32 {
        match emit.gen_range(0..3) {
            0 => "x * 2_i32".to_string(),
            1 => "x + 1_i32".to_string(),
            _ => "-x".to_string(),
        }
    } else {
        match emit.gen_range(0..3) {
            0 => "x * 2".to_string(),
            1 => "x + 1".to_string(),
            _ => "-x".to_string(),
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
        assert_eq!(IterChainCollect.name(), "iter_chain_collect");
    }

    #[test]
    fn generates_chain_collect() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "arr1".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope.add_local(
            "arr2".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterChainCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".chain("), "expected chain, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }

    #[test]
    fn returns_none_with_one_array() {
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

        let result = IterChainCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_none());
    }
}

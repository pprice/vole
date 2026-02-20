//! Rule: iterator filter+collect expression.
//!
//! Generates `arr.iter().filter((x) => pred).collect()` where the
//! predicate filters elements of the source array. The element type
//! must match the target array element type.
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

pub struct IterFilterCollect;

impl ExprRule for IterFilterCollect {
    fn name(&self) -> &'static str {
        "iter_filter_collect"
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
        let target_elem = match expected_type {
            TypeInfo::Array(inner) => inner.as_ref(),
            _ => return None,
        };

        let array_vars = scope.array_vars();

        // Filter to arrays whose element type matches and supports predicates
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                elem_ty == target_elem
                    && matches!(
                        elem_ty,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::F64
                                | PrimitiveType::I32
                                | PrimitiveType::Bool
                                | PrimitiveType::String
                        )
                    )
            })
            .collect();

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, elem_ty) = candidates[idx];

        let pred = gen_filter_pred(emit, elem_ty)?;

        // ~40%: call .filter() directly on the array (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let lambda = emit_single_param_lambda(emit, &pred);
        if use_direct {
            Some(format!("{}.filter({}).collect()", var_name, lambda))
        } else {
            Some(format!("{}.iter().filter({}).collect()", var_name, lambda))
        }
    }
}

fn gen_filter_pred(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => match emit.gen_range(0..4) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x > {}", n))
            }
            1 => {
                let n = emit.gen_i64_range(0, 10);
                Some(format!("x < {}", n))
            }
            2 => Some("x % 2 == 0".to_string()),
            _ => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x != {}", n))
            }
        },
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
        }
        TypeInfo::Primitive(PrimitiveType::I32) => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x > {}", n))
            }
            1 => {
                let n = emit.gen_i64_range(0, 10);
                Some(format!("x < {}", n))
            }
            _ => Some("x % 2 == 0".to_string()),
        },
        TypeInfo::Primitive(PrimitiveType::Bool) => {
            if emit.gen_bool(0.5) {
                Some("x".to_string())
            } else {
                Some("!x".to_string())
            }
        }
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
        assert_eq!(IterFilterCollect.name(), "iter_filter_collect");
    }

    #[test]
    fn generates_filter_collect() {
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

        let result = IterFilterCollect.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".filter("), "expected filter, got: {text}");
        assert!(text.contains(".collect()"), "expected collect, got: {text}");
    }
}

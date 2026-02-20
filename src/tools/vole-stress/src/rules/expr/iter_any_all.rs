//! Rule: iterator any/all predicate expression.
//!
//! Generates `arrVar.iter().any((x) => pred)` or `.all((x) => pred)`
//! on arrays with primitive element types. Result type is `bool`.
//!
//! Unparenthesized single-param lambdas (`x => pred`) are emitted 30% of the
//! time; implicit-it style (`it > 0`) is emitted 20% of the time.

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

pub struct IterAnyAll;

impl ExprRule for IterAnyAll {
    fn name(&self) -> &'static str {
        "iter_any_all"
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
        if !matches!(expected_type, TypeInfo::Primitive(PrimitiveType::Bool)) {
            return None;
        }

        let array_vars = scope.array_vars();
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::F64
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

        let method = if emit.gen_bool(0.5) { "any" } else { "all" };

        // ~40%: call method directly on the array (no .iter())
        let use_direct = emit.gen_bool(0.4);
        let receiver = if use_direct {
            format!("{}.{}(", var_name, method)
        } else {
            format!("{}.iter().{}(", var_name, method)
        };

        let body_x = match elem_ty {
            TypeInfo::Primitive(PrimitiveType::I64) => match emit.gen_range(0..4_usize) {
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
            },
            TypeInfo::Primitive(PrimitiveType::F64) => {
                let n = emit.gen_i64_range(0, 50);
                format!("x > {}.0", n)
            }
            TypeInfo::Primitive(PrimitiveType::Bool) => {
                if emit.gen_bool(0.5) {
                    "x".to_string()
                } else {
                    "!x".to_string()
                }
            }
            TypeInfo::Primitive(PrimitiveType::String) => {
                let n = emit.gen_i64_range(0, 3);
                format!("x.length() > {}", n)
            }
            _ => return None,
        };

        let lambda = emit_single_param_lambda(emit, &body_x);
        Some(format!("{}{})", receiver, lambda))
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
        assert_eq!(IterAnyAll.name(), "iter_any_all");
    }

    #[test]
    fn generates_any_all() {
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

        let result = IterAnyAll.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".any(") || text.contains(".all("),
            "expected any/all, got: {text}"
        );
    }

    #[test]
    fn returns_none_for_non_bool() {
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

        let result = IterAnyAll.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}

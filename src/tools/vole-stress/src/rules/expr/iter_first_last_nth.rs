//! Rule: iterator first/last/nth expression.
//!
//! Generates `arr.iter().first()`, `arr.iter().last()`, or
//! `arr.iter().nth(N)` for Optional-typed expressions. These iterator
//! terminals return `T?` from `[T]` arrays. Optionally chains
//! `.filter()` or `.map()` before the terminal.

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct IterFirstLastNth;

impl ExprRule for IterFirstLastNth {
    fn name(&self) -> &'static str {
        "iter_first_last_nth"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.12)]
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
        // Expected type must be Optional(T)
        let inner = match expected_type {
            TypeInfo::Optional(inner) => inner.as_ref(),
            _ => return None,
        };

        let array_vars = scope.array_vars();

        // Filter to arrays whose element type matches and is supported
        let candidates: Vec<_> = array_vars
            .iter()
            .filter(|(_, elem_ty)| {
                elem_ty == inner
                    && matches!(
                        elem_ty,
                        TypeInfo::Primitive(
                            PrimitiveType::I64
                                | PrimitiveType::I32
                                | PrimitiveType::I128
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

        // Pick the terminal method
        let terminal = match emit.gen_range(0..3) {
            0 => ".first()".to_string(),
            1 => ".last()".to_string(),
            _ => {
                let n = emit.random_in(0, 3);
                format!(".nth({})", n)
            }
        };

        // ~20% chance: chain a .filter() before the terminal
        if emit.gen_bool(0.2) {
            if let Some(pred) = gen_pred(emit, elem_ty) {
                return Some(format!(
                    "{}.iter().filter((x) => {}){}",
                    var_name, pred, terminal
                ));
            }
        }

        // ~20% chance: chain a .map() before the terminal (same-type only)
        if emit.gen_bool(0.2) {
            if let Some(body) = gen_map_body(emit, elem_ty) {
                return Some(format!(
                    "{}.iter().map((x) => {}){}",
                    var_name, body, terminal
                ));
            }
        }

        Some(format!("{}.iter(){}", var_name, terminal))
    }
}

fn gen_pred(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x > {}", n))
            }
            1 => Some("x % 2 == 0".to_string()),
            _ => {
                let n = emit.gen_i64_range(0, 10);
                Some(format!("x < {}", n))
            }
        },
        TypeInfo::Primitive(PrimitiveType::I32) => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x > {}", n))
            }
            1 => Some("x % 2 == 0".to_string()),
            _ => {
                let n = emit.gen_i64_range(0, 10);
                Some(format!("x < {}", n))
            }
        },
        TypeInfo::Primitive(PrimitiveType::I128) => match emit.gen_range(0..3) {
            0 => {
                let n = emit.gen_i64_range(0, 5);
                Some(format!("x > {}", n))
            }
            1 => Some("x % 2 == 0".to_string()),
            _ => {
                let n = emit.gen_i64_range(0, 10);
                Some(format!("x < {}", n))
            }
        },
        TypeInfo::Primitive(PrimitiveType::F64) => {
            let n = emit.gen_i64_range(0, 50);
            Some(format!("x > {}.0", n))
        }
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

fn gen_map_body(emit: &mut Emit, elem_ty: &TypeInfo) -> Option<String> {
    match elem_ty {
        TypeInfo::Primitive(PrimitiveType::I64) => match emit.gen_range(0..4) {
            0 => Some("x * 2".to_string()),
            1 => Some("x + 1".to_string()),
            2 => Some("x % 10".to_string()),
            _ => Some("-x".to_string()),
        },
        TypeInfo::Primitive(PrimitiveType::I32) => match emit.gen_range(0..2) {
            0 => Some("x * 2_i32".to_string()),
            _ => Some("x + 1_i32".to_string()),
        },
        TypeInfo::Primitive(PrimitiveType::I128) => match emit.gen_range(0..2) {
            0 => Some("x * 2_i128".to_string()),
            _ => Some("x + 1_i128".to_string()),
        },
        TypeInfo::Primitive(PrimitiveType::F64) => match emit.gen_range(0..3) {
            0 => Some("x * 2.0".to_string()),
            1 => Some("x + 1.0".to_string()),
            _ => Some("-x".to_string()),
        },
        TypeInfo::Primitive(PrimitiveType::Bool) => Some("!x".to_string()),
        TypeInfo::Primitive(PrimitiveType::String) => match emit.gen_range(0..3) {
            0 => Some("x.trim()".to_string()),
            1 => Some("x.to_upper()".to_string()),
            _ => Some("x.to_lower()".to_string()),
        },
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(IterFirstLastNth.name(), "iter_first_last_nth");
    }

    #[test]
    fn generates_first_last_nth_for_optional() {
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

        let result = IterFirstLastNth.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Optional(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()"), "expected iter, got: {text}");
        assert!(
            text.contains(".first()") || text.contains(".last()") || text.contains(".nth("),
            "expected first/last/nth, got: {text}"
        );
    }

    #[test]
    fn returns_none_for_non_optional() {
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

        let result = IterFirstLastNth.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}

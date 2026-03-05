//! Rule: variable shadowing with type change.
//!
//! Re-declares an existing primitive variable with a *different* type,
//! exercising the compiler's variable scoping, constant propagation,
//! and type resolution across shadow boundaries.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct VariableShadowTypeChange;

/// Returns `true` if `p` is one of the types we convert from.
fn is_shadowable(p: PrimitiveType) -> bool {
    matches!(
        p,
        PrimitiveType::I64 | PrimitiveType::String | PrimitiveType::Bool
    )
}

/// Collect immutable primitive locals whose type is shadowable.
fn shadowable_locals(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    scope
        .locals
        .iter()
        .filter_map(|(name, ty, is_mut)| {
            if *is_mut {
                return None;
            }
            if let TypeInfo::Primitive(p) = ty {
                if is_shadowable(*p) {
                    return Some((name.clone(), *p));
                }
            }
            None
        })
        .collect()
}

impl StmtRule for VariableShadowTypeChange {
    fn name(&self) -> &'static str {
        "variable_shadow_type_change"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !shadowable_locals(scope).is_empty()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = shadowable_locals(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, src_type) = &candidates[idx];

        // Decide whether to chain two conversions (~25% of the time).
        let do_chain = emit.gen_bool(0.25);

        if do_chain {
            return generate_chain(emit, var_name, *src_type, scope);
        }

        // Pick a single-step conversion.
        let (expr, dest_type) = generate_single(emit, var_name, *src_type)?;

        scope.add_local(var_name.clone(), TypeInfo::Primitive(dest_type), false);
        Some(format!("let {} = {}", var_name, expr))
    }
}

/// Generate a single type-changing conversion expression.
/// Returns `(expression_text, destination_type)`.
fn generate_single(
    emit: &mut Emit,
    var_name: &str,
    src: PrimitiveType,
) -> Option<(String, PrimitiveType)> {
    match src {
        PrimitiveType::I64 => {
            // i64 -> string  or  i64 -> bool
            if emit.gen_bool(0.5) {
                // i64 -> string: x.to_string()
                Some((format!("{}.to_string()", var_name), PrimitiveType::String))
            } else {
                // i64 -> bool: x > 0  or  x == <literal>
                if emit.gen_bool(0.5) {
                    Some((format!("{} > 0", var_name), PrimitiveType::Bool))
                } else {
                    let n = emit.gen_i64_range(0, 20);
                    Some((format!("{} == {}", var_name, n), PrimitiveType::Bool))
                }
            }
        }
        PrimitiveType::String => {
            // string -> i64  or  string -> bool
            if emit.gen_bool(0.5) {
                // string -> i64: x.length()
                Some((format!("{}.length()", var_name), PrimitiveType::I64))
            } else {
                // string -> bool: x.length() > N
                let n = emit.gen_i64_range(0, 10);
                Some((
                    format!("{}.length() > {}", var_name, n),
                    PrimitiveType::Bool,
                ))
            }
        }
        PrimitiveType::Bool => {
            // bool -> string: x.to_string()
            Some((format!("{}.to_string()", var_name), PrimitiveType::String))
        }
        _ => None,
    }
}

/// Generate a chained two-step conversion.
/// e.g. i64 -> string -> i64 via `.to_string().length()`.
fn generate_chain(
    emit: &mut Emit,
    var_name: &str,
    src: PrimitiveType,
    scope: &mut Scope,
) -> Option<String> {
    // Pick a chain based on the source type.
    let (expr, dest_type) = match src {
        PrimitiveType::I64 => {
            // i64 -> string -> i64: x.to_string().length()
            // i64 -> string -> bool: x.to_string().length() > N
            if emit.gen_bool(0.5) {
                (
                    format!("{}.to_string().length()", var_name),
                    PrimitiveType::I64,
                )
            } else {
                let n = emit.gen_i64_range(0, 5);
                (
                    format!("{}.to_string().length() > {}", var_name, n),
                    PrimitiveType::Bool,
                )
            }
        }
        PrimitiveType::String => {
            // string -> i64 -> bool: x.length() > 0
            // string -> i64 -> string: x.length().to_string()
            if emit.gen_bool(0.5) {
                (format!("{}.length() > 0", var_name), PrimitiveType::Bool)
            } else {
                (
                    format!("{}.length().to_string()", var_name),
                    PrimitiveType::String,
                )
            }
        }
        PrimitiveType::Bool => {
            // bool -> string -> i64: x.to_string().length()
            // bool -> string -> bool: x.to_string().length() > N
            if emit.gen_bool(0.5) {
                (
                    format!("{}.to_string().length()", var_name),
                    PrimitiveType::I64,
                )
            } else {
                let n = emit.gen_i64_range(0, 5);
                (
                    format!("{}.to_string().length() > {}", var_name, n),
                    PrimitiveType::Bool,
                )
            }
        }
        _ => return None,
    };

    scope.add_local(var_name.to_string(), TypeInfo::Primitive(dest_type), false);
    Some(format!("let {} = {}", var_name, expr))
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
            SymbolTable::empty_ref(),
        )
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(
            VariableShadowTypeChange.name(),
            "variable_shadow_type_change"
        );
    }

    #[test]
    fn precondition_false_without_locals() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!VariableShadowTypeChange.precondition(&scope, &params));
    }

    #[test]
    fn precondition_false_with_only_mutable() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!VariableShadowTypeChange.precondition(&scope, &params));
    }

    #[test]
    fn precondition_true_with_immutable_primitive() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(VariableShadowTypeChange.precondition(&scope, &params));
    }

    #[test]
    fn returns_none_without_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            VariableShadowTypeChange
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_shadow_from_i64() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = VariableShadowTypeChange.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let x = "), "got: {text}");
        // Must contain a type-changing operation (.to_string(), > , == , .length()).
        assert!(
            text.contains(".to_string()")
                || text.contains("> ")
                || text.contains("== ")
                || text.contains(".length()"),
            "expected type-changing expression, got: {text}"
        );
        // Scope must be updated with the shadow.
        let last_local = scope.locals.last().unwrap();
        assert_eq!(last_local.0, "x");
    }

    #[test]
    fn generates_shadow_from_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = VariableShadowTypeChange.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let s = "), "got: {text}");
    }

    #[test]
    fn generates_shadow_from_bool() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("b".into(), TypeInfo::Primitive(PrimitiveType::Bool), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = VariableShadowTypeChange.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let b = "), "got: {text}");
        // bool -> string is the only single-step option
        let last_local = scope.locals.last().unwrap();
        assert_eq!(last_local.0, "b");
    }

    #[test]
    fn updates_scope_type() {
        // Run many seeds and verify every result changes the type in scope.
        let table = SymbolTable::new();
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = VariableShadowTypeChange.generate(&mut scope, &mut emit, &params) {
                assert!(text.starts_with("let n = "), "seed {seed}: {text}");
                // Scope must have at least 2 entries (original + shadow).
                assert!(scope.locals.len() >= 2, "seed {seed}: scope not updated");
            }
        }
    }

    #[test]
    fn skips_mutable_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Only mutable variables -- should produce None.
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), true);
        scope.add_local("s".into(), TypeInfo::Primitive(PrimitiveType::String), true);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            VariableShadowTypeChange
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }
}

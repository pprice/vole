//! Rule: nested when expression.
//!
//! Generates a when expression where one arm contains another when expression.
//! Only fires for `i64` or `string` expected types, and requires at least one
//! `i64` variable in scope for building comparison conditions.
//!
//! **Patterns:**
//! ```vole
//! when { x > 20 => 3, x > 10 => when { x > 14 => 2, _ => 1 }, _ => 0 }
//! when { x > 10 => "high", x > 5 => when { x % 2 == 0 => "med-even", _ => "med-odd" }, _ => "low" }
//! ```

use crate::emit::Emit;
use crate::rule::{ExprRule, Param, Params, TypeInfo};
use crate::scope::Scope;
use crate::symbols::PrimitiveType;

pub struct NestedWhenExpr;

/// Generate a comparison condition using an i64 variable.
///
/// Picks from `var > N`, `var < N`, and `var % N == 0` patterns.
fn make_condition(emit: &mut Emit, var_name: &str) -> String {
    match emit.gen_range(0..3_usize) {
        0 => {
            let n = emit.random_in(1, 50);
            format!("{} > {}", var_name, n)
        }
        1 => {
            let n = emit.random_in(10, 100);
            format!("{} < {}", var_name, n)
        }
        _ => {
            let n = emit.random_in(2, 5);
            format!("{} % {} == 0", var_name, n)
        }
    }
}

/// Generate a value literal for an arm.
fn arm_value(emit: &mut Emit, is_string: bool) -> String {
    if is_string {
        let labels = [
            "high", "low", "medium", "even", "odd", "big", "small", "zero", "pos", "neg", "ok",
            "done", "yes", "no", "a", "b",
        ];
        let idx = emit.gen_range(0..labels.len());
        format!("\"{}\"", labels[idx])
    } else {
        let n: i64 = emit.random_in(0, 100) as i64;
        n.to_string()
    }
}

impl ExprRule for NestedWhenExpr {
    fn name(&self) -> &'static str {
        "nested_when_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.has_var_of_type(&TypeInfo::Primitive(PrimitiveType::I64))
    }

    fn generate(
        &self,
        scope: &Scope,
        emit: &mut Emit,
        _params: &Params,
        expected_type: &TypeInfo,
    ) -> Option<String> {
        // Only fire for i64 or string expected types.
        let is_string = match expected_type {
            TypeInfo::Primitive(PrimitiveType::I64) => false,
            TypeInfo::Primitive(PrimitiveType::String) => true,
            _ => return None,
        };

        // Need an i64 variable for conditions.
        let i64_ty = TypeInfo::Primitive(PrimitiveType::I64);
        let i64_vars = scope.vars_of_type(&i64_ty);
        if i64_vars.is_empty() {
            return None;
        }

        // Pick a variable for conditions.
        let var_idx = emit.gen_range(0..i64_vars.len());
        let var_name = &i64_vars[var_idx].name;

        // Decide outer arm count: 2 or 3 (not counting the wildcard).
        let outer_arm_count = emit.random_in(2, 3);

        // Decide which arm (0-indexed, excluding wildcard) holds the nested when.
        let nested_arm_idx = emit.gen_range(0..outer_arm_count);

        let mut arms = Vec::new();

        for i in 0..outer_arm_count {
            let cond = make_condition(emit, var_name);
            if i == nested_arm_idx {
                // Build inner when with 2 arms: one condition + wildcard.
                let inner_cond = make_condition(emit, var_name);
                let inner_value = arm_value(emit, is_string);
                let inner_default = arm_value(emit, is_string);
                let inner_when = format!(
                    "when {{ {} => {}, _ => {} }}",
                    inner_cond, inner_value, inner_default
                );
                arms.push(format!("{} => {}", cond, inner_when));
            } else {
                let value = arm_value(emit, is_string);
                arms.push(format!("{} => {}", cond, value));
            }
        }

        // Wildcard default arm.
        let default_value = arm_value(emit, is_string);
        arms.push(format!("_ => {}", default_value));

        Some(format!("when {{ {} }}", arms.join(", ")))
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

    fn make_scope_with_i64(table: &SymbolTable) -> Scope<'_> {
        let mut scope = Scope::new(&[], table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope
    }

    fn default_params() -> Params {
        Params::from_iter([("probability", ParamValue::Probability(1.0))])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(NestedWhenExpr.name(), "nested_when_expr");
    }

    #[test]
    fn precondition_requires_i64_var() {
        let table = SymbolTable::new();
        let scope_empty = Scope::new(&[], &table);
        let params = default_params();
        assert!(!NestedWhenExpr.precondition(&scope_empty, &params));

        let scope_with_i64 = make_scope_with_i64(&table);
        assert!(NestedWhenExpr.precondition(&scope_with_i64, &params));
    }

    #[test]
    fn generates_nested_when_for_i64() {
        let table = SymbolTable::new();
        let scope = make_scope_with_i64(&table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = NestedWhenExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        // Outer when present.
        assert!(
            text.starts_with("when {"),
            "expected when expr, got: {text}"
        );
        // Contains a nested when.
        let when_count = text.matches("when {").count();
        assert!(
            when_count >= 2,
            "expected nested when (2+ occurrences), got {when_count} in: {text}"
        );
        // Has wildcard arm.
        assert!(text.contains("_ =>"), "expected wildcard arm, got: {text}");
    }

    #[test]
    fn generates_nested_when_for_string() {
        let table = SymbolTable::new();
        let scope = make_scope_with_i64(&table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = NestedWhenExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::String),
        );
        assert!(result.is_some());
        let text = result.unwrap();
        // Contains nested when.
        let when_count = text.matches("when {").count();
        assert!(
            when_count >= 2,
            "expected nested when (2+ occurrences), got {when_count} in: {text}"
        );
        // String literals present (quoted values).
        assert!(
            text.contains('"'),
            "expected string literals in arms, got: {text}"
        );
    }

    #[test]
    fn returns_none_for_unsupported_type() {
        let table = SymbolTable::new();
        let scope = make_scope_with_i64(&table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = default_params();

        let result = NestedWhenExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::Bool),
        );
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_i64_in_scope() {
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
        let params = default_params();

        let result = NestedWhenExpr.generate(
            &scope,
            &mut emit,
            &params,
            &TypeInfo::Primitive(PrimitiveType::I64),
        );
        assert!(result.is_none());
    }
}

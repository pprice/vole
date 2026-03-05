//! Rule: nested functions calling iterator methods on array parameters.
//!
//! Exercises function + iterator interaction by generating a nested helper
//! function and a call to it using an existing `[i64]` array variable.
//!
//! All variants use concrete `[i64]` types because nested `func<T>` is
//! rewritten to `let = lambda` by vole-fmt, and lambdas don't support
//! generic type params.
//!
//! **Pattern -- filter+sum:**
//! ```vole
//! func local0(arr: [i64], pred: (i64) -> bool) -> i64 {
//!     return arr.iter().filter(pred).sum()
//! }
//! let local1 = local0(nums, (x: i64) => x > 3)
//! ```
//!
//! **Pattern -- filter+count:**
//! ```vole
//! func local0(arr: [i64], pred: (i64) -> bool) -> i64 {
//!     return arr.iter().filter(pred).count()
//! }
//! let local1 = local0(nums, (x: i64) => x > 3)
//! ```
//!
//! **Pattern -- any:**
//! ```vole
//! func local0(arr: [i64], pred: (i64) -> bool) -> bool {
//!     return arr.iter().any(pred)
//! }
//! let local1 = local0(nums, (x: i64) => x > 3)
//! ```
//!
//! **Pattern -- all:**
//! ```vole
//! func local0(arr: [i64], pred: (i64) -> bool) -> bool {
//!     return arr.iter().all(pred)
//! }
//! let local1 = local0(nums, (x: i64) => x > 3)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct GenericIterCall;

impl StmtRule for GenericIterCall {
    fn name(&self) -> &'static str {
        "generic_iter_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        // Need at least one [i64] array in scope and room for a nested func.
        scope.can_recurse() && has_i64_array(scope)
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arr_var = pick_i64_array(scope, emit)?;
        let threshold = emit.gen_i64_range(0, 10);

        let variant = emit.gen_range(0..4);
        match variant {
            0 => emit_filter_sum(scope, emit, &arr_var, threshold),
            1 => emit_filter_count(scope, emit, &arr_var, threshold),
            2 => emit_any_match(scope, emit, &arr_var, threshold),
            _ => emit_all_match(scope, emit, &arr_var, threshold),
        }
    }
}

// ---------------------------------------------------------------------------
// Scope helpers
// ---------------------------------------------------------------------------

/// Check whether at least one `[i64]` array is in scope.
fn has_i64_array(scope: &Scope) -> bool {
    let i64_array = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
    scope.has_var_of_type(&i64_array)
}

/// Pick a random `[i64]` array variable from scope.
fn pick_i64_array(scope: &Scope, emit: &mut Emit) -> Option<String> {
    let i64_array = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
    let vars = scope.vars_of_type(&i64_array);
    if vars.is_empty() {
        return None;
    }
    let idx = emit.gen_range(0..vars.len());
    Some(vars[idx].name.clone())
}

// ---------------------------------------------------------------------------
// Variant: filter + sum (non-generic, since sum requires numeric)
// ---------------------------------------------------------------------------

/// ```vole
/// func sum_filtered_N(arr: [i64], pred: (i64) -> bool) -> i64 {
///     return arr.iter().filter(pred).sum()
/// }
/// let result = sum_filtered_N(arr_var, (x: i64) => x > K)
/// ```
fn emit_filter_sum(
    scope: &mut Scope,
    emit: &mut Emit,
    arr_var: &str,
    threshold: i64,
) -> Option<String> {
    let fn_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let indent = emit.indent_str();
    let body_indent = format!("{}    ", indent);

    let fn_def = format!(
        "func {}(arr: [i64], pred: (i64) -> bool) -> i64 {{\n\
         {}return arr.iter().filter(pred).sum()\n\
         {}}}",
        fn_name, body_indent, indent,
    );

    let call_expr = format!(
        "let {} = {}({}, (x: i64) => x > {})",
        result_name, fn_name, arr_var, threshold,
    );

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("{}\n{}{}", fn_def, indent, call_expr))
}

// ---------------------------------------------------------------------------
// Variant: filter + count (generic)
// ---------------------------------------------------------------------------

/// ```vole
/// func count_matching_N<T>(arr: [T], pred: (T) -> bool) -> i64 {
///     return arr.iter().filter(pred).count()
/// }
/// let result = count_matching_N(arr_var, (x: i64) => x > K)
/// ```
fn emit_filter_count(
    scope: &mut Scope,
    emit: &mut Emit,
    arr_var: &str,
    threshold: i64,
) -> Option<String> {
    let fn_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let indent = emit.indent_str();
    let body_indent = format!("{}    ", indent);

    let fn_def = format!(
        "func {}(arr: [i64], pred: (i64) -> bool) -> i64 {{\n\
         {}return arr.iter().filter(pred).count()\n\
         {}}}",
        fn_name, body_indent, indent,
    );

    let call_expr = format!(
        "let {} = {}({}, (x: i64) => x > {})",
        result_name, fn_name, arr_var, threshold,
    );

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::I64),
        false,
    );

    Some(format!("{}\n{}{}", fn_def, indent, call_expr))
}

// ---------------------------------------------------------------------------
// Variant: any (generic)
// ---------------------------------------------------------------------------

/// ```vole
/// func any_match_N<T>(arr: [T], pred: (T) -> bool) -> bool {
///     return arr.iter().any(pred)
/// }
/// let result = any_match_N(arr_var, (x: i64) => x > K)
/// ```
fn emit_any_match(
    scope: &mut Scope,
    emit: &mut Emit,
    arr_var: &str,
    threshold: i64,
) -> Option<String> {
    let fn_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let indent = emit.indent_str();
    let body_indent = format!("{}    ", indent);

    let fn_def = format!(
        "func {}(arr: [i64], pred: (i64) -> bool) -> bool {{\n\
         {}return arr.iter().any(pred)\n\
         {}}}",
        fn_name, body_indent, indent,
    );

    let call_expr = format!(
        "let {} = {}({}, (x: i64) => x > {})",
        result_name, fn_name, arr_var, threshold,
    );

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::Bool),
        false,
    );

    Some(format!("{}\n{}{}", fn_def, indent, call_expr))
}

// ---------------------------------------------------------------------------
// Variant: all (generic)
// ---------------------------------------------------------------------------

/// ```vole
/// func all_match_N<T>(arr: [T], pred: (T) -> bool) -> bool {
///     return arr.iter().all(pred)
/// }
/// let result = all_match_N(arr_var, (x: i64) => x > K)
/// ```
fn emit_all_match(
    scope: &mut Scope,
    emit: &mut Emit,
    arr_var: &str,
    threshold: i64,
) -> Option<String> {
    let fn_name = scope.fresh_name();
    let result_name = scope.fresh_name();
    let indent = emit.indent_str();
    let body_indent = format!("{}    ", indent);

    let fn_def = format!(
        "func {}(arr: [i64], pred: (i64) -> bool) -> bool {{\n\
         {}return arr.iter().all(pred)\n\
         {}}}",
        fn_name, body_indent, indent,
    );

    let call_expr = format!(
        "let {} = {}({}, (x: i64) => x > {})",
        result_name, fn_name, arr_var, threshold,
    );

    scope.add_local(
        result_name.clone(),
        TypeInfo::Primitive(PrimitiveType::Bool),
        false,
    );

    Some(format!("{}\n{}{}", fn_def, indent, call_expr))
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

    fn scope_with_i64_array(table: &SymbolTable) -> Scope<'_> {
        let mut scope = Scope::new(&[], table);
        scope.add_local(
            "nums".into(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        scope
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(GenericIterCall.name(), "generic_iter_call");
    }

    #[test]
    fn returns_none_without_i64_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            GenericIterCall
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn precondition_requires_i64_array() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!GenericIterCall.precondition(&scope, &params));

        let scope = scope_with_i64_array(&table);
        assert!(GenericIterCall.precondition(&scope, &params));
    }

    #[test]
    fn precondition_rejects_at_max_depth() {
        let table = SymbolTable::new();
        let mut scope = scope_with_i64_array(&table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!GenericIterCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_func_def_and_call() {
        let table = SymbolTable::new();
        let mut scope = scope_with_i64_array(&table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericIterCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("func "), "expected func keyword, got: {text}");
        assert!(text.contains("let "), "expected let binding, got: {text}");
        assert!(
            text.contains("(x: i64) =>"),
            "lambda must have explicit type annotation, got: {text}"
        );
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = scope_with_i64_array(&table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        GenericIterCall.generate(&mut scope, &mut emit, &params);
        // Should add 1 result local (func name is consumed by fresh_name but not
        // added as a local -- only the result binding is registered).
        assert!(scope.locals.len() > initial_len);
    }

    #[test]
    fn generates_all_variants() {
        let table = SymbolTable::new();
        let mut found_filter_sum = false;
        let mut found_filter_count = false;
        let mut found_any = false;
        let mut found_all = false;

        for seed in 0..200 {
            let mut scope = scope_with_i64_array(&table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericIterCall.generate(&mut scope, &mut emit, &params) {
                if text.contains(".filter(pred).sum()") {
                    found_filter_sum = true;
                }
                if text.contains(".filter(pred).count()") {
                    found_filter_count = true;
                }
                if text.contains(".any(pred)") {
                    found_any = true;
                }
                if text.contains(".all(pred)") {
                    found_all = true;
                }
            }
        }
        assert!(found_filter_sum, "never generated filter+sum variant");
        assert!(found_filter_count, "never generated filter+count variant");
        assert!(found_any, "never generated any variant");
        assert!(found_all, "never generated all variant");
    }

    #[test]
    fn uses_existing_array_variable() {
        let table = SymbolTable::new();
        let mut scope = scope_with_i64_array(&table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = GenericIterCall.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains("(nums,"),
            "expected call with existing array var, got: {text}"
        );
    }

    #[test]
    fn all_variants_use_concrete_i64() {
        let table = SymbolTable::new();
        for seed in 0..200 {
            let mut scope = scope_with_i64_array(&table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = GenericIterCall.generate(&mut scope, &mut emit, &params) {
                assert!(
                    text.contains("[i64]"),
                    "all variants should use concrete [i64], got: {text}"
                );
                assert!(
                    !text.contains("<T>"),
                    "no variant should use generic <T> (nested func limitation), got: {text}"
                );
            }
        }
    }
}

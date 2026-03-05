//! Rule: for-loop over array with `when` classification, accumulating a result.
//!
//! Generates a for-loop over an i64 array where a `when` expression classifies
//! each element, accumulating the result into a `var`.  Combines iteration +
//! conditional branching + accumulation.
//!
//! Three variants:
//! 1. **sum_classified** – multiply large values by 10, keep small as-is, sum.
//! 2. **count_classified** – count elements matching a condition.
//! 3. **build_string** – concatenate a category string per element.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForWhenAccum;

impl StmtRule for ForWhenAccum {
    fn name(&self) -> &'static str {
        "for_when_accum"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Find or create an i64 array to iterate over.
        let arr_expr = pick_or_create_i64_array(scope, emit)?;

        let variant = emit.gen_range(0..3);
        match variant {
            0 => Some(gen_sum_classified(scope, emit, &arr_expr)),
            1 => Some(gen_count_classified(scope, emit, &arr_expr)),
            _ => Some(gen_build_string(scope, emit, &arr_expr)),
        }
    }
}

/// Try to pick an existing i64 array from scope, or generate a literal.
fn pick_or_create_i64_array(scope: &Scope, emit: &mut Emit) -> Option<String> {
    let i64_arrays: Vec<String> = scope
        .array_vars()
        .into_iter()
        .filter(|(_, elem)| matches!(elem, TypeInfo::Primitive(PrimitiveType::I64)))
        .map(|(name, _)| name)
        .collect();

    if !i64_arrays.is_empty() && emit.gen_bool(0.6) {
        let idx = emit.gen_range(0..i64_arrays.len());
        Some(i64_arrays[idx].clone())
    } else {
        Some(gen_i64_array_literal(emit))
    }
}

/// Generate a literal i64 array with 3-5 elements.
fn gen_i64_array_literal(emit: &mut Emit) -> String {
    let len = emit.random_in(3, 5);
    let elems: Vec<String> = (0..len)
        .map(|_| emit.gen_i64_range(0, 10).to_string())
        .collect();
    format!("[{}]", elems.join(", "))
}

/// Random threshold in 2..=8.
fn random_threshold(emit: &mut Emit) -> i64 {
    emit.gen_i64_range(2, 8)
}

// ---------------------------------------------------------------------------
// Variant 1: sum_classified
// ---------------------------------------------------------------------------

fn gen_sum_classified(scope: &mut Scope, emit: &mut Emit, arr_expr: &str) -> String {
    let acc = scope.fresh_name();
    let iter_var = scope.fresh_name();
    let threshold = random_threshold(emit);
    let multiplier = emit.gen_i64_range(2, 10);
    let indent = emit.indent_str();

    scope.add_local(acc.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(acc.clone());

    format!(
        "var {acc} = 0\n\
         {indent}for {iter_var} in {arr_expr} {{\n\
         {indent}    let {add} = when {{\n\
         {indent}        {iter_var} > {threshold} => {iter_var} * {multiplier}\n\
         {indent}        _ => {iter_var}\n\
         {indent}    }}\n\
         {indent}    {acc} = {acc} + {add}\n\
         {indent}}}",
        acc = acc,
        iter_var = iter_var,
        arr_expr = arr_expr,
        threshold = threshold,
        multiplier = multiplier,
        add = scope.fresh_name(),
        indent = indent,
    )
}

// ---------------------------------------------------------------------------
// Variant 2: count_classified
// ---------------------------------------------------------------------------

fn gen_count_classified(scope: &mut Scope, emit: &mut Emit, arr_expr: &str) -> String {
    let count = scope.fresh_name();
    let iter_var = scope.fresh_name();
    let threshold = random_threshold(emit);
    let indent = emit.indent_str();

    scope.add_local(count.clone(), TypeInfo::Primitive(PrimitiveType::I64), true);
    scope.protected_vars.push(count.clone());

    format!(
        "var {count} = 0\n\
         {indent}for {iter_var} in {arr_expr} {{\n\
         {indent}    {count} = {count} + when {{\n\
         {indent}        {iter_var} > {threshold} => 1\n\
         {indent}        _ => 0\n\
         {indent}    }}\n\
         {indent}}}",
        count = count,
        iter_var = iter_var,
        arr_expr = arr_expr,
        threshold = threshold,
        indent = indent,
    )
}

// ---------------------------------------------------------------------------
// Variant 3: build_string
// ---------------------------------------------------------------------------

fn gen_build_string(scope: &mut Scope, emit: &mut Emit, arr_expr: &str) -> String {
    let result = scope.fresh_name();
    let iter_var = scope.fresh_name();
    let threshold = random_threshold(emit);
    let indent = emit.indent_str();

    let labels = [
        ("\"big\"", "\"small\""),
        ("\"high\"", "\"low\""),
        ("\"yes\"", "\"no\""),
        ("\"hot\"", "\"cold\""),
    ];
    let (label_hi, label_lo) = labels[emit.gen_range(0..labels.len())];

    scope.add_local(
        result.clone(),
        TypeInfo::Primitive(PrimitiveType::String),
        true,
    );
    scope.protected_vars.push(result.clone());

    format!(
        "var {result} = \"\"\n\
         {indent}for {iter_var} in {arr_expr} {{\n\
         {indent}    {result} = {result} + when {{\n\
         {indent}        {iter_var} > {threshold} => {label_hi}\n\
         {indent}        _ => {label_lo}\n\
         {indent}    }} + \",\"\n\
         {indent}}}",
        result = result,
        iter_var = iter_var,
        arr_expr = arr_expr,
        threshold = threshold,
        label_hi = label_hi,
        label_lo = label_lo,
        indent = indent,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, SymbolTable};
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
        assert_eq!(ForWhenAccum.name(), "for_when_accum");
    }

    #[test]
    fn returns_none_at_max_depth() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ForWhenAccum.precondition(&scope, &params));
    }

    #[test]
    fn generates_with_literal_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ForWhenAccum.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("var "), "expected var, got: {text}");
        assert!(text.contains("for "), "expected for, got: {text}");
        assert!(text.contains("when"), "expected when, got: {text}");
        assert!(text.contains("["), "expected array literal, got: {text}");
    }

    #[test]
    fn generates_with_existing_array() {
        let table = SymbolTable::new();
        let params_info = &[ParamInfo {
            name: "nums".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params_info, &table);

        // Try multiple seeds to hit the path that picks an existing array
        let resolved = ResolvedParams::new();
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let mut found_existing = false;
        for seed in 0..30 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            if let Some(text) = ForWhenAccum.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("in nums") {
                    found_existing = true;
                    break;
                }
            }
        }
        assert!(
            found_existing,
            "expected at least one generation using existing array"
        );
    }

    #[test]
    fn all_three_variants_reachable() {
        let table = SymbolTable::new();
        let resolved = ResolvedParams::new();
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let mut found_sum = false;
        let mut found_count = false;
        let mut found_string = false;

        for seed in 0..100 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let mut emit = test_emit(&mut rng, &resolved);
            if let Some(text) = ForWhenAccum.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("var ") && text.contains("= 0\n") && text.contains("let ") {
                    found_sum = true;
                } else if text.contains("=> 1") && text.contains("=> 0") {
                    found_count = true;
                } else if text.contains("\"\"") && text.contains("+ \",\"") {
                    found_string = true;
                }
            }
            if found_sum && found_count && found_string {
                break;
            }
        }

        assert!(found_sum, "sum_classified variant not reached");
        assert!(found_count, "count_classified variant not reached");
        assert!(found_string, "build_string variant not reached");
    }
}

//! Rule: function call with many parameters (8-16).
//!
//! Generates a local function with 8-16 parameters of mixed types
//! (i64, i32, f64, bool, string), a body that combines multiple
//! parameters with simple arithmetic/string ops, then immediately
//! calls the function with literals or scope variables.
//!
//! This stresses calling conventions, register allocation, and stack
//! layout -- areas where bugs tend to hide when the parameter count
//! exceeds the number of available argument registers.
//!
//! ```vole
//! func local0(p0: i64, p1: i32, p2: f64, p3: bool, p4: string,
//!             p5: i64, p6: i32, p7: f64, p8: bool, p9: string) -> i64 {
//!     let acc0 = p0
//!     let acc1 = acc0 + p5
//!     return acc1
//! }
//! let local1 = local0(1_i64, 2_i32, 3.14_f64, true, "hi", ...)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ManyParamsCall;

/// The parameter types we draw from.
const PARAM_TYPES: &[PrimitiveType] = &[
    PrimitiveType::I64,
    PrimitiveType::I32,
    PrimitiveType::F64,
    PrimitiveType::Bool,
    PrimitiveType::String,
];

impl StmtRule for ManyParamsCall {
    fn name(&self) -> &'static str {
        "many_params_call"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick how many parameters: 8..=16
        let num_params = emit.random_in(8, 16);

        // Choose a return type: i64, string, or bool.
        let return_prim = match emit.gen_range(0..3) {
            0 => PrimitiveType::I64,
            1 => PrimitiveType::String,
            _ => PrimitiveType::Bool,
        };
        let return_type = TypeInfo::Primitive(return_prim);

        // Generate parameter list with mixed types.
        let mut param_prims: Vec<PrimitiveType> = Vec::with_capacity(num_params);
        for _ in 0..num_params {
            let idx = emit.gen_range(0..PARAM_TYPES.len());
            param_prims.push(PARAM_TYPES[idx]);
        }

        // Ensure we have at least one param matching the return type so the
        // body can trivially return something type-correct.
        if !param_prims.contains(&return_prim) {
            let replace_idx = emit.gen_range(0..num_params);
            param_prims[replace_idx] = return_prim;
        }

        // Build the parameter signature: "p0: i64, p1: i32, ..."
        let param_sig: Vec<String> = param_prims
            .iter()
            .enumerate()
            .map(|(i, prim)| format!("p{}: {}", i, prim.as_str()))
            .collect();

        // Build the function body. Reference 4+ parameters.
        let indent = emit.indent_str();
        let body_indent = format!("{}        ", indent); // 2 extra levels inside func
        let body = build_body(emit, &param_prims, return_prim, &body_indent);

        // Function name and call result name.
        let fn_name = scope.fresh_name();
        let result_name = scope.fresh_name();

        // Build function definition.
        let fn_def = format!(
            "func {}({}) -> {} {{\n{}\n{}    }}",
            fn_name,
            param_sig.join(", "),
            return_prim.as_str(),
            body,
            indent,
        );

        // Build call arguments -- use literals for each parameter type.
        let call_args: Vec<String> = param_prims
            .iter()
            .map(|prim| emit.literal(&TypeInfo::Primitive(*prim)))
            .collect();

        let call_stmt = format!(
            "let {} = {}({})",
            result_name,
            fn_name,
            call_args.join(", "),
        );

        // Register the result in scope.
        scope.add_local(result_name, return_type, false);

        Some(format!("{}\n{}{}", fn_def, indent, call_stmt))
    }
}

/// Build a function body that references at least 4 parameters and returns `return_prim`.
fn build_body(
    emit: &mut Emit,
    param_prims: &[PrimitiveType],
    return_prim: PrimitiveType,
    indent: &str,
) -> String {
    match return_prim {
        PrimitiveType::I64 => build_i64_body(emit, param_prims, indent),
        PrimitiveType::String => build_string_body(emit, param_prims, indent),
        PrimitiveType::Bool => build_bool_body(emit, param_prims, indent),
        _ => unreachable!("return_prim is always i64, string, or bool"),
    }
}

/// Build an i64-returning body that accumulates values from multiple params.
fn build_i64_body(emit: &mut Emit, param_prims: &[PrimitiveType], indent: &str) -> String {
    let mut lines = Vec::new();

    // Collect indices of i64 params only — Vole has no .to_i64() conversion
    // method, so we can only directly add i64 values.
    let numeric_indices: Vec<usize> = param_prims
        .iter()
        .enumerate()
        .filter(|(_, p)| matches!(p, PrimitiveType::I64))
        .map(|(i, _)| i)
        .collect();

    // Pick at least 4 params to reference (mix of numeric and others).
    let use_count = emit.random_in(4, numeric_indices.len().min(8).max(4));

    // Start accumulator from the first i64 param (guaranteed to exist since
    // we ensure at least one param matches the return type).
    let first_idx = find_first_of(param_prims, PrimitiveType::I64).unwrap_or(0);

    let first_expr = format!("p{}", first_idx);
    lines.push(format!("{}let acc0 = {}", indent, first_expr));

    let mut acc_counter = 0;
    let mut used = 1;

    // Add more params to the accumulator.
    for &idx in numeric_indices.iter() {
        if idx == first_idx {
            continue;
        }
        if used >= use_count {
            break;
        }
        let expr = format!("p{}", idx); // always i64 since numeric_indices is filtered
        let op = if emit.gen_bool(0.7) { "+" } else { "-" };
        let new_acc = format!("acc{}", acc_counter + 1);
        lines.push(format!(
            "{}let {} = acc{} {} {}",
            indent, new_acc, acc_counter, op, expr
        ));
        acc_counter += 1;
        used += 1;
    }

    // If we still need more references, add bool/string length checks.
    if used < 4 {
        for (i, prim) in param_prims.iter().enumerate() {
            if used >= 4 {
                break;
            }
            match prim {
                PrimitiveType::Bool => {
                    let new_acc = format!("acc{}", acc_counter + 1);
                    lines.push(format!(
                        "{}let {} = acc{} + when {{ p{} => 1 _ => 0 }}",
                        indent, new_acc, acc_counter, i
                    ));
                    acc_counter += 1;
                    used += 1;
                }
                PrimitiveType::String => {
                    let new_acc = format!("acc{}", acc_counter + 1);
                    lines.push(format!(
                        "{}let {} = acc{} + p{}.length()",
                        indent, new_acc, acc_counter, i
                    ));
                    acc_counter += 1;
                    used += 1;
                }
                _ => {}
            }
        }
    }

    lines.push(format!("{}return acc{}", indent, acc_counter));
    lines.join("\n")
}

/// Build a string-returning body that concatenates values from multiple params.
fn build_string_body(emit: &mut Emit, param_prims: &[PrimitiveType], indent: &str) -> String {
    let mut lines = Vec::new();

    // Find string params.
    let string_indices: Vec<usize> = param_prims
        .iter()
        .enumerate()
        .filter(|(_, p)| matches!(p, PrimitiveType::String))
        .map(|(i, _)| i)
        .collect();

    // Start from the first string param.
    let first_str = string_indices.first().copied().unwrap_or(0);
    if param_prims[first_str] == PrimitiveType::String {
        lines.push(format!("{}let acc0 = p{}", indent, first_str));
    } else {
        lines.push(format!("{}let acc0 = p{}.to_string()", indent, first_str));
    }

    let mut acc_counter = 0;
    let mut used = 1;
    let use_count = emit.random_in(4, 6);

    // Concatenate more params via .to_string() interpolation.
    for (i, prim) in param_prims.iter().enumerate() {
        if i == first_str {
            continue;
        }
        if used >= use_count {
            break;
        }
        let new_acc = format!("acc{}", acc_counter + 1);
        match prim {
            PrimitiveType::String => {
                lines.push(format!(
                    "{}let {} = acc{} + p{}",
                    indent, new_acc, acc_counter, i,
                ));
            }
            _ => {
                lines.push(format!(
                    "{}let {} = acc{} + p{}.to_string()",
                    indent, new_acc, acc_counter, i,
                ));
            }
        }
        acc_counter += 1;
        used += 1;
    }

    lines.push(format!("{}return acc{}", indent, acc_counter));
    lines.join("\n")
}

/// Build a bool-returning body that combines conditions on multiple params.
fn build_bool_body(emit: &mut Emit, param_prims: &[PrimitiveType], indent: &str) -> String {
    let mut lines = Vec::new();

    // Build conditions referencing at least 4 params.
    let mut conds: Vec<String> = Vec::new();

    for (i, prim) in param_prims.iter().enumerate() {
        if conds.len() >= 6 {
            break;
        }
        match prim {
            PrimitiveType::I64 => {
                let threshold = emit.gen_i64_range(0, 100);
                conds.push(format!("p{} > {}_i64", i, threshold));
            }
            PrimitiveType::I32 => {
                let threshold = emit.gen_i64_range(0, 50);
                conds.push(format!("p{} > {}_i32", i, threshold));
            }
            PrimitiveType::F64 => {
                let threshold = emit.gen_i64_range(0, 50);
                conds.push(format!("p{} > {}.0_f64", i, threshold));
            }
            PrimitiveType::Bool => {
                conds.push(format!("p{}", i));
            }
            PrimitiveType::String => {
                let len = emit.gen_i64_range(0, 5);
                conds.push(format!("p{}.length() > {}", i, len));
            }
            _ => {}
        }
    }

    // Ensure at least 4 conditions.
    while conds.len() < 4 {
        conds.push("true".to_string());
    }

    // Combine conditions with && and || operators.
    // Split into pairs joined by &&, then join pairs with ||.
    let half = conds.len() / 2;
    let left = conds[..half].join(" && ");
    let right = conds[half..].join(" && ");
    let combined = format!("({}) || ({})", left, right);

    lines.push(format!("{}let result = {}", indent, combined));
    lines.push(format!("{}return result", indent));
    lines.join("\n")
}

/// Find the first parameter of a given type.
fn find_first_of(param_prims: &[PrimitiveType], target: PrimitiveType) -> Option<usize> {
    param_prims.iter().position(|p| *p == target)
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

    #[test]
    fn name_is_correct() {
        assert_eq!(ManyParamsCall.name(), "many_params_call");
    }

    #[test]
    fn generates_function_and_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ManyParamsCall.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("func "), "expected func keyword, got: {text}");
        assert!(text.contains("return "), "expected return, got: {text}");
        // Should have the call on a separate line.
        assert!(
            text.contains("let local1 = local0("),
            "expected call, got: {text}"
        );
    }

    #[test]
    fn generates_many_parameters() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        // Try several seeds to check parameter counts.
        for seed in 0..10 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &rule_params) {
                // Count occurrences of "p" followed by a digit and ":" in the func signature.
                let sig_line = text.lines().next().unwrap();
                let param_count = sig_line.matches(": ").count();
                assert!(
                    param_count >= 8,
                    "expected >=8 params, got {} for seed {}. sig: {}",
                    param_count,
                    seed,
                    sig_line,
                );
            }
        }
    }

    #[test]
    fn adds_result_local_to_scope() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        ManyParamsCall.generate(&mut scope, &mut emit, &rule_params);
        // Should add 1 local (the call result).
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!ManyParamsCall.precondition(&scope, &params));
    }

    #[test]
    fn generates_all_return_types() {
        let table = SymbolTable::new();
        let mut found_i64 = false;
        let mut found_string = false;
        let mut found_bool = false;

        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = ManyParamsCall.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("-> i64") {
                    found_i64 = true;
                }
                if text.contains("-> string") {
                    found_string = true;
                }
                if text.contains("-> bool") {
                    found_bool = true;
                }
            }
        }
        assert!(found_i64, "never generated i64 return type");
        assert!(found_string, "never generated string return type");
        assert!(found_bool, "never generated bool return type");
    }
}

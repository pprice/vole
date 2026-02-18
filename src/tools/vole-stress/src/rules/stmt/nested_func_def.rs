//! Rule: nested function definition inside the current scope.
//!
//! Generates a `func` definition nested inside the current function body,
//! optionally capturing immutable variables from the enclosing scope, then
//! immediately calls the nested function and binds the result.
//!
//! This stresses scope resolution, variable capture, and codegen for nested
//! `func` declarations.
//!
//! ```vole
//! func inner(y: i64) -> i64 {
//!     return y * factor + x
//! }
//! let result = inner(10)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedFuncDef;

/// The primitive types we use for nested function parameters.
const PARAM_TYPES: &[PrimitiveType] = &[
    PrimitiveType::I64,
    PrimitiveType::String,
    PrimitiveType::Bool,
];

impl StmtRule for NestedFuncDef {
    fn name(&self) -> &'static str {
        "nested_func_def"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.025)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Pick 1-3 parameters for the nested function.
        let num_params = emit.random_in(1, 3);

        // Choose a return type from i64, string, or bool.
        let return_prim = match emit.gen_range(0..3) {
            0 => PrimitiveType::I64,
            1 => PrimitiveType::String,
            _ => PrimitiveType::Bool,
        };
        let return_type = TypeInfo::Primitive(return_prim);

        // Generate parameter types.
        let mut param_prims: Vec<PrimitiveType> = Vec::with_capacity(num_params);
        for _ in 0..num_params {
            let idx = emit.gen_range(0..PARAM_TYPES.len());
            param_prims.push(PARAM_TYPES[idx]);
        }

        // Ensure at least one parameter matches the return type so the body
        // can trivially produce a type-correct return value.
        if !param_prims.contains(&return_prim) {
            let replace_idx = emit.gen_range(0..num_params);
            param_prims[replace_idx] = return_prim;
        }

        // Try to find an immutable variable to capture from the enclosing scope.
        // Only capture variables whose type matches one of the primitive types
        // we know how to use in the body expression.
        let capture = find_capturable_var(scope, emit, return_prim);

        // Build the parameter signature: "p0: i64, p1: string, ..."
        let param_sig: Vec<String> = param_prims
            .iter()
            .enumerate()
            .map(|(i, prim)| format!("p{}: {}", i, prim.as_str()))
            .collect();

        // Build the function body.
        let indent = emit.indent_str();
        let body_indent = format!("{}        ", indent); // 2 extra levels inside func
        let body = build_body(emit, &param_prims, return_prim, &capture, &body_indent);

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

/// Information about a captured variable from the enclosing scope.
struct CaptureInfo {
    /// The name of the captured variable.
    name: String,
    /// The primitive type of the captured variable.
    prim: PrimitiveType,
}

/// Find an immutable variable in scope that can be captured by the nested function.
///
/// Looks for immutable locals of type i64, string, or bool. Returns `None` if
/// no suitable variable is found or if the RNG decides not to capture.
fn find_capturable_var(
    scope: &Scope,
    emit: &mut Emit,
    return_prim: PrimitiveType,
) -> Option<CaptureInfo> {
    // 60% chance to try capturing a variable.
    if !emit.gen_bool(0.6) {
        return None;
    }

    // Prefer capturing a variable whose type matches the return type, since
    // that makes the body expression simpler and more likely to type-check.
    let preferred_type = TypeInfo::Primitive(return_prim);
    let candidates: Vec<_> = scope
        .vars_matching(|v| {
            !v.is_mutable
                && matches!(
                    v.type_info,
                    TypeInfo::Primitive(PrimitiveType::I64)
                        | TypeInfo::Primitive(PrimitiveType::String)
                        | TypeInfo::Primitive(PrimitiveType::Bool)
                )
        })
        .into_iter()
        .collect();

    if candidates.is_empty() {
        return None;
    }

    // Try to find one matching the return type first.
    let matching: Vec<_> = candidates
        .iter()
        .filter(|v| matches_type(&v.type_info, &preferred_type))
        .collect();

    let chosen = if !matching.is_empty() {
        let idx = emit.gen_range(0..matching.len());
        matching[idx]
    } else {
        let idx = emit.gen_range(0..candidates.len());
        &candidates[idx]
    };

    let prim = match &chosen.type_info {
        TypeInfo::Primitive(p) => *p,
        _ => return None,
    };

    Some(CaptureInfo {
        name: chosen.name.clone(),
        prim,
    })
}

/// Simple structural type equality check.
fn matches_type(a: &TypeInfo, b: &TypeInfo) -> bool {
    matches!((a, b), (TypeInfo::Primitive(pa), TypeInfo::Primitive(pb)) if pa == pb)
}

/// Build the function body based on the return type.
fn build_body(
    emit: &mut Emit,
    param_prims: &[PrimitiveType],
    return_prim: PrimitiveType,
    capture: &Option<CaptureInfo>,
    indent: &str,
) -> String {
    match return_prim {
        PrimitiveType::I64 => build_i64_body(emit, param_prims, capture, indent),
        PrimitiveType::String => build_string_body(emit, param_prims, capture, indent),
        PrimitiveType::Bool => build_bool_body(emit, param_prims, capture, indent),
        _ => unreachable!("return_prim is always i64, string, or bool"),
    }
}

/// Build an i64-returning body.
fn build_i64_body(
    emit: &mut Emit,
    param_prims: &[PrimitiveType],
    capture: &Option<CaptureInfo>,
    indent: &str,
) -> String {
    let mut lines = Vec::new();

    // Find the first i64 parameter.
    let first_i64 = param_prims
        .iter()
        .position(|p| matches!(p, PrimitiveType::I64))
        .unwrap_or(0);

    lines.push(format!("{}let acc = p{}", indent, first_i64));

    // If we have a captured i64 variable, add it.
    if let Some(cap) = capture {
        if matches!(cap.prim, PrimitiveType::I64) {
            let op = if emit.gen_bool(0.5) { "+" } else { "*" };
            lines.push(format!("{}let acc2 = acc {} {}", indent, op, cap.name));
            lines.push(format!("{}return acc2", indent));
            return lines.join("\n");
        }
    }

    // Use a constant offset.
    let offset = emit.random_in(1, 20);
    let op = if emit.gen_bool(0.7) { "+" } else { "*" };
    lines.push(format!("{}let acc2 = acc {} {}", indent, op, offset));
    lines.push(format!("{}return acc2", indent));
    lines.join("\n")
}

/// Build a string-returning body.
fn build_string_body(
    emit: &mut Emit,
    param_prims: &[PrimitiveType],
    capture: &Option<CaptureInfo>,
    indent: &str,
) -> String {
    let mut lines = Vec::new();

    // Find the first string parameter.
    let first_str = param_prims
        .iter()
        .position(|p| matches!(p, PrimitiveType::String))
        .unwrap_or(0);

    if param_prims[first_str] == PrimitiveType::String {
        lines.push(format!("{}let acc = p{}", indent, first_str));
    } else {
        lines.push(format!("{}let acc = p{}.to_string()", indent, first_str));
    }

    // If we have a captured string variable, concatenate it.
    if let Some(cap) = capture {
        if matches!(cap.prim, PrimitiveType::String) {
            lines.push(format!("{}let acc2 = acc + {}", indent, cap.name));
            lines.push(format!("{}return acc2", indent));
            return lines.join("\n");
        }
    }

    // Concatenate a literal suffix.
    let suffix_id = emit.random_in(0, 99);
    lines.push(format!("{}let acc2 = acc + \"_s{}\"", indent, suffix_id));
    lines.push(format!("{}return acc2", indent));
    lines.join("\n")
}

/// Build a bool-returning body.
fn build_bool_body(
    emit: &mut Emit,
    param_prims: &[PrimitiveType],
    capture: &Option<CaptureInfo>,
    indent: &str,
) -> String {
    let mut lines = Vec::new();

    // Find the first bool parameter.
    let first_bool = param_prims
        .iter()
        .position(|p| matches!(p, PrimitiveType::Bool))
        .unwrap_or(0);

    if param_prims[first_bool] == PrimitiveType::Bool {
        lines.push(format!("{}let cond = p{}", indent, first_bool));
    } else {
        // Fall back: compare an i64 param to a threshold.
        let threshold = emit.random_in(0, 50);
        lines.push(format!(
            "{}let cond = p{} > {}_i64",
            indent, first_bool, threshold
        ));
    }

    // If we have a captured bool variable, combine with it.
    if let Some(cap) = capture {
        if matches!(cap.prim, PrimitiveType::Bool) {
            let combiner = if emit.gen_bool(0.5) { "&&" } else { "||" };
            lines.push(format!(
                "{}let cond2 = cond {} {}",
                indent, combiner, cap.name
            ));
            lines.push(format!("{}return cond2", indent));
            return lines.join("\n");
        }
    }

    lines.push(format!("{}return cond", indent));
    lines.join("\n")
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
        assert_eq!(NestedFuncDef.name(), "nested_func_def");
    }

    #[test]
    fn generates_function_and_call() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedFuncDef.generate(&mut scope, &mut emit, &rule_params);
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
    fn generates_with_capture() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        // Add an immutable i64 local that can be captured.
        scope.add_local(
            "factor".into(),
            TypeInfo::Primitive(PrimitiveType::I64),
            false,
        );

        // Try many seeds to find one that captures.
        let mut found_capture = false;
        for seed in 0..50 {
            let mut scope_copy = Scope::new(&[], &table);
            scope_copy.add_local(
                "factor".into(),
                TypeInfo::Primitive(PrimitiveType::I64),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = NestedFuncDef.generate(&mut scope_copy, &mut emit, &rule_params) {
                if text.contains("factor") {
                    found_capture = true;
                    break;
                }
            }
        }
        assert!(found_capture, "never generated a capture across 50 seeds");
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

        NestedFuncDef.generate(&mut scope, &mut emit, &rule_params);
        // Should add 1 local (the call result).
        assert_eq!(scope.locals.len(), initial_len + 1);
    }

    #[test]
    fn respects_depth_limit() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.depth = scope.max_depth;
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(!NestedFuncDef.precondition(&scope, &params));
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

            if let Some(text) = NestedFuncDef.generate(&mut scope, &mut emit, &rule_params) {
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

    #[test]
    fn does_not_capture_mutable_vars() {
        let table = SymbolTable::new();

        // Only provide a mutable variable -- capture should not use it.
        let mut found_capture = false;
        for seed in 0..50 {
            let mut scope = Scope::new(&[], &table);
            scope.add_local(
                "mut_var".into(),
                TypeInfo::Primitive(PrimitiveType::I64),
                true, // mutable!
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            if let Some(text) = NestedFuncDef.generate(&mut scope, &mut emit, &rule_params) {
                if text.contains("mut_var") {
                    found_capture = true;
                }
            }
        }
        assert!(!found_capture, "should never capture mutable variables");
    }
}

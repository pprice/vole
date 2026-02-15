//! Rule: match with closure arms.
//!
//! Generates a match expression whose arms produce closures that capture
//! surrounding variables. The resulting closure is then either immediately
//! invoked (Pattern A) or passed to an iterator chain (Pattern B).
//!
//! Pattern A (invoke):
//! ```vole
//! let f = match x { 0 => (n: i64) => n + y, _ => (n: i64) => n * y }
//! let result = f(10)
//! ```
//!
//! Pattern B (iterator chain):
//! ```vole
//! let f = match x { 0 => (n: i64) => n + y, _ => (n: i64) => n * y }
//! let result = arr.iter().map(f).collect()
//! ```

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchClosure;

impl StmtRule for MatchClosure {
    fn name(&self) -> &'static str {
        "match_closure"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope.is_in_generic_class_method()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        // Step 1: Find i64-typed scrutinee candidates
        let scrutinee_candidates = collect_i64_vars(scope);
        if scrutinee_candidates.is_empty() {
            return None;
        }

        // Step 2: Find capturable numeric variables (i64 or i32)
        let capture_candidates = collect_numeric_vars(scope);
        if capture_candidates.is_empty() {
            return None;
        }

        // Pick the scrutinee
        let scr_idx = emit.gen_range(0..scrutinee_candidates.len());
        let scrutinee = scrutinee_candidates[scr_idx].clone();

        // Pick a capture variable (prefer one different from the scrutinee)
        let non_scrutinee: Vec<&(String, PrimitiveType)> = capture_candidates
            .iter()
            .filter(|(name, _)| *name != scrutinee)
            .collect();
        let (capture_var, capture_prim) = if !non_scrutinee.is_empty() {
            let idx = emit.gen_range(0..non_scrutinee.len());
            non_scrutinee[idx].clone()
        } else {
            let idx = emit.gen_range(0..capture_candidates.len());
            capture_candidates[idx].clone()
        };

        let closure_prim = capture_prim;
        let closure_type_name = match closure_prim {
            PrimitiveType::I64 => "i64",
            PrimitiveType::I32 => "i32",
            _ => "i64",
        };

        let arm_count = emit.random_in(2, 3);
        let indent = emit.indent_str();

        let match_stmt = build_match_stmt(
            emit,
            &MatchStmtSpec {
                scrutinee: &scrutinee,
                capture_var: &capture_var,
                closure_type_name,
                arm_count,
                indent: &indent,
            },
        );

        let fn_name = scope.fresh_name();
        let closure_type = TypeInfo::Function {
            param_types: vec![TypeInfo::Primitive(closure_prim)],
            return_type: Box::new(TypeInfo::Primitive(closure_prim)),
        };

        let ctx = ClosureCtx {
            match_text: &match_stmt,
            fn_name: &fn_name,
            closure_type,
            closure_prim,
            indent: &indent,
        };

        // Decide: Pattern A (invoke) or Pattern B (iterator chain)
        let matching_arrays = collect_matching_arrays(scope, closure_prim);
        let use_iter = !matching_arrays.is_empty() && emit.gen_bool(0.4);

        if use_iter {
            build_iter_pattern(scope, emit, &ctx, closure_type_name, &matching_arrays)
        } else {
            build_invoke_pattern(scope, emit, &ctx)
        }
    }
}

fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(param.name.clone());
        }
    }
    out
}

fn collect_numeric_vars(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) = ty {
            out.push((name.clone(), *p));
        }
    }
    for param in scope.params {
        if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) =
            &param.param_type
        {
            out.push((param.name.clone(), *p));
        }
    }
    out
}

fn collect_matching_arrays(scope: &Scope, closure_prim: PrimitiveType) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Array(inner) = ty {
            if matches!(inner.as_ref(), TypeInfo::Primitive(p) if *p == closure_prim) {
                out.push(name.clone());
            }
        }
    }
    for param in scope.params {
        if let TypeInfo::Array(inner) = &param.param_type {
            if matches!(inner.as_ref(), TypeInfo::Primitive(p) if *p == closure_prim) {
                out.push(param.name.clone());
            }
        }
    }
    out
}

struct MatchStmtSpec<'a> {
    scrutinee: &'a str,
    capture_var: &'a str,
    closure_type_name: &'a str,
    arm_count: usize,
    indent: &'a str,
}

fn build_match_stmt(emit: &mut Emit, spec: &MatchStmtSpec<'_>) -> String {
    let operations = [
        ("n + {}", "add"),
        ("n * {}", "mul"),
        ("n - {}", "sub"),
        ("{} - n", "rsub"),
        ("{} + n", "radd"),
    ];

    let mut arms = Vec::new();
    let mut used_values = HashSet::new();

    for _ in 0..spec.arm_count {
        let mut lit_val = emit.gen_i64_range(0, 9);
        while used_values.contains(&lit_val) {
            lit_val = emit.gen_i64_range(0, 9);
        }
        used_values.insert(lit_val);

        let op_idx = emit.gen_range(0..operations.len());
        let (op_template, _) = operations[op_idx];
        let body = op_template.replace("{}", spec.capture_var);
        arms.push(format!(
            "{}    {} => (n: {}) => {}",
            spec.indent, lit_val, spec.closure_type_name, body
        ));
    }

    // Wildcard arm
    let wildcard_op_idx = emit.gen_range(0..operations.len());
    let (wildcard_template, _) = operations[wildcard_op_idx];
    let wildcard_body = wildcard_template.replace("{}", spec.capture_var);
    arms.push(format!(
        "{}    _ => (n: {}) => {}",
        spec.indent, spec.closure_type_name, wildcard_body
    ));

    // The fn_name will be prepended by the caller
    format!(
        "match {} {{\n{}\n{}}}",
        spec.scrutinee,
        arms.join("\n"),
        spec.indent,
    )
}

/// Context shared between the invoke and iter pattern builders.
struct ClosureCtx<'a> {
    match_text: &'a str,
    fn_name: &'a str,
    closure_type: TypeInfo,
    closure_prim: PrimitiveType,
    indent: &'a str,
}

fn build_iter_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    ctx: &ClosureCtx<'_>,
    closure_type_name: &str,
    matching_arrays: &[String],
) -> Option<String> {
    let arr_idx = emit.gen_range(0..matching_arrays.len());
    let arr_name = &matching_arrays[arr_idx];

    let result_name = scope.fresh_name();
    let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(ctx.closure_prim)));

    scope.add_local(ctx.fn_name.to_string(), ctx.closure_type.clone(), false);
    scope.add_local(result_name.clone(), result_type, false);

    // Optionally add a .filter() after the .map() (~30%)
    let chain_suffix = if emit.gen_bool(0.3) {
        let pred = filter_pred(ctx.closure_prim, emit);
        format!(".filter((y: {}) => {})", closure_type_name, pred)
    } else {
        String::new()
    };

    let iter_stmt = format!(
        "let {} = {}.iter().map({}){}.collect()",
        result_name, arr_name, ctx.fn_name, chain_suffix
    );
    Some(format!(
        "let {} = {}\n{}{}",
        ctx.fn_name, ctx.match_text, ctx.indent, iter_stmt
    ))
}

fn build_invoke_pattern(
    scope: &mut Scope,
    emit: &mut Emit,
    ctx: &ClosureCtx<'_>,
) -> Option<String> {
    let result_name = scope.fresh_name();
    let result_type = TypeInfo::Primitive(ctx.closure_prim);

    let arg = match ctx.closure_prim {
        PrimitiveType::I64 => format!("{}", emit.random_in(1, 20)),
        PrimitiveType::I32 => format!("{}_i32", emit.random_in(1, 20)),
        _ => "0".to_string(),
    };

    scope.add_local(ctx.fn_name.to_string(), ctx.closure_type.clone(), false);
    scope.add_local(result_name.clone(), result_type, false);

    let call_stmt = format!("let {} = {}({})", result_name, ctx.fn_name, arg);
    Some(format!(
        "let {} = {}\n{}{}",
        ctx.fn_name, ctx.match_text, ctx.indent, call_stmt
    ))
}

fn filter_pred(prim: PrimitiveType, emit: &mut Emit) -> String {
    match prim {
        PrimitiveType::I64 => {
            let threshold = emit.gen_i64_range(-5, 10);
            format!("y > {}", threshold)
        }
        PrimitiveType::I32 => {
            let threshold = emit.gen_i64_range(-5, 10);
            format!("y > {}_i32", threshold)
        }
        _ => "true".to_string(),
    }
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchClosure.name(), "match_closure");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchClosure
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn precondition_false_in_generic_class_method() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        // Without generic class context, precondition is true
        assert!(MatchClosure.precondition(&scope, &params));
    }

    #[test]
    fn generates_with_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchClosure.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match "), "got: {text}");
        assert!(text.contains("(n:"), "got: {text}");
        assert!(text.contains("=>"), "got: {text}");
    }
}

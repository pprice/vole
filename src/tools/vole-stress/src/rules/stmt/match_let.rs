//! Rule: match expression let-binding on integer variables.
//!
//! Finds an i64/i32-typed variable in scope and generates:
//! ```vole
//! let result = match var {
//!     1 => <expr>
//!     2 => <expr>
//!     _ => <expr>
//! }
//! ```
//! Supports complex scrutinees (arithmetic expressions), iterator chains
//! as scrutinees, unreachable wildcards, and match guards.

use std::collections::HashSet;

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchLet;

impl StmtRule for MatchLet {
    fn name(&self) -> &'static str {
        "match_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![
            Param::prob("probability", 0.08),
            Param::prob("unreachable_probability", 0.05),
            Param::prob("match_guard_probability", 0.15),
        ]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, params: &Params) -> Option<String> {
        let candidates = collect_integer_candidates(scope);
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (var_name, scrutinee_prim) = candidates[idx].clone();
        let is_i32 = matches!(scrutinee_prim, PrimitiveType::I32);
        let suffix = if is_i32 { "_i32" } else { "" };

        // ~15% chance to use an iterator chain as the scrutinee (feature interaction)
        let i64_arrays = collect_i64_arrays(scope);
        let scrutinee = build_scrutinee(emit, &var_name, suffix, is_i32, &i64_arrays);

        let unreachable_prob = params.prob("unreachable_probability");
        let guard_prob = params.prob("match_guard_probability");

        let has_complex_scrutinee = scrutinee.starts_with('(');
        let use_unreachable = !has_complex_scrutinee && emit.gen_bool(unreachable_prob);

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let arm_count = emit.random_in(2, 3);
        let indent = emit.indent_str();

        let ctx = MatchLetCtx {
            result_name: &result_name,
            result_type: &result_type,
            suffix,
            arm_count,
            indent: &indent,
        };

        if use_unreachable {
            generate_unreachable_match(scope, emit, &ctx)
        } else {
            generate_normal_match(scope, emit, &ctx, &scrutinee, guard_prob)
        }
    }
}

fn collect_integer_candidates(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    let mut candidates = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) = ty {
            candidates.push((name.clone(), *p));
        }
    }
    for param in scope.params {
        if let TypeInfo::Primitive(p @ (PrimitiveType::I64 | PrimitiveType::I32)) =
            &param.param_type
        {
            candidates.push((param.name.clone(), *p));
        }
    }
    candidates
}

fn collect_i64_arrays(scope: &Scope) -> Vec<String> {
    scope
        .locals
        .iter()
        .filter_map(|(name, ty, _)| match ty {
            TypeInfo::Array(inner)
                if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect()
}

fn build_scrutinee(
    emit: &mut Emit,
    var_name: &str,
    suffix: &str,
    is_i32: bool,
    i64_arrays: &[String],
) -> String {
    if !is_i32 && !i64_arrays.is_empty() && emit.gen_bool(0.15) {
        let arr_idx = emit.gen_range(0..i64_arrays.len());
        let arr = &i64_arrays[arr_idx];
        match emit.gen_range(0..3) {
            0 => format!("{}.iter().count()", arr),
            1 => format!("{}.iter().filter((x) => x > 0).count()", arr),
            _ => format!("{}.iter().sum()", arr),
        }
    } else if emit.gen_bool(0.30) {
        let ops = ["+", "-", "*", "%"];
        let op = ops[emit.gen_range(0..ops.len())];
        let lit = emit.random_in(1, 9);
        format!("({} {} {}{})", var_name, op, lit, suffix)
    } else {
        var_name.to_string()
    }
}

/// Shared context for unreachable/normal match builders.
struct MatchLetCtx<'a> {
    result_name: &'a str,
    result_type: &'a TypeInfo,
    suffix: &'a str,
    arm_count: usize,
    indent: &'a str,
}

fn generate_unreachable_match(
    scope: &mut Scope,
    emit: &mut Emit,
    ctx: &MatchLetCtx<'_>,
) -> Option<String> {
    let known_val = emit.gen_i64_range(-10, 19);
    let mut arms = Vec::new();

    let arm_expr = emit.literal(ctx.result_type);
    arms.push(format!(
        "{}    {}{} => {}",
        ctx.indent, known_val, ctx.suffix, arm_expr
    ));

    let mut used_values = HashSet::new();
    used_values.insert(known_val);
    for _ in 1..ctx.arm_count {
        let mut val = emit.gen_i64_range(-10, 19);
        while used_values.contains(&val) {
            val = emit.gen_i64_range(-10, 19);
        }
        used_values.insert(val);
        let arm_expr = emit.literal(ctx.result_type);
        arms.push(format!(
            "{}    {}{} => {}",
            ctx.indent, val, ctx.suffix, arm_expr
        ));
    }

    arms.push(format!("{}    _ => unreachable", ctx.indent));

    scope.add_local(ctx.result_name.to_string(), ctx.result_type.clone(), false);

    Some(format!(
        "let {} = match {}{} {{\n{}\n{}}}",
        ctx.result_name,
        known_val,
        ctx.suffix,
        arms.join("\n"),
        ctx.indent,
    ))
}

fn generate_normal_match(
    scope: &mut Scope,
    emit: &mut Emit,
    ctx: &MatchLetCtx<'_>,
    scrutinee: &str,
    guard_prob: f64,
) -> Option<String> {
    let mut arms = Vec::new();
    let mut used_values = HashSet::new();
    for _ in 0..ctx.arm_count {
        let mut val = emit.gen_i64_range(-10, 19);
        while used_values.contains(&val) {
            val = emit.gen_i64_range(-10, 19);
        }
        used_values.insert(val);
        let arm_expr = emit.literal(ctx.result_type);
        arms.push(format!(
            "{}    {}{} => {}",
            ctx.indent, val, ctx.suffix, arm_expr
        ));
    }

    // Sometimes generate a guarded wildcard arm before the bare wildcard
    if emit.gen_bool(guard_prob) {
        let guard_expr = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let guarded_val = emit.literal(ctx.result_type);
        arms.push(format!(
            "{}    _ if {} => {}",
            ctx.indent, guard_expr, guarded_val
        ));
    }

    let wildcard_expr = emit.literal(ctx.result_type);
    arms.push(format!("{}    _ => {}", ctx.indent, wildcard_expr));

    scope.add_local(ctx.result_name.to_string(), ctx.result_type.clone(), false);

    Some(format!(
        "let {} = match {} {{\n{}\n{}}}",
        ctx.result_name,
        scrutinee,
        arms.join("\n"),
        ctx.indent,
    ))
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

    fn test_params() -> Params {
        Params::from_iter([
            ("probability", ParamValue::Probability(1.0)),
            ("unreachable_probability", ParamValue::Probability(0.05)),
            ("match_guard_probability", ParamValue::Probability(0.15)),
        ])
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(MatchLet.name(), "match_let");
    }

    #[test]
    fn returns_none_without_integer_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        assert!(
            MatchLet
                .generate(&mut scope, &mut emit, &test_params())
                .is_none()
        );
    }

    #[test]
    fn generates_with_i64_variable() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        let result = MatchLet.generate(&mut scope, &mut emit, &test_params());
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match "), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }

    #[test]
    fn adds_one_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I32), false);
        let initial_len = scope.locals.len();

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);

        MatchLet.generate(&mut scope, &mut emit, &test_params());
        assert_eq!(scope.locals.len(), initial_len + 1);
    }
}

//! Rule: sentinel union let-binding.
//!
//! Creates a union type combining a primitive with sentinel type(s),
//! assigns a value, then follows up with a match or `is`-check.
//!
//! Pattern 1 (match):
//! ```vole
//! let x: i64 | Sent1 = Sent1
//! let result = match x {
//!     i64 => "value"
//!     Sent1 => "sentinel"
//! }
//! ```
//!
//! Pattern 2 (is-check via when):
//! ```vole
//! let x: i64 | Sent1 = 42
//! let result = when { x is Sent1 => "sentinel", _ => "value" }
//! ```
//!
//! 30% chance of multi-sentinel union when 2+ sentinels available.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct SentinelUnionLet;

impl StmtRule for SentinelUnionLet {
    fn name(&self) -> &'static str {
        "sentinel_union_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.module_id.is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let module_id = scope.module_id?;
        let module = scope.table.get_module(module_id)?;

        let sentinels: Vec<_> = module.sentinels().collect();
        if sentinels.is_empty() {
            return None;
        }

        // Pick sentinel(s)
        let use_multi = sentinels.len() >= 2 && emit.gen_bool(0.3);

        let sentinel_idx = emit.gen_range(0..sentinels.len());
        let sentinel_name = sentinels[sentinel_idx].name.clone();
        let sentinel_sym_id = sentinels[sentinel_idx].id;

        let second_sentinel = if use_multi {
            let mut idx2 = emit.gen_range(0..sentinels.len());
            while idx2 == sentinel_idx {
                idx2 = emit.gen_range(0..sentinels.len());
            }
            Some((sentinels[idx2].name.clone(), sentinels[idx2].id))
        } else {
            None
        };

        // Pick a primitive type for the other union variant
        let prim_type = emit.random_expr_primitive();
        let prim_type_info = TypeInfo::Primitive(prim_type);

        // Build the union type
        let sentinel_type_info = TypeInfo::Sentinel(module_id, sentinel_sym_id);
        let mut union_members = vec![prim_type_info.clone(), sentinel_type_info];
        let mut union_type_parts = vec![prim_type.as_str().to_string(), sentinel_name.clone()];

        if let Some((ref name2, sym_id2)) = second_sentinel {
            union_members.push(TypeInfo::Sentinel(module_id, sym_id2));
            union_type_parts.push(name2.clone());
        }
        let union_type = TypeInfo::Union(union_members);
        let union_type_syntax = union_type_parts.join(" | ");

        let union_var_name = scope.fresh_name();

        // Randomly choose initial value
        let init_choices = if second_sentinel.is_some() { 3 } else { 2 };
        let init_choice = emit.gen_range(0..init_choices);

        let init_value = match init_choice {
            0 => emit.literal(&prim_type_info),
            1 => sentinel_name.clone(),
            _ => second_sentinel.as_ref().unwrap().0.clone(),
        };

        let let_stmt = format!(
            "let {}: {} = {}",
            union_var_name, union_type_syntax, init_value
        );

        scope.add_local(union_var_name.clone(), union_type, false);

        // Choose follow-up: match (60%) or is-check (40%)
        if emit.gen_bool(0.6) {
            let follow_up = gen_match_follow_up(
                scope,
                emit,
                &union_var_name,
                prim_type,
                &sentinel_name,
                &second_sentinel,
            );
            Some(format!("{}\n{}", let_stmt, follow_up))
        } else {
            let follow_up = gen_is_check_follow_up(scope, emit, &union_var_name, &sentinel_name);
            Some(format!("{}\n{}", let_stmt, follow_up))
        }
    }
}

/// Generate a match expression follow-up on the union variable.
fn gen_match_follow_up(
    scope: &mut Scope,
    emit: &mut Emit,
    union_var_name: &str,
    prim_type: PrimitiveType,
    sentinel_name: &str,
    second_sentinel: &Option<(String, crate::symbols::SymbolId)>,
) -> String {
    let result_type = emit.random_primitive_type();
    let result_name = scope.fresh_name();

    let indent = emit.indented(|e| e.indent_str());
    let close_indent = emit.indent_str();

    let prim_arm_expr = emit.literal(&result_type);
    let sentinel_arm_expr = emit.literal(&result_type);

    let mut match_arms = format!(
        "{}{} => {}\n{}{} => {}",
        indent,
        prim_type.as_str(),
        prim_arm_expr,
        indent,
        sentinel_name,
        sentinel_arm_expr,
    );

    if let Some((name2, _)) = second_sentinel {
        let sent2_arm_expr = emit.literal(&result_type);
        match_arms.push_str(&format!("\n{}{} => {}", indent, name2, sent2_arm_expr));
    }

    let match_stmt = format!(
        "let {} = match {} {{\n{}\n{}}}",
        result_name, union_var_name, match_arms, close_indent,
    );

    scope.add_local(result_name, result_type, false);
    match_stmt
}

/// Generate a when-based is-check follow-up.
fn gen_is_check_follow_up(
    scope: &mut Scope,
    emit: &mut Emit,
    union_var_name: &str,
    sentinel_name: &str,
) -> String {
    let result_type = emit.random_primitive_type();
    let result_name = scope.fresh_name();

    let sentinel_branch_expr = emit.literal(&result_type);
    let else_branch_expr = emit.literal(&result_type);

    let indent = emit.indented(|e| e.indent_str());
    let close_indent = emit.indent_str();

    let is_stmt = format!(
        "let {} = when {{\n{}{} is {} => {}\n{}_ => {}\n{}}}",
        result_name,
        indent,
        union_var_name,
        sentinel_name,
        sentinel_branch_expr,
        indent,
        else_branch_expr,
        close_indent,
    );

    scope.add_local(result_name, result_type, false);
    is_stmt
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
        assert_eq!(SentinelUnionLet.name(), "sentinel_union_let");
    }

    #[test]
    fn returns_none_without_sentinels() {
        let mut table = SymbolTable::new();
        let _mod_id = table.add_module("test".to_string(), "test.vole".to_string());
        let mut scope = Scope::new(&[], &table);
        scope.module_id = Some(crate::symbols::ModuleId(0));

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = SentinelUnionLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}

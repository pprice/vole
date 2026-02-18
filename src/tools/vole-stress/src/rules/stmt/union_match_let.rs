//! Rule: match on a union-typed variable with type-pattern arms.
//!
//! Finds a union-typed variable (all-primitive variants) in scope and
//! generates either a `match` with type-pattern arms or a `when { x is T }`
//! check:
//!
//! ```vole
//! let result = match unionVar {
//!     i32 => <expr>
//!     string => <expr>
//!     bool => <expr>
//! }
//! ```
//!
//! ~35% chance of an `is`-check variant instead of a full match.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct UnionMatchLet;

impl StmtRule for UnionMatchLet {
    fn name(&self) -> &'static str {
        "union_match_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| is_all_primitive_union(&v.type_info))
            .first()
            .is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = scope.vars_matching(|v| is_all_primitive_union(&v.type_info));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let scrutinee = candidates[idx].name.clone();
        let variants = match &candidates[idx].type_info {
            TypeInfo::Union(v) => v.clone(),
            _ => return None,
        };

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let indent = emit.indented(|e| e.indent_str());
        let close_indent = emit.indent_str();

        // ~35% chance: generate `when { x is Type => ... }` instead of match
        if emit.gen_bool(0.35) {
            return gen_is_check(
                scope,
                emit,
                &result_name,
                &scrutinee,
                &variants,
                &result_type,
                &indent,
                &close_indent,
            );
        }

        let mut arms = Vec::new();
        for variant in &variants {
            if let TypeInfo::Primitive(prim) = variant {
                let arm_expr = emit.literal(&result_type);
                arms.push(format!("{}{} => {}", indent, prim.as_str(), arm_expr));
            }
        }

        if arms.is_empty() {
            return None;
        }

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}\n{}}}",
            result_name,
            scrutinee,
            arms.join("\n"),
            close_indent,
        ))
    }
}

/// Generate a `when { x is T => ... _ => ... }` variant.
fn gen_is_check(
    scope: &mut Scope,
    emit: &mut Emit,
    result_name: &str,
    scrutinee: &str,
    variants: &[TypeInfo],
    result_type: &TypeInfo,
    indent: &str,
    close_indent: &str,
) -> Option<String> {
    let prim_variants: Vec<PrimitiveType> = variants
        .iter()
        .filter_map(|v| {
            if let TypeInfo::Primitive(p) = v {
                Some(*p)
            } else {
                None
            }
        })
        .collect();
    if prim_variants.is_empty() {
        return None;
    }

    let check_type = prim_variants[emit.gen_range(0..prim_variants.len())];
    let is_branch_expr = emit.literal(result_type);
    let else_branch_expr = emit.literal(result_type);

    scope.add_local(result_name.to_string(), result_type.clone(), false);

    Some(format!(
        "let {} = when {{\n{}{} is {} => {}\n{}_ => {}\n{}}}",
        result_name,
        indent,
        scrutinee,
        check_type.as_str(),
        is_branch_expr,
        indent,
        else_branch_expr,
        close_indent,
    ))
}

fn is_all_primitive_union(ty: &TypeInfo) -> bool {
    matches!(ty, TypeInfo::Union(variants) if variants.iter().all(|v| matches!(v, TypeInfo::Primitive(_))))
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
        assert_eq!(UnionMatchLet.name(), "union_match_let");
    }

    #[test]
    fn returns_none_without_union_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = UnionMatchLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_match_with_union_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "u".into(),
            TypeInfo::Union(vec![
                TypeInfo::Primitive(PrimitiveType::I64),
                TypeInfo::Primitive(PrimitiveType::String),
            ]),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = UnionMatchLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        // Should contain either "match" or "when" (is-check variant)
        assert!(
            text.contains("match") || text.contains("when"),
            "got: {text}"
        );
        assert!(text.contains("=>"), "got: {text}");
    }
}

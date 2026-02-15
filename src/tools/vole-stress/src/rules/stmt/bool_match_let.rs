//! Rule: match on boolean value.
//!
//! Finds a bool-typed variable or computes a bool expression (iterator
//! predicate, string method) and generates a match with true/wildcard arms.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct BoolMatchLet;

impl StmtRule for BoolMatchLet {
    fn name(&self) -> &'static str {
        "bool_match_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let bool_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::Bool)))
            .map(|(name, _, _)| name.clone())
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::Bool)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // Collect array params for computed bool scrutinee
        let array_params: Vec<(String, TypeInfo)> = scope
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| (p.name.clone(), p.param_type.clone()))
            .collect();

        // Collect string candidates
        let string_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::String)))
            .map(|(name, _, _)| name.clone())
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::String)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        // ~35% chance: use a computed bool expression as scrutinee
        let scrutinee = if emit.gen_bool(0.35) {
            if let Some(expr) = computed_bool_scrutinee(emit, &array_params, &string_vars) {
                expr
            } else if !bool_vars.is_empty() {
                bool_vars[emit.gen_range(0..bool_vars.len())].clone()
            } else {
                return None;
            }
        } else if !bool_vars.is_empty() {
            bool_vars[emit.gen_range(0..bool_vars.len())].clone()
        } else {
            return None;
        };

        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let true_val = emit.literal(&result_type);
        let false_val = emit.literal(&result_type);

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = match {} {{\n{}true => {}\n{}_ => {}\n{}}}",
            result_name, scrutinee, inner_indent, true_val, inner_indent, false_val, indent,
        ))
    }
}

/// Generate a computed bool expression for use as a match scrutinee.
fn computed_bool_scrutinee(
    emit: &mut Emit,
    array_params: &[(String, TypeInfo)],
    string_vars: &[String],
) -> Option<String> {
    let mut options: Vec<String> = Vec::new();

    for (name, elem_ty) in array_params {
        if let TypeInfo::Array(inner) = elem_ty {
            if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I64)) {
                options.push(format!("{}.iter().any((x) => x > 0)", name));
                options.push(format!("{}.iter().all((x) => x == x)", name));
            } else if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::I32)) {
                options.push(format!("{}.iter().any((x) => x > 0_i32)", name));
                options.push(format!("{}.iter().all((x) => x == x)", name));
            } else if matches!(inner.as_ref(), TypeInfo::Primitive(PrimitiveType::Bool)) {
                options.push(format!("{}.iter().any((x) => x)", name));
            }
        }
    }

    for name in string_vars {
        options.push(format!("{}.contains(\"a\")", name));
        options.push(format!("{}.starts_with(\"\")", name));
        options.push(format!("{}.length() > 0", name));
    }

    if options.is_empty() {
        return None;
    }

    let idx = emit.gen_range(0..options.len());
    Some(options.swap_remove(idx))
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(BoolMatchLet.name(), "bool_match_let");
    }

    #[test]
    fn generates_bool_match() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "flag".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::Bool),
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = BoolMatchLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
        assert!(text.contains("true =>"), "got: {text}");
    }

    #[test]
    fn returns_none_without_bools() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            BoolMatchLet
                .generate(&mut scope, &mut emit, &rule_params)
                .is_none()
        );
    }
}

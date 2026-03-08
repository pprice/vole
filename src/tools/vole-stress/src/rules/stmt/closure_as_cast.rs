//! Rule: closure that captures a union-typed variable and performs `as?` cast.
//!
//! Finds a union-typed variable (all-primitive variants) in scope and generates
//! a closure that captures it and performs a safe cast inside the body.  This
//! exercises the intersection of closure captures + union type dispatch.
//!
//! **Variant 0 -- closure with as? cast (~50%)**:
//! ```vole
//! let get_intN = () => unionVar as? targetType
//! let resultN = get_intN()
//! assert(resultN != nil || resultN == nil)
//! ```
//! Result is optional -- do NOT add to scope.
//!
//! **Variant 1 -- closure with as? + null coalesce (~50%)**:
//! ```vole
//! let get_or_defaultN = () => (unionVar as? targetType) ?? defaultValue
//! let resultN = get_or_defaultN()
//! assert(resultN != nil || resultN == nil)
//! ```
//! Result is a concrete primitive -- add to scope.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ClosureAsCast;

impl StmtRule for ClosureAsCast {
    fn name(&self) -> &'static str {
        "closure_as_cast"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        !scope
            .vars_matching(|v| is_all_primitive_union(&v.type_info))
            .is_empty()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let candidates = scope.vars_matching(|v| is_all_primitive_union(&v.type_info));
        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let var_name = candidates[idx].name.clone();
        let variants = match &candidates[idx].type_info {
            TypeInfo::Union(v) => v.clone(),
            _ => return None,
        };

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

        let target = prim_variants[emit.gen_range(0..prim_variants.len())];

        // 50/50 split: variant 0 = plain as?, variant 1 = as? + null coalesce
        if emit.gen_bool(0.5) {
            emit_plain_as_cast(scope, emit, &var_name, target)
        } else {
            emit_coalesce_as_cast(scope, emit, &var_name, target)
        }
    }
}

/// Variant 0: closure with plain `as?` cast.  Result is optional -- not added
/// to scope.
fn emit_plain_as_cast(
    scope: &mut Scope,
    emit: &mut Emit,
    var_name: &str,
    target: PrimitiveType,
) -> Option<String> {
    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    // Do NOT add result to scope (optional type).
    let mut lines = Vec::new();
    lines.push(format!(
        "let {} = () => {} as? {}",
        closure_name,
        var_name,
        target.as_str(),
    ));
    lines.push(format!("let {} = {}()", result_name, closure_name));
    lines.push(format!(
        "assert({} != nil || {} == nil)",
        result_name, result_name,
    ));

    Some(lines.join("\n"))
}

/// Variant 1: closure with `as?` + null coalesce.  Result is a concrete
/// primitive -- added to scope.
fn emit_coalesce_as_cast(
    scope: &mut Scope,
    emit: &mut Emit,
    var_name: &str,
    target: PrimitiveType,
) -> Option<String> {
    let target_type = TypeInfo::Primitive(target);
    let default_val = emit.literal(&target_type);

    let closure_name = scope.fresh_name();
    let result_name = scope.fresh_name();

    scope.add_local(result_name.clone(), target_type, false);

    let mut lines = Vec::new();
    lines.push(format!(
        "let {} = () => ({} as? {}) ?? {}",
        closure_name,
        var_name,
        target.as_str(),
        default_val,
    ));
    lines.push(format!("let {} = {}()", result_name, closure_name));
    lines.push(format!(
        "assert({} != nil || {} == nil)",
        result_name, result_name,
    ));

    Some(lines.join("\n"))
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
        assert_eq!(ClosureAsCast.name(), "closure_as_cast");
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

        let result = ClosureAsCast.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_with_union_var() {
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

        let mut found_plain = false;
        let mut found_coalesce = false;

        for seed in 0..50 {
            let table2 = SymbolTable::new();
            let mut scope2 = Scope::new(&[], &table2);
            scope2.add_local(
                "u".into(),
                TypeInfo::Union(vec![
                    TypeInfo::Primitive(PrimitiveType::I64),
                    TypeInfo::Primitive(PrimitiveType::String),
                ]),
                false,
            );

            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let result = ClosureAsCast.generate(&mut scope2, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {seed} returned None");
            let text = result.unwrap();

            // All variants should have as? and assert
            assert!(text.contains("as?"), "seed {seed}: missing as? in: {text}");
            assert!(
                text.contains("assert("),
                "seed {seed}: missing assert in: {text}"
            );
            // All variants should define a closure and call it
            assert!(
                text.contains("() =>"),
                "seed {seed}: missing closure in: {text}"
            );

            if text.contains("??") {
                found_coalesce = true;
            } else {
                found_plain = true;
            }
        }

        assert!(found_plain, "no plain as? variant seen in 50 seeds");
        assert!(found_coalesce, "no coalesce variant seen in 50 seeds");
    }
}

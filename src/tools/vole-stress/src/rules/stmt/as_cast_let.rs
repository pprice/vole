//! Rule: generate `as?` (safe cast) and `as!` (unsafe cast) on union-typed
//! variables.
//!
//! Finds a union-typed variable whose variants are all primitives and emits
//! one of three patterns:
//!
//! **Variant 0 — safe cast (~40%)**:
//! ```vole
//! let result = unionVar as? i64
//! ```
//! Result is `Optional<TargetType>` — not added to scope.
//!
//! **Variant 1 — safe cast with null coalesce (~30%)**:
//! ```vole
//! let result = (unionVar as? i64) ?? defaultValue
//! ```
//! Result is the target primitive type, added to scope.
//!
//! **Variant 2 — unsafe cast (~30%)**:
//! ```vole
//! let result: targetType = unionVar as! targetType
//! ```
//! Always uses the first variant of the union (the value the variable was
//! initialised with) so the cast cannot panic at runtime.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct AsCastLet;

impl StmtRule for AsCastLet {
    fn name(&self) -> &'static str {
        "as_cast_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
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

        let result_name = scope.fresh_name();

        // Pick variant: 0 = safe cast (40%), 1 = safe + coalesce (30%), 2 = unsafe (30%)
        let roll: f64 = emit.gen_range(0..100usize) as f64 / 100.0;

        if roll < 0.40 {
            // Variant 0: safe cast — result is Optional, do NOT add to scope.
            let target = prim_variants[emit.gen_range(0..prim_variants.len())];
            Some(format!(
                "let {} = {} as? {}",
                result_name,
                var_name,
                target.as_str()
            ))
        } else if roll < 0.70 {
            // Variant 1: safe cast with null coalesce — result is the target type.
            let target = prim_variants[emit.gen_range(0..prim_variants.len())];
            let target_type = TypeInfo::Primitive(target);
            let default_val = emit.literal(&target_type);
            scope.add_local(result_name.clone(), target_type, false);
            Some(format!(
                "let {} = ({} as? {}) ?? {}",
                result_name,
                var_name,
                target.as_str(),
                default_val,
            ))
        } else {
            // Variant 2: unsafe cast — MUST use first variant for safety.
            let target = prim_variants[0];
            let target_type = TypeInfo::Primitive(target);
            scope.add_local(result_name.clone(), target_type, false);
            Some(format!(
                "let {}: {} = {} as! {}",
                result_name,
                target.as_str(),
                var_name,
                target.as_str(),
            ))
        }
    }
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
        assert_eq!(AsCastLet.name(), "as_cast_let");
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

        let result = AsCastLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_cast_with_union_var() {
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

        // Try multiple seeds to cover different variant paths.
        let mut found_safe = false;
        let mut found_coalesce = false;
        let mut found_unsafe = false;

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

            let result = AsCastLet.generate(&mut scope2, &mut emit, &rule_params);
            assert!(result.is_some(), "seed {seed} returned None");
            let text = result.unwrap();

            if text.contains("as!") {
                found_unsafe = true;
                assert!(text.contains("let "), "seed {seed}: {text}");
                // Unsafe cast must target the first variant (i64)
                assert!(
                    text.contains("as! i64"),
                    "seed {seed}: unsafe cast should target first variant, got: {text}"
                );
            } else if text.contains("??") {
                found_coalesce = true;
                assert!(text.contains("as?"), "seed {seed}: {text}");
            } else {
                found_safe = true;
                assert!(text.contains("as?"), "seed {seed}: {text}");
            }
        }

        assert!(found_safe, "no safe cast variant seen in 50 seeds");
        assert!(found_coalesce, "no coalesce variant seen in 50 seeds");
        assert!(found_unsafe, "no unsafe cast variant seen in 50 seeds");
    }
}

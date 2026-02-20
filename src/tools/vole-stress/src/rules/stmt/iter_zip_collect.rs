//! Rule: `.iter().zip(other.iter()).collect()` chains on arrays.
//!
//! Produces `[(T1, T2)]` from `[T1]` and `[T2]`.  Optionally chains `.map()`
//! on the zip when both element types are `i64`, summing the paired values.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IterZipCollect;

impl StmtRule for IterZipCollect {
    fn name(&self) -> &'static str {
        "iter_zip_collect"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let arrays: Vec<(String, TypeInfo)> = scope
            .array_vars()
            .into_iter()
            .filter(|(_, elem_ty)| {
                matches!(
                    elem_ty,
                    TypeInfo::Primitive(
                        PrimitiveType::I64
                            | PrimitiveType::I32
                            | PrimitiveType::String
                            | PrimitiveType::F64
                            | PrimitiveType::Bool
                    )
                )
            })
            .collect();

        if arrays.len() < 2 {
            return None;
        }

        let idx1 = emit.gen_range(0..arrays.len());
        let mut idx2 = emit.gen_range(0..arrays.len());
        if idx2 == idx1 {
            idx2 = (idx1 + 1) % arrays.len();
        }

        let (arr1_name, elem1_ty) = &arrays[idx1];
        let (arr2_name, elem2_ty) = &arrays[idx2];
        let name = scope.fresh_name();

        let both_i64 = matches!(elem1_ty, TypeInfo::Primitive(PrimitiveType::I64))
            && matches!(elem2_ty, TypeInfo::Primitive(PrimitiveType::I64));
        let use_map = both_i64 && emit.gen_bool(0.4);

        if use_map {
            // .iter().zip(other.iter()).map((p) => p[0] + p[1]).collect() -> [i64]
            let result_type = TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64)));
            scope.add_local(name.clone(), result_type, false);
            Some(format!(
                "let {} = {}.iter().zip({}.iter()).map((p) => p[0] + p[1]).collect()",
                name, arr1_name, arr2_name
            ))
        } else {
            // .iter().zip(other.iter()).collect() -> [(T1, T2)]
            let tuple_type = TypeInfo::Tuple(vec![elem1_ty.clone(), elem2_ty.clone()]);
            let result_type = TypeInfo::Array(Box::new(tuple_type));
            scope.add_local(name.clone(), result_type, false);
            Some(format!(
                "let {} = {}.iter().zip({}.iter()).collect()",
                name, arr1_name, arr2_name
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolver::ResolvedParams;
    use crate::rule::{ExprRule, ParamValue};
    use crate::symbols::{ParamInfo, PrimitiveType, SymbolTable};
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
        assert_eq!(IterZipCollect.name(), "iter_zip_collect");
    }

    #[test]
    fn generates_zip_collect() {
        let table = SymbolTable::new();
        let params = &[
            ParamInfo {
                name: "arr1".to_string(),
                param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                has_default: false,
            },
            ParamInfo {
                name: "arr2".to_string(),
                param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::String))),
                has_default: false,
            },
        ];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterZipCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(
            text.contains(".iter().zip(") && text.contains(".collect()"),
            "got: {text}"
        );
    }

    #[test]
    fn generates_zip_with_both_i64() {
        let table = SymbolTable::new();
        let params = &[
            ParamInfo {
                name: "xs".to_string(),
                param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                has_default: false,
            },
            ParamInfo {
                name: "ys".to_string(),
                param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
                has_default: false,
            },
        ];
        let mut scope = Scope::new(params, &table);

        // Run several seeds to get both variants (plain zip and map variant)
        let mut saw_plain = false;
        let mut saw_map = false;
        for seed in 0..100 {
            let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
            let resolved = ResolvedParams::new();
            let mut emit = test_emit(&mut rng, &resolved);
            let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

            let mut scope_copy = Scope::new(params, &table);
            if let Some(text) = IterZipCollect.generate(&mut scope_copy, &mut emit, &rule_params) {
                if text.contains(".map(") {
                    saw_map = true;
                } else {
                    saw_plain = true;
                }
            }
            if saw_plain && saw_map {
                break;
            }
        }
        assert!(saw_plain, "should produce plain zip+collect for i64 arrays");
        assert!(saw_map, "should produce map variant for i64 arrays");
    }

    #[test]
    fn returns_none_with_fewer_than_two_arrays() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "arr".to_string(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterZipCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn returns_none_without_arrays() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IterZipCollect.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}

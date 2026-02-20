//! Rule: type widening conversion.
//!
//! Generates `let wide: i64 = narrow_var` where narrow_var is a narrower type.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WideningLet;

impl StmtRule for WideningLet {
    fn name(&self) -> &'static str {
        "widening_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.10)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut candidates: Vec<(String, PrimitiveType, PrimitiveType)> = Vec::new();

        // Collect from locals
        for var in scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(_))) {
            if let TypeInfo::Primitive(narrow) = &var.type_info {
                for wide in widening_targets(*narrow) {
                    candidates.push((var.name.clone(), *narrow, wide));
                }
            }
        }

        // Collect from params
        for param in scope.params {
            if let TypeInfo::Primitive(narrow) = &param.param_type {
                for wide in widening_targets(*narrow) {
                    candidates.push((param.name.clone(), *narrow, wide));
                }
            }
        }

        if candidates.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..candidates.len());
        let (source_name, _narrow, wide_type) = &candidates[idx];

        let name = scope.fresh_name();
        let wide_ty = TypeInfo::Primitive(*wide_type);
        scope.add_local(name.clone(), wide_ty, false);

        Some(format!(
            "let {}: {} = {}",
            name,
            wide_type.as_str(),
            source_name
        ))
    }
}

/// Returns types that the given narrow type can widen to.
fn widening_targets(narrow: PrimitiveType) -> Vec<PrimitiveType> {
    match narrow {
        PrimitiveType::I8 => vec![
            PrimitiveType::I16,
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I128,
        ],
        PrimitiveType::I16 => vec![PrimitiveType::I32, PrimitiveType::I64, PrimitiveType::I128],
        PrimitiveType::I32 => vec![PrimitiveType::I64, PrimitiveType::I128],
        PrimitiveType::I64 => vec![PrimitiveType::I128],
        PrimitiveType::U8 => vec![
            PrimitiveType::U16,
            PrimitiveType::U32,
            PrimitiveType::U64,
            PrimitiveType::I16,
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I128,
        ],
        PrimitiveType::U16 => vec![
            PrimitiveType::U32,
            PrimitiveType::U64,
            PrimitiveType::I32,
            PrimitiveType::I64,
            PrimitiveType::I128,
        ],
        PrimitiveType::U32 => vec![PrimitiveType::U64, PrimitiveType::I64, PrimitiveType::I128],
        PrimitiveType::U64 => vec![PrimitiveType::I128],
        PrimitiveType::F32 => vec![PrimitiveType::F64],
        _ => vec![],
    }
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
        assert_eq!(WideningLet.name(), "widening_let");
    }

    #[test]
    fn generates_widening_from_param() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "x".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I32),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WideningLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let "), "got: {text}");
        assert!(text.contains("= x"), "got: {text}");
    }

    #[test]
    fn returns_none_for_non_widenable() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "s".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::String),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WideningLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_none());
    }
}

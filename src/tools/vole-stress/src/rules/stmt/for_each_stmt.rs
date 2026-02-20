//! Rule: for_each iterator statement.
//!
//! Generates `arr.iter()[.filter(...)].for_each((x) => { let y = expr })`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ForEachStmt;

impl StmtRule for ForEachStmt {
    fn name(&self) -> &'static str {
        "for_each_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut array_vars: Vec<(String, PrimitiveType)> = Vec::new();

        for var in scope.vars_matching(|v| matches!(v.type_info, TypeInfo::Array(_))) {
            if let TypeInfo::Array(inner) = &var.type_info {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                    ) {
                        array_vars.push((var.name, *p));
                    }
                }
            }
        }

        for param in scope.params.iter() {
            if let TypeInfo::Array(inner) = &param.param_type {
                if let TypeInfo::Primitive(p) = inner.as_ref() {
                    if matches!(
                        p,
                        PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::String
                    ) {
                        array_vars.push((param.name.clone(), *p));
                    }
                }
            }
        }

        if array_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_vars.len());
        let (arr_name, elem_prim) = &array_vars[idx];

        // Optional filter prefix: ~30% for numeric
        let prefix = if emit.gen_bool(0.30)
            && matches!(elem_prim, PrimitiveType::I64 | PrimitiveType::I32)
        {
            let n = emit.gen_i64_range(-5, 2);
            format!(".filter((x) => x > {})", n)
        } else {
            String::new()
        };

        let body = match elem_prim {
            PrimitiveType::I64 | PrimitiveType::I32 => match emit.gen_range(0..3) {
                0 => "let y = x * 2".to_string(),
                1 => "let y = x + 1".to_string(),
                _ => "let y = x".to_string(),
            },
            _ => "let y = x".to_string(),
        };

        Some(format!(
            "{}.iter(){}.for_each((x) => {{ {} }})",
            arr_name, prefix, body
        ))
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
        assert_eq!(ForEachStmt.name(), "for_each_stmt");
    }

    #[test]
    fn generates_for_each() {
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

        let result = ForEachStmt.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".for_each("), "got: {text}");
    }
}

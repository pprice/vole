//! Rule: variable shadowing.
//!
//! Re-declares an existing primitive variable with a transformed value,
//! exercising the compiler's variable shadowing and scope resolution.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct VariableShadow;

impl StmtRule for VariableShadow {
    fn name(&self) -> &'static str {
        "variable_shadow"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.04)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_locals: Vec<(String, PrimitiveType)> = scope
            .locals
            .iter()
            .filter_map(|(name, ty, _)| {
                if let TypeInfo::Primitive(p) = ty {
                    Some((name.clone(), *p))
                } else {
                    None
                }
            })
            .collect();

        if prim_locals.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..prim_locals.len());
        let (var_name, prim) = &prim_locals[idx];

        let expr = match prim {
            PrimitiveType::I64 => {
                let n = emit.gen_i64_range(1, 10);
                let op = ["+", "-", "*"][emit.gen_range(0..3)];
                format!("{} {} {}", var_name, op, n)
            }
            PrimitiveType::I32 => {
                let n = emit.gen_i64_range(1, 5);
                format!("{} + {}_i32", var_name, n)
            }
            PrimitiveType::String => {
                format!("{} + \"!\"", var_name)
            }
            PrimitiveType::Bool => {
                format!("!{}", var_name)
            }
            _ => return None,
        };

        // Shadow: re-declare same name
        scope.add_local(var_name.clone(), TypeInfo::Primitive(*prim), false);
        Some(format!("let {} = {}", var_name, expr))
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
        assert_eq!(VariableShadow.name(), "variable_shadow");
    }

    #[test]
    fn returns_none_without_locals() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            VariableShadow
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_shadow() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = VariableShadow.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("let x = x"), "got: {text}");
    }
}

//! Rule: tautological assert statement.
//!
//! Generates `assert(cond)` where `cond` is a tautological expression
//! (always true at runtime): `x == x`, `true`, `s.length() >= 0`, etc.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct AssertStmt;

impl StmtRule for AssertStmt {
    fn name(&self) -> &'static str {
        "assert_stmt"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let prim_vars = collect_primitive_vars(scope);
        let string_vars = collect_string_vars(scope);
        let array_vars = collect_array_vars(scope);

        let condition = match emit.gen_range(0..7) {
            0 if !prim_vars.is_empty() => {
                let (name, _) = &prim_vars[emit.gen_range(0..prim_vars.len())];
                format!("{} == {}", name, name)
            }
            1 if !prim_vars.is_empty() => {
                let (name, ty) = &prim_vars[emit.gen_range(0..prim_vars.len())];
                match ty {
                    PrimitiveType::I64 => format!("{} >= 0 || {} < 0", name, name),
                    PrimitiveType::I32 => format!("{} >= 0_i32 || {} < 0_i32", name, name),
                    PrimitiveType::Bool => format!("{} || !{}", name, name),
                    PrimitiveType::String => format!("{}.length() >= 0", name),
                    _ => "true".to_string(),
                }
            }
            2 => "true".to_string(),
            3 if !array_vars.is_empty() => {
                let name = &array_vars[emit.gen_range(0..array_vars.len())];
                format!("{}.iter().count() >= 0", name)
            }
            4 if !string_vars.is_empty() => {
                let name = &string_vars[emit.gen_range(0..string_vars.len())];
                match emit.gen_range(0..3) {
                    0 => format!("{}.trim().length() >= 0", name),
                    1 => format!("{}.to_upper().length() == {}.length()", name, name),
                    _ => format!("{}.length() >= 0", name),
                }
            }
            _ => {
                if !prim_vars.is_empty() {
                    let (name, _) = &prim_vars[emit.gen_range(0..prim_vars.len())];
                    format!("{} == {}", name, name)
                } else {
                    "true".to_string()
                }
            }
        };

        Some(format!("assert({})", condition))
    }
}

fn collect_primitive_vars(scope: &Scope) -> Vec<(String, PrimitiveType)> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if let TypeInfo::Primitive(p) = ty {
            out.push((name.clone(), *p));
        }
    }
    for param in scope.params {
        if let TypeInfo::Primitive(p) = &param.param_type {
            out.push((param.name.clone(), *p));
        }
    }
    out
}

fn collect_string_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::String)) {
            out.push(param.name.clone());
        }
    }
    out
}

fn collect_array_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Array(_)) {
            out.push(param.name.clone());
        }
    }
    out
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
        assert_eq!(AssertStmt.name(), "assert_stmt");
    }

    #[test]
    fn generates_assert_without_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = AssertStmt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("assert("), "got: {text}");
    }

    #[test]
    fn generates_assert_with_i64_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = AssertStmt.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.starts_with("assert("), "got: {text}");
    }
}

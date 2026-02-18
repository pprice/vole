//! Rule: string interpolation with complex embedded expressions.
//!
//! Generates `"sum={a + b}"`, `"len={arr.length()}"`, etc.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct InterpolationExpr;

impl StmtRule for InterpolationExpr {
    fn name(&self) -> &'static str {
        "interpolation_expr"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars = collect_i64_vars(scope);
        let string_vars = collect_string_vars(scope);

        if i64_vars.is_empty() && string_vars.is_empty() {
            return None;
        }

        let name = scope.fresh_name();
        let mut parts: Vec<String> = Vec::new();

        let num_segments = emit.random_in(2, 3);
        for _ in 0..num_segments {
            let choice = emit.gen_range(0..5);
            match choice {
                0 if !i64_vars.is_empty() => {
                    let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
                    let n = emit.gen_i64_range(1, 10);
                    let op = ["+", "-", "*"][emit.gen_range(0..3)];
                    parts.push(format!("{{{} {} {}}}", var, op, n));
                }
                1 if !string_vars.is_empty() => {
                    let var = &string_vars[emit.gen_range(0..string_vars.len())];
                    let method = [".to_upper()", ".length()", ".trim()"][emit.gen_range(0..3)];
                    parts.push(format!("{{{}{}}}", var, method));
                }
                3 if !i64_vars.is_empty() => {
                    let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
                    parts.push(format!("{{{}}}", var));
                }
                _ if !string_vars.is_empty() => {
                    let var = &string_vars[emit.gen_range(0..string_vars.len())];
                    parts.push(format!("{{{}}}", var));
                }
                _ => {
                    parts.push("ok".to_string());
                }
            }
        }

        let labels = ["val", "result", "out", "x", "data"];
        let label = labels[emit.gen_range(0..labels.len())];
        let sep = [", ", " | ", " "][emit.gen_range(0..3)];

        let interp_str = format!("\"{}={}\"", label, parts.join(sep));

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, interp_str))
    }
}

fn collect_i64_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(param.param_type, TypeInfo::Primitive(PrimitiveType::I64)) {
            out.push(param.name.clone());
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
        assert_eq!(InterpolationExpr.name(), "interpolation_expr");
    }

    #[test]
    fn generates_interpolation() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = InterpolationExpr.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
    }
}

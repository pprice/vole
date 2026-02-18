//! Rule: when expression with string method conditions.
//!
//! Generates `when { str.contains("x") => N, str.length() > 5 => M, _ => D }`,
//! testing codegen for method calls in when arm conditions.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenStringMethodConds;

impl StmtRule for WhenStringMethodConds {
    fn name(&self) -> &'static str {
        "when_string_method_conds"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        let var = &string_vars[emit.gen_range(0..string_vars.len())];
        let name = scope.fresh_name();
        let indent = emit.indent_str();

        let num_arms = emit.random_in(2, 3);
        let mut arms = Vec::new();

        for i in 0..num_arms {
            let cond = generate_string_cond(var, i, emit);
            let val = emit.gen_i64_range(-20, 20);
            arms.push(format!("{}    {} => {}", indent, cond, val));
        }

        let default_val = emit.gen_i64_range(-20, 20);
        arms.push(format!("{}    _ => {}", indent, default_val));

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);

        Some(format!(
            "let {} = when {{\n{}\n{}}}",
            name,
            arms.join(",\n"),
            indent,
        ))
    }
}

fn generate_string_cond(var: &str, variant: usize, emit: &mut Emit) -> String {
    match variant % 4 {
        0 => {
            let subs = ["\"a\"", "\"e\"", "\"hello\"", "\"test\"", "\" \""];
            let sub = subs[emit.gen_range(0..subs.len())];
            format!("{}.contains({})", var, sub)
        }
        1 => {
            let thresh = emit.gen_i64_range(0, 15);
            format!("{}.length() > {}", var, thresh)
        }
        2 => format!("{}.length() == 0", var),
        _ => {
            let prefixes = ["\"a\"", "\"test\"", "\"h\""];
            let prefix = prefixes[emit.gen_range(0..prefixes.len())];
            format!("{}.starts_with({})", var, prefix)
        }
    }
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
        assert_eq!(WhenStringMethodConds.name(), "when_string_method_conds");
    }

    #[test]
    fn returns_none_without_string_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            WhenStringMethodConds
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_when_with_string_methods() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenStringMethodConds.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
    }
}

//! Rule: string interpolation let-binding.
//!
//! Collects variables suitable for interpolation (numeric, string, bool) and
//! generates a string with 1-3 interpolated segments:
//! ```vole
//! let s = "val: {x + 3}, data: {y.to_string()}"
//! ```
//!
//! Interpolation expressions may include simple references, arithmetic,
//! method calls, when expressions, or .to_string() chains.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringInterpolationLet;

impl StmtRule for StringInterpolationLet {
    fn name(&self) -> &'static str {
        "string_interpolation_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.05)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope
            .vars_matching(|v| is_interpolatable(&v.type_info))
            .first()
            .is_some()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let mut candidates = scope.vars_matching(|v| is_interpolatable(&v.type_info));
        if candidates.is_empty() {
            return None;
        }

        let num_segments = std::cmp::min(candidates.len(), emit.random_in(1, 3));

        // Shuffle candidates for variety
        let len = candidates.len();
        for i in (1..len).rev() {
            let j = emit.gen_range(0..i + 1);
            candidates.swap(i, j);
        }

        let prefixes = ["val: ", "result: ", "x=", "", "data: ", "v="];
        let separators = [", ", " | ", " + ", " and ", " / "];

        let mut parts: Vec<String> = Vec::new();
        for (i, var) in candidates.iter().enumerate().take(num_segments) {
            let prim = match &var.type_info {
                TypeInfo::Primitive(p) => *p,
                _ => continue,
            };
            let name = &var.name;
            let expr = gen_interpolation_expr(emit, name, prim);

            if i == 0 {
                let prefix = prefixes[emit.gen_range(0..prefixes.len())];
                parts.push(format!("{}{{{}}}", prefix, expr));
            } else {
                let sep = separators[emit.gen_range(0..separators.len())];
                parts.push(format!("{}{{{}}}", sep, expr));
            }
        }

        let interpolated_string = parts.join("");
        let result_name = scope.fresh_name();
        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        Some(format!("let {} = \"{}\"", result_name, interpolated_string))
    }
}

fn is_interpolatable(ty: &TypeInfo) -> bool {
    matches!(
        ty,
        TypeInfo::Primitive(
            PrimitiveType::I64
                | PrimitiveType::I32
                | PrimitiveType::F64
                | PrimitiveType::String
                | PrimitiveType::Bool,
        )
    )
}

fn gen_interpolation_expr(emit: &mut Emit, name: &str, prim: PrimitiveType) -> String {
    match emit.gen_range(0..6) {
        0 => name.to_string(),
        1 if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) => {
            let n = emit.random_in(1, 10);
            format!("{} + {}", name, n)
        }
        2 if matches!(prim, PrimitiveType::String) => {
            format!("{}.length()", name)
        }
        3 if matches!(prim, PrimitiveType::I64 | PrimitiveType::I32) => {
            let threshold = emit.random_in(0, 10);
            let suffix = if matches!(prim, PrimitiveType::I32) {
                "_i32"
            } else {
                ""
            };
            format!(
                "when {{ {} > {}{} => {} * 2{}, _ => 0{} }}",
                name, threshold, suffix, name, suffix, suffix
            )
        }
        4 if matches!(prim, PrimitiveType::Bool) => {
            format!("when {{ {} => 1, _ => 0 }}", name)
        }
        5 if matches!(
            prim,
            PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64
        ) =>
        {
            format!("{}.to_string()", name)
        }
        _ => name.to_string(),
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
        Emit::new(rng, EMPTY_STMT, EMPTY_EXPR, resolved)
    }

    #[test]
    fn name_is_correct() {
        assert_eq!(StringInterpolationLet.name(), "string_interpolation_let");
    }

    #[test]
    fn returns_none_without_suitable_vars() {
        let table = SymbolTable::new();
        let scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result =
            StringInterpolationLet.generate(&mut Scope::new(&[], &table), &mut emit, &rule_params);
        assert!(result.is_none());
    }

    #[test]
    fn generates_interpolation_with_var() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringInterpolationLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("let"), "got: {text}");
        assert!(text.contains('{'), "expected interpolation, got: {text}");
    }
}

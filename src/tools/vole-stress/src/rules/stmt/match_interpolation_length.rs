//! Rule: match on interpolated string length.
//!
//! Generates `match "val={x}".length() { 4 => "short", 5 => "medium", _ => "long" }`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchInterpolationLength;

impl StmtRule for MatchInterpolationLength {
    fn name(&self) -> &'static str {
        "match_interpolation_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let vars = collect_primitive_vars(scope);
        if vars.is_empty() {
            return None;
        }

        let var = &vars[emit.gen_range(0..vars.len())];
        let name = scope.fresh_name();
        let prefix = ["val", "x", "result", "out"];
        let pfx = prefix[emit.gen_range(0..prefix.len())];

        let mut used = std::collections::HashSet::new();
        let mut arms = Vec::new();
        for _ in 0..emit.random_in(2, 3) {
            let v = emit.gen_range(1..21) as i64;
            if used.insert(v) {
                let labels = ["\"short\"", "\"medium\"", "\"exact\""];
                let label = labels[arms.len().min(labels.len() - 1)];
                arms.push(format!("{} => {}", v, label));
            }
        }
        arms.push("_ => \"other\"".to_string());

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match \"{}={{{}}}\".length() {{ {} }}",
            name,
            pfx,
            var,
            arms.join(", ")
        ))
    }
}

fn collect_primitive_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(
            ty,
            TypeInfo::Primitive(
                PrimitiveType::I64
                    | PrimitiveType::I32
                    | PrimitiveType::String
                    | PrimitiveType::Bool
            )
        ) {
            out.push(name.clone());
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
        assert_eq!(
            MatchInterpolationLength.name(),
            "match_interpolation_length"
        );
    }

    #[test]
    fn generates_match() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchInterpolationLength.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("match"), "got: {text}");
        assert!(text.contains(".length()"), "got: {text}");
    }
}

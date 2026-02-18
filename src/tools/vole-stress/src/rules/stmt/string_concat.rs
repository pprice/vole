//! Rule: string concatenation let-binding.
//!
//! Finds string variables in scope and generates a concatenation:
//! ```vole
//! let result = s1 + " " + s2
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct StringConcat;

impl StmtRule for StringConcat {
    fn name(&self) -> &'static str {
        "string_concat"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        let name = scope.fresh_name();
        let num_parts = emit.random_in(2, 3);
        let mut parts: Vec<String> = Vec::new();

        for _ in 0..num_parts {
            if emit.gen_bool(0.6) {
                let idx = emit.gen_range(0..string_vars.len());
                parts.push(string_vars[idx].clone());
            } else {
                let lit = match emit.gen_range(0..4) {
                    0 => "\" \"".to_string(),
                    1 => "\",\"".to_string(),
                    2 => "\"-\"".to_string(),
                    _ => "\"_\"".to_string(),
                };
                parts.push(lit);
            }
        }

        let expr = parts.join(" + ");
        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, expr))
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
        assert_eq!(StringConcat.name(), "string_concat");
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
            StringConcat
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_concat() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "s1".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        scope.add_local(
            "s2".into(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = StringConcat.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("+"), "got: {text}");
    }
}

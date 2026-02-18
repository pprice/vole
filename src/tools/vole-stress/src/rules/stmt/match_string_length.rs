//! Rule: match on string length.
//!
//! Finds a string variable in scope and generates a match on `.length()`:
//! ```vole
//! let result = match str.length() {
//!     0 => "empty"
//!     1 => "one"
//!     _ => "medium"
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchStringLength;

impl StmtRule for MatchStringLength {
    fn name(&self) -> &'static str {
        "match_string_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let string_vars = collect_string_vars(scope);
        if string_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..string_vars.len());
        let var = &string_vars[idx];
        let name = scope.fresh_name();

        let result_strs = [
            "\"empty\"",
            "\"one\"",
            "\"short\"",
            "\"medium\"",
            "\"long\"",
        ];
        let num_arms = emit.random_in(2, 3);

        let mut arms = Vec::new();
        for i in 0..num_arms {
            let val = i as i64;
            arms.push(format!(
                "    {} => {}",
                val,
                result_strs[i % result_strs.len()]
            ));
        }
        let default = result_strs[num_arms % result_strs.len()];
        arms.push(format!("    _ => {}", default));

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.length() {{\n{}\n}}",
            name,
            var,
            arms.join("\n")
        ))
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
        assert_eq!(MatchStringLength.name(), "match_string_length");
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
            MatchStringLength
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_string_variable() {
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

        let result = MatchStringLength.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("s.length()"), "got: {text}");
        assert!(text.contains("_ =>"), "got: {text}");
    }
}

//! Rule: match on array length.
//!
//! Picks a parameter array and generates a match on `.length()`:
//! ```vole
//! let result = match arr.length() {
//!     0 => "empty"
//!     1 => "one"
//!     2 => "two"
//!     _ => "many"
//! }
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct MatchArrayLength;

impl StmtRule for MatchArrayLength {
    fn name(&self) -> &'static str {
        "match_array_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let array_params: Vec<String> = scope
            .params
            .iter()
            .filter(|p| matches!(p.param_type, TypeInfo::Array(_)))
            .map(|p| p.name.clone())
            .collect();

        if array_params.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..array_params.len());
        let arr = &array_params[idx];
        let name = scope.fresh_name();

        let labels = ["\"empty\"", "\"one\"", "\"two\"", "\"few\"", "\"many\""];

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!(
            "let {} = match {}.length() {{\n    0 => {}\n    1 => {}\n    2 => {}\n    _ => {}\n}}",
            name, arr, labels[0], labels[1], labels[2], labels[4]
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
        assert_eq!(MatchArrayLength.name(), "match_array_length");
    }

    #[test]
    fn returns_none_without_array_params() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            MatchArrayLength
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_with_array_param() {
        let table = SymbolTable::new();
        let fn_params = [ParamInfo {
            name: "items".into(),
            param_type: TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
        }];
        let mut scope = Scope::new(&fn_params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = MatchArrayLength.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("items.length()"), "got: {text}");
        assert!(text.contains("\"empty\""), "got: {text}");
        assert!(text.contains("\"many\""), "got: {text}");
    }
}

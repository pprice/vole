//! Rule: .to_string().length() chained method.
//!
//! Generates `x.to_string().length()` on numeric variables,
//! testing method chaining on temporary string values.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct TostringLength;

impl StmtRule for TostringLength {
    fn name(&self) -> &'static str {
        "tostring_length"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars: Vec<String> = scope
            .locals
            .iter()
            .filter(|(_, ty, _)| matches!(ty, TypeInfo::Primitive(PrimitiveType::I64)))
            .map(|(name, _, _)| name.clone())
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let name = scope.fresh_name();

        scope.add_local(name.clone(), TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(format!("let {} = {}.to_string().length()", name, var))
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
        assert_eq!(TostringLength.name(), "tostring_length");
    }

    #[test]
    fn returns_none_without_i64_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            TostringLength
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_chain() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = TostringLength.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".to_string().length()"), "got: {text}");
    }
}

//! Rule: numeric .to_string() let-binding.
//!
//! Finds a numeric variable and generates a `.to_string()` expression,
//! optionally with a prefix or suffix:
//! ```vole
//! let s = num.to_string()
//! let s = "n=" + num.to_string()
//! let s = num.to_string() + "!"
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct ToStringLet;

impl StmtRule for ToStringLet {
    fn name(&self) -> &'static str {
        "to_string_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let numeric_vars = collect_numeric_vars(scope);
        if numeric_vars.is_empty() {
            return None;
        }

        let idx = emit.gen_range(0..numeric_vars.len());
        let var_name = &numeric_vars[idx];
        let name = scope.fresh_name();

        let expr = match emit.gen_range(0..3) {
            0 => format!("{}.to_string()", var_name),
            1 => {
                let prefix = match emit.gen_range(0..3) {
                    0 => "\"n=\"",
                    1 => "\"val:\"",
                    _ => "\"x=\"",
                };
                format!("{} + {}.to_string()", prefix, var_name)
            }
            _ => format!("{}.to_string() + \"!\"", var_name),
        };

        scope.add_local(
            name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            false,
        );
        Some(format!("let {} = {}", name, expr))
    }
}

fn collect_numeric_vars(scope: &Scope) -> Vec<String> {
    let mut out = Vec::new();
    for (name, ty, _) in &scope.locals {
        if matches!(
            ty,
            TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64)
        ) {
            out.push(name.clone());
        }
    }
    for param in scope.params {
        if matches!(
            param.param_type,
            TypeInfo::Primitive(PrimitiveType::I64 | PrimitiveType::I32 | PrimitiveType::F64)
        ) {
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
        assert_eq!(ToStringLet.name(), "to_string_let");
    }

    #[test]
    fn returns_none_without_numeric_vars() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        assert!(
            ToStringLet
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_to_string() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("n".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = ToStringLet.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("to_string()"), "got: {text}");
    }
}

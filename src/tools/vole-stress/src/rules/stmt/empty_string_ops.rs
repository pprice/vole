//! Rule: empty string operations.
//!
//! Generates method calls on `""`: `.length()`, `.to_upper()`, `.trim()`,
//! `.split(",").count()`, `.contains("")`, `.starts_with("")`.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct EmptyStringOps;

impl StmtRule for EmptyStringOps {
    fn name(&self) -> &'static str {
        "empty_string_ops"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let name = scope.fresh_name();

        let (expr, ty) = match emit.gen_range(0..6) {
            0 => (
                "\"\".length()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            1 => (
                "\"\".to_upper()".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
            2 => (
                "\"\".trim()".to_string(),
                TypeInfo::Primitive(PrimitiveType::String),
            ),
            3 => (
                "\"\".split(\",\").count()".to_string(),
                TypeInfo::Primitive(PrimitiveType::I64),
            ),
            4 => (
                "\"\".contains(\"\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
            _ => (
                "\"\".starts_with(\"\")".to_string(),
                TypeInfo::Primitive(PrimitiveType::Bool),
            ),
        };

        scope.add_local(name.clone(), ty, false);
        Some(format!("let {} = {}", name, expr))
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
        assert_eq!(EmptyStringOps.name(), "empty_string_ops");
    }

    #[test]
    fn generates_empty_string_op() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = EmptyStringOps.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("\"\""), "got: {text}");
    }
}

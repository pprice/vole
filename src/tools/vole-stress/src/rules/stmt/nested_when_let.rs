//! Rule: nested when-in-when expression.
//!
//! Generates a nested when expression with an outer condition guarding
//! an inner when, each with literal branch values.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct NestedWhenLet;

impl StmtRule for NestedWhenLet {
    fn name(&self) -> &'static str {
        "nested_when_let"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let result_type = emit.random_primitive_type();
        let result_name = scope.fresh_name();

        let outer_cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));
        let inner_cond = emit.literal(&TypeInfo::Primitive(PrimitiveType::Bool));

        let val1 = emit.literal(&result_type);
        let val2 = emit.literal(&result_type);
        let val3 = emit.literal(&result_type);

        let indent = emit.indent_str();
        let inner_indent = format!("{}    ", indent);
        let deep_indent = format!("{}        ", indent);

        scope.add_local(result_name.clone(), result_type, false);

        Some(format!(
            "let {} = when {{\n\
             {}{} => when {{\n\
             {}{} => {}\n\
             {}_ => {}\n\
             {}}}\n\
             {}_ => {}\n\
             {}}}",
            result_name,
            inner_indent,
            outer_cond,
            deep_indent,
            inner_cond,
            val1,
            deep_indent,
            val2,
            inner_indent,
            inner_indent,
            val3,
            indent,
        ))
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
        assert_eq!(NestedWhenLet.name(), "nested_when_let");
    }

    #[test]
    fn generates_nested_when() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = NestedWhenLet.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when {"), "got: {text}");
        // Should have nested when
        assert!(
            text.matches("when {").count() >= 2,
            "expected nested when, got: {text}"
        );
    }
}

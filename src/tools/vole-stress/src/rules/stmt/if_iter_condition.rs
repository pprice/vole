//! Rule: if statements with iterator aggregate conditions.
//!
//! Generates `if arr.iter().count() > 0 { ... }` and similar patterns where
//! the condition involves an iterator terminal (.count(), .sum(), .any(), .all())
//! applied to an array variable. Stresses iterator dispatch inside conditionals.
//!
//! Uses `if`/`else` as a statement (not expression) since Vole's `if` is not
//! an expression. The result variable is declared with `let mut` and assigned
//! in both branches.

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct IfIterCondition;

impl StmtRule for IfIterCondition {
    fn name(&self) -> &'static str {
        "if_iter_condition"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.02)]
    }

    fn precondition(&self, scope: &Scope, _params: &Params) -> bool {
        scope.can_recurse()
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_arrays: Vec<String> = scope
            .array_vars()
            .into_iter()
            .filter_map(|(name, elem_ty)| {
                if matches!(elem_ty, TypeInfo::Primitive(PrimitiveType::I64)) {
                    Some(name)
                } else {
                    None
                }
            })
            .collect();

        if i64_arrays.is_empty() {
            return None;
        }

        let arr = i64_arrays[emit.gen_range(0..i64_arrays.len())].clone();
        let indent = emit.indent_str();
        let result_name = scope.fresh_name();

        let variant = emit.gen_range(0..4);
        let (condition, then_val, else_val) = match variant {
            0 => (
                format!("{arr}.iter().count() > 0"),
                "\"non-empty\"",
                "\"empty\"",
            ),
            1 => (
                format!("{arr}.iter().sum() > 0"),
                "\"positive\"",
                "\"non-positive\"",
            ),
            2 => (
                format!("{arr}.iter().any((x) => x > 5)"),
                "\"has big\"",
                "\"all small\"",
            ),
            _ => (
                format!("{arr}.iter().all((x) => x >= 0)"),
                "\"all non-neg\"",
                "\"has neg\"",
            ),
        };

        scope.add_local(
            result_name.clone(),
            TypeInfo::Primitive(PrimitiveType::String),
            true,
        );

        Some(format!(
            "var {result_name} = {else_val}\n\
             {indent}if {condition} {{\n\
             {indent}    {result_name} = {then_val}\n\
             {indent}}}"
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
        assert_eq!(IfIterCondition.name(), "if_iter_condition");
    }

    #[test]
    fn no_generation_without_array() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);
        assert!(
            IfIterCondition
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_if_with_iter() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local(
            "nums".to_string(),
            TypeInfo::Array(Box::new(TypeInfo::Primitive(PrimitiveType::I64))),
            false,
        );
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = IfIterCondition.generate(&mut scope, &mut emit, &params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains(".iter()."), "got: {text}");
        assert!(text.contains("if "), "got: {text}");
        assert!(text.contains("var "), "got: {text}");
    }
}

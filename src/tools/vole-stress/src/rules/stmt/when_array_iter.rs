//! Rule: when-expression returning array literals with iterator operations.
//!
//! Generates patterns where a `when` expression returns different array
//! literals from different arms, then an iterator operation is performed
//! on the result.  This exercises the interaction between branch RC
//! management and iterator dispatch.
//!
//! ```vole
//! let local5 = when {
//!     x > 5 => [10, 20, 30]
//!     _ => [1, 2, 3]
//! }.iter().reduce(0, (acc, x) => acc + x)
//! ```

use crate::emit::Emit;
use crate::rule::{Param, Params, StmtRule};
use crate::scope::Scope;
use crate::symbols::{PrimitiveType, TypeInfo};

pub struct WhenArrayIter;

impl StmtRule for WhenArrayIter {
    fn name(&self) -> &'static str {
        "when_array_iter"
    }

    fn params(&self) -> Vec<Param> {
        vec![Param::prob("probability", 0.03)]
    }

    fn generate(&self, scope: &mut Scope, emit: &mut Emit, _params: &Params) -> Option<String> {
        let i64_vars: Vec<String> = scope
            .vars_matching(|v| matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::I64)))
            .into_iter()
            .map(|v| v.name)
            .chain(
                scope
                    .params
                    .iter()
                    .filter(|p| matches!(p.param_type, TypeInfo::Primitive(PrimitiveType::I64)))
                    .map(|p| p.name.clone()),
            )
            .collect();

        if i64_vars.is_empty() {
            return None;
        }

        let cond_var = &i64_vars[emit.gen_range(0..i64_vars.len())];
        let cond_threshold = emit.gen_i64_range(-10, 20);
        let result_name = scope.fresh_name();

        let arm1 = gen_array_literal(emit);
        let arm2 = gen_array_literal(emit);

        let indent = emit.indented(|e| e.indent_str());
        let close_indent = emit.indent_str();

        let when_block = format!(
            "when {{\n{}{} > {} => {}\n{}_ => {}\n{}}}",
            indent, cond_var, cond_threshold, arm1, indent, arm2, close_indent
        );

        let variant = emit.gen_range(0..3);
        let code = match variant {
            0 => {
                // reduce variant
                let init = emit.gen_i64_range(0, 10);
                format!(
                    "let {} = {}.iter().reduce({}, (acc, x) => acc + x)",
                    result_name, when_block, init
                )
            }
            1 => {
                // filter + count variant
                let filter_threshold = emit.gen_i64_range(0, 20);
                format!(
                    "let {} = {}.iter().filter((x) => x > {}).count()",
                    result_name, when_block, filter_threshold
                )
            }
            _ => {
                // length variant
                format!("let {} = {}.length()", result_name, when_block)
            }
        };

        scope.add_local(result_name, TypeInfo::Primitive(PrimitiveType::I64), false);
        Some(code)
    }
}

/// Generate an array literal with 2-3 i64 elements.
fn gen_array_literal(emit: &mut Emit) -> String {
    let len = emit.gen_range(2..4); // 2 or 3 elements
    let elems: Vec<String> = (0..len)
        .map(|_| emit.gen_i64_range(-50, 100).to_string())
        .collect();
    format!("[{}]", elems.join(", "))
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
        assert_eq!(WhenArrayIter.name(), "when_array_iter");
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
            WhenArrayIter
                .generate(&mut scope, &mut emit, &params)
                .is_none()
        );
    }

    #[test]
    fn generates_when_with_iter_from_local() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("x".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenArrayIter.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(text.contains("["), "expected array literal, got: {text}");
    }

    #[test]
    fn generates_when_with_iter_from_param() {
        let table = SymbolTable::new();
        let params = &[ParamInfo {
            name: "n".to_string(),
            param_type: TypeInfo::Primitive(PrimitiveType::I64),
            has_default: false,
        }];
        let mut scope = Scope::new(params, &table);

        let mut rng = rand::rngs::StdRng::seed_from_u64(99);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenArrayIter.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        let text = result.unwrap();
        assert!(text.contains("when"), "got: {text}");
        assert!(
            text.contains("n >"),
            "expected condition on param, got: {text}"
        );
    }

    #[test]
    fn result_is_i64() {
        let table = SymbolTable::new();
        let mut scope = Scope::new(&[], &table);
        scope.add_local("y".into(), TypeInfo::Primitive(PrimitiveType::I64), false);

        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        let resolved = ResolvedParams::new();
        let mut emit = test_emit(&mut rng, &resolved);
        let rule_params = Params::from_iter([("probability", ParamValue::Probability(1.0))]);

        let result = WhenArrayIter.generate(&mut scope, &mut emit, &rule_params);
        assert!(result.is_some());
        // Verify the local was added with I64 type
        let locals: Vec<_> = scope
            .vars_matching(|v| {
                v.name.starts_with("local")
                    && matches!(v.type_info, TypeInfo::Primitive(PrimitiveType::I64))
            })
            .into_iter()
            .collect();
        // Should have added at least one new local (the result)
        assert!(
            locals.len() >= 1,
            "expected at least one new i64 local, got {}",
            locals.len()
        );
    }
}
